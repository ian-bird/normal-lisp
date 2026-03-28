(use-modules (srfi srfi-9) (ice-9 match))

(define (nth seq n)
  (do ((seq seq (cdr seq))
       (n 0 (1+ n)))
      ((zero? n) (car seq))))

(define (last-cons seq)
  (if (null? (cdr seq))
      seq
      (last-cons (cdr seq))))

(define (last seq)
  (car (last-cons seq)))

(define (some proc seq)
  (let loop ((seq seq))
    (cond ((null? seq) #f)
	  ((proc (car seq)) (car seq))
	  (else (loop (cdr seq))))))

(define compose
  (case-lambda ((fn) fn)		; if its one thing just return it
	       ;; if its multiple, do the rest apply with the args and
	       ;; pass it into the leftmost arg
	       ((ffirst . frest)
		(let ((rest (apply compose frest)))
		  (lambda args
		    (ffirst (apply rest args)))))))

(define (partial fn . args)
  (lambda rest-args
    (apply fn (append args rest-args))))

(define (constantly c) (lambda (_) c))

(define (add-global-binding env var)
  (if (null? (last env))
      (set-car! (last-cons env)
		(list (list var)))
      (set-cdr! (last-cons (last env))
		(list (list var)))))

;; creates a lookup function to get the variable mentioned.  this
;; lookup actually ignores the given function and directly returns the
;; assoc pair, or #f if its not found (or if the cdr is null) at the
;; time of creation, a variable not being found will create a
;; global-level placeholder.
;;
;; this allows for later functions to potentially define it, and
;; delays the error until runtime if it's not defined.
(define (get-assoc env var)
  (let* ((al (some (partial assoc var) env))
	 (binding (if al (assoc var al) #f)))
    (if binding
	(lambda (_)
	  (if (null? (cdr binding))
	      #f
	      binding))
	;; if we cant find the variable we need to create an empty
	;; slot for it in the global scope and return that
	(begin
          (add-global-binding env var)
          (get-assoc env var)))))


(define (map-args params args)
  (let loop ((params params)
	     (args args)
	     (mapping '()))
    (reverse
     (cond ((null? params) mapping)
	   ((symbol? params) (acons params args mapping))
	   (else (loop (cdr params)
		       (cdr args)
		       (acons (car params) (car args) mapping)))))))

(define (any? pred seq)
  (not (eq? #f (some pred seq))))

(define (tap val lambda)
  (lambda val)
  val)


(define (and-print x)
  (tap x (lambda (x) (format #t "and print: ~a\n" x))))


;; walks the code, combining lambdas into a fn that produces the desired behavior.
;; compiling thus splits syntactical analysis / symbol location from executing the code.
;; compilation yields a 5x speedup over naive interpretation.
(define (compile-statement s example-env)
  (let ((check-arity (lambda (n)
		       (unless (= (length s) (1+ n)) 
                         (error (string-append
                                 "arity mismatch: expected " 
                                 (number->string n)
                                 " found "
                                 (number->string (1- (length s)))))))))
    (cond ((symbol? s)
	   (let ((find-pair (get-assoc example-env s)))
             ;; if found then pass to k, otherwise eval and pass to k.
             (lambda (env k)
               (let ((p (find-pair env)))
                 (k (if p (cdr p) (eval s (current-module))))))))
          ((any? (lambda (proc) (proc s)) (list boolean? string? number?) )
           ;; self-evaluating. pass value to k directly.
           (lambda (_ k) (k s)))
          ((list? s)
           (match s
	     (('quote v) (lambda (_ k) (k v)))
	     (('car p1) (check-arity 1)
	      (let ((a1 (compile-statement p1 example-env)))
		(lambda (env k)
		  (a1 env (lambda (v1) (k (car v1)))))))
	     (('cdr p1) (check-arity 1)
	      (let ((a1 (compile-statement p1 example-env)))
		(lambda (env k)
		  (a1 env (lambda (v1) (k (cdr v1)))))))
	     (('cons p1 p2) (check-arity 2)
	      (let ((a1 (compile-statement p1 example-env))
		    (a2 (compile-statement p2 example-env)))
		(lambda (env k)
		  (a1 env (lambda (v1) (a2 env (lambda (v2) (k (cons v1 v2)))))))))
	     (('if p1 p2 p3) (check-arity 3)
	      (let ((a1 (compile-statement p1 example-env))
                    (a2 (compile-statement p2 example-env))
                    (a3 (compile-statement p3 example-env)))
                ;; evaluate predicate, if valid, eval a2 otherwise eval a3
                ;; with the continuation as k
                (lambda (env k)
                  (a1 env (lambda (v1) ((if v1 a2 a3) env k))))))
	     (('lambda params body . rest)
              (let* (			; build the default environmnet with slots
		     (extended-env (cons (map list params) example-env))
		     ;; do the mutation, saving the old state, and
		     ;; return a lambda that restores the context
                     (extend-env! (lambda (args)
				    (let ((prevs (map cdr (car extended-env))))
                                      (for-each (lambda (cell assignment)
						  (set-cdr! cell (cdr assignment)))
						(car extended-env)
						(map-args params args))
                                      (lambda ()
                                        (for-each (lambda (old-val current-binding)
						    (set-cdr! current-binding old-val))
						  prevs
						  (car extended-env))))))
		     ;; compile all the expressions in the lambda
                     (compiled-statements (map (lambda (s) (compile-statement s extended-env))
					       (cons body rest)))
		     ;; and chain them into a single lambda that
		     ;; returns the last value, (effectively a begin
		     ;; block)
		     (evaled-statements (let loop ((statements compiled-statements))
					  (if (null? (cdr statements))
					      ;; if this is the last statement evaluate it with continuation
					      ;; as k.
					      (lambda (env k) ((car statements) env k))
					      ;; force evaluation of the whole list at compile time
					      (let ((r (loop (cdr statements))))
						;; if there's more statements, evaluate this one, discard the
                                                ;; result and go to the next one.
						(lambda (env k)
                                                  ((car statements) env (lambda (_)
								    (r env k)))))))))
                
		;; pass lambda to k directly
		(lambda (_ k) (k (lambda args
                                   (unless (= (length params) (length args))
                                     (error "arity mismatch"))
                                   ;; build the env and then pass it to the begin block
				   (let ((restore-fn (extend-env! args)))
				     ;; make sure that we restore even if an error occurs
				     (dynamic-wind
				       (lambda () '())
				       (lambda ()
					 ;; run the code 
					 (evaled-statements extended-env identity))
				       (lambda ()
					 ;; restore the environment on exit 
					 (restore-fn)))))))))
	     (('define name value) (check-arity 2)
	      (when (> (length example-env) 1)
		(error "define is only valid in the global scope"))
              (let ((rval (compile-statement value example-env)))
                ;; eval argument, store it in env, then call k with null
                (lambda (env k)
                  (rval env (lambda (r)
                              (cond ((assoc name (car example-env))
				     (set-cdr! (assoc name (car example-env)) r))
				    ((null? (car example-env))
                                     (set-car! example-env (list (cons name r))))
				    (else
				     (set-car! example-env (acons name r (car example-env)))))
                              (k '()))))))
	     (('set! name value) (check-arity 2)
              (let ((find-pair (get-assoc example-env name))
                    (rval (compile-statement value example-env)))
                ;; eval argument, store it in the appropriate cell in env, then call k with null
                (lambda (env k)
                  (rval env (lambda (r)
                              (set-cdr! (find-pair env) r)
                              (k '()))))))
	     ((proc . arguments)			;fn application
	      (let* ((fn (compile-statement proc example-env))
                       (args (map (lambda (s) (compile-statement s example-env))
                                  arguments))
		       (evaled-args (let loop ((args args))
				     (if (null? args)
					 (lambda (env k) (k '()))
					 (let ((f (car args))
                                               (r (loop (cdr args))))
                                           (lambda (env k)
					     (f env (lambda (f)
                                                      (r env (lambda (r)
                                                               (k (cons f r))))))))))))
                ;; eval the function, then eval the args, then apply the fn and pass the result to k
                (lambda (env k)
                  (fn env (lambda (fn)
                            (evaled-args env (lambda (args)
                                               (k (apply fn args))))))))))))))
