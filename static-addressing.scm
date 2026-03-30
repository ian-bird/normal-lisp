(define (some proc seq)
  (cond ((null? seq) #f)
	((proc (car seq)) (car seq))
	(else (some proc (cdr seq)))))

(define (any? proc seq)
  (if (some proc seq)
      #t
      #f))

(define (constantly c) (lambda (_) c))

(define (partial fn . args) (lambda rest-args (apply fn (append args rest-args))))

(define (compose first-fn . rest-fns)
  (if (null? rest-fns)
      first-fn
      (let ((rest-fn (apply compose rest-fns)))
	(lambda args
	  (first-fn (apply rest-fn args))))))

(define (from-right fn) (compose (lambda (x) (if (list? x) (reverse x) x)) fn reverse))

(define last (from-right car))

(define butlast (from-right cdr))

;; creates a lookup function to get the variable mentioned.
;; the lookup uses no counters and should be as fast as a car/cdr chain.
;; if the variable is not found, it returns a function that performs
;; a dynamic lookup for the variable.
(define (get-assoc env var)
  (let ((lexical-envs (car env))
	(get-vec-num (lambda (vec k)
		       (let loop ((n 0))
			 (cond ((>= n (vector-length vec)) #f)
			       ((eq? (car (vector-ref vec n)) k) n )
			       (else (loop (1+ n))))))))
    (let ((lexical-accessor (let loop ((frame-num 0))
			      (if (>= frame-num (vector-length lexical-envs))
				  #f
				  (let ((binding-num (get-vec-num (vector-ref lexical-envs
									      frame-num)
								  var)))
				    (if binding-num
					(lambda (env) (vector-ref (vector-ref (car env)
									      frame-num)
								  binding-num))
					(loop (1+ frame-num))))))))
      (if lexical-accessor
	  lexical-accessor
	  (let ((binding (assoc var (cadr env))))
	    (unless binding
              (add-global-binding! env var)
	      (set! binding (assoc var (cadr env))))
	    (lambda (_env)
              binding))))))

(define (run-code . statements)
  (let ((env (list #() '()))
        (result '()))
    (for-each (lambda (statement)
		(set! result ((comp statement env) env identity)))
	      statements)
    result))

;; add an unbound definition to the global environment
;; since define can only run in the global level,
;; anything not in the lexical scope at compile time must be present here.
(define (add-global-binding! env var)
  (if (null? (cadr env))
      (begin (raise-exception var #:continuable? #t)
	     (set-car! (cdr env) (list (list var))))
      (set-cdr! (last-pair (cadr env)) (list (list var)))))

(define (map-args params args)
  (let ((v (make-vector (let loop ((params params)
				   (c 0))
                          (cond ((null? params) c)
				((symbol? params) (1+ c))
				(else (loop (cdr params) (1+ c))))))))
    (do ((params params (if (symbol? params) params (cdr params)))
	 (args args (cdr args))
	 (i 0 (1+ i)))
	((>= i (vector-length v)) v)
      (vector-set! v i (if (symbol? params)
			   (cons params args)
			   (list (car params) (car args)))))))



(define (vector-cons val vec)
  (let ((result (make-vector (1+ (vector-length vec)))))
    (vector-set! result 0 val)
    (vector-copy! result 1 vec)
    result))

(define (comp s env)
  (lambda (runtime-env k)
    (with-exception-handler
	(lambda (exn)
	  (unless (and (list? exn) (eq? (car exn) 'jump))
	    (raise-exception exn))
	  (cadr exn))
      (lambda ()
	(with-exception-handler
	    (lambda (exn)
	      (unless (symbol? exn)
		(raise-exception exn))
	      (if (with-exception-handler
		      (lambda (exn) #f)
		    (lambda () (eval exn (current-module)) #t)
		    #:unwind? #t)
		  (format #t "warning: using host environment variable ~a\n" exn)
		  (format #t "warning: potentially unbound variable ~a\n" exn)))
	  (lambda ()
	    ((compile-statement s env) runtime-env k))))
      #:unwind? #t)))

;; analyzes the code, combining lambdas into a fn that produces the desired behavior.
;; compiling thus splits syntactical analysis / symbol location from executing the code.
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
                 (k (if (and p (not (null? (cdr p)))) (cadr p) (eval s (current-module))))))))
          ((any? (lambda (proc) (proc s)) (list boolean? string? number?) )
           ;; self-evaluating. pass value to k directly.
           (lambda (_env k) (k s)))
          ((list? s)
           (case (car s)
                 ((quote) (check-arity 1)
                  (let ((v (cadr s)))
                    ;; pass 2nd value to k directly.
                    (lambda (_env k) (k v))))
                 ((car) (check-arity 1)
                  (let ((a1 (compile-statement (cadr s) example-env)))
                    ;; evaluate argument, car it, then pass to k.
                    (lambda (env k)
                      (a1 env (lambda (v1) (k (car v1)))))))
                 ((cdr) (check-arity 1)
                  (let ((a1 (compile-statement (cadr s) example-env)))
                    ;; evaluate argument, cdr it, then pass to k.
                    (lambda (env k)
                      (a1 env (lambda (v1) (k (cdr v1)))))))
                 ((cons) (check-arity 2)
                  (let ((a1 (compile-statement (cadr s) example-env))
                        (a2 (compile-statement (caddr s) example-env)))
                    ;; evaluate both args, cons them, then pass to k.
                    (lambda (env k)
                      (a1 env (lambda (v1) (a2 env (lambda (v2) (k (cons v1 v2)))))))))
                 ((if) (check-arity 3)
                  (let ((a1 (compile-statement (cadr s) example-env))
                        (a2 (compile-statement (caddr s) example-env))
                        (a3 (compile-statement (cadddr s) example-env)))
                    ;; evaluate predicate, if valid, eval a2 otherwise eval a3
                    ;; with the continuation as k
                    (lambda (env k)
                      (a1 env (lambda (v1) ((if v1 a2 a3) env k))))))
                 ((lambda)
                  (let* (		; this function builds an
					; application environment
					; using the provided args
			 (extend-env (lambda (env arg-vals)
                                       (cons (vector-cons (map-args (cadr s) arg-vals) (car env))
					     (cdr env))))
			 ;; this is the compile-time environment, with
			 ;; all variables unbound. This is primarily
			 ;; used to build the accessor functions at compile-time.
                         (extended-env (extend-env example-env (make-list (length (cadr s)) '())))
			 ;; compile all the statements in the body of
			 ;; the lambda.
                         (compiled-statements (map (lambda (s) (compile-statement s extended-env)) (cddr s)))
			 ;; link them together into a single
			 ;; executable function that returns the value
			 ;; of the last s-exp.
			 (evaled-statements (let loop ((statements compiled-statements))
						(if (null? (cdr statements))
                                                    ;; if this is the last statement evaluate it with continuation
                                                    ;; as k.
                                                    (lambda (env k) ((car statements) env k))
                                                    (let ((r (loop (cdr statements))))
                                                      ;; if there's more statements, evaluate this one, discard the
                                                      ;; result and go to the next one.
                                                      (lambda (env k) ((car statements) env (lambda (_args) (r env k)))))))))
                    ;; pass lambda to k directly
                    (lambda (creation-env k)
		      (k (lambda args
                           (unless (= (length (cadr s)) (length args))
                             (error "arity mismatch"))
                           ;; eval each statement and return the last
			   ;; as result, and eval them under the
			   ;; environment that existed when the lambda
			   ;; was created, not when it was compiled,
			   ;; or when it was ran.
                           (evaled-statements (extend-env creation-env args) identity))))))
                 ((define) (check-arity 2)
		  (when (positive? (vector-length (car example-env)))
		    (error "use of define within non-global scope"))
                  (let ((rval (compile-statement (caddr s) example-env)))
                    ;; eval argument, store it in env, then call k with null
                    (lambda (env k)
                      (rval env (lambda (r)
				  (with-exception-handler
				      (lambda (exn)
					(unless (symbol? exn)
					  (raise-exception exn))
					(unless (eq? exn (cadr s))
					  (raise-exception exn #:continuable? #t)))
				    (lambda ()
                                      (let ((binding (assoc (cadr s) (cadr env))))
					(if binding
					    (if (null? (cdr binding))
						(set-cdr! binding (list r))
						(error (string-append (symbol->string (cadr s))
								      " is already defined!")))
					    (begin (add-global-binding! env (cadr s))
						   (set-cdr! (assoc (cadr s) (cadr env)) (list r)))))))
                                  (k '()))))))
                 ((set!) (check-arity 2)
                  (let ((find-pair (get-assoc example-env (cadr s)))
                        (rval (compile-statement (caddr s) example-env)))
                    ;; eval argument, store it in the appropriate cell
                    ;; in env, then call k with null
                    (lambda (env k)
                      (rval env (lambda (r)
				  ;; variables must exist for them to
				  ;; be settable. unbound variables
				  ;; dont really exist, so we cant use
				  ;; them either.
				  (if (and (find-pair env) (not (null? (cdr (find-pair env)))))
                                      (set-cdr! (find-pair env) (list r))
				      (error (string-append "cannot set unbound variable "
							    (symbol->string (cadr s)))))
                                  (k '()))))))
		 ((call/cc) (check-arity 1)
		  ;; compile the lambda 2nd argument
		  (let ((fn (compile-statement (cadr s) example-env)))
		    (lambda (env k)
		      (k (fn env	; evaluate the lambda, get the
					; actual thing in f
			     (lambda (f)
			       (f (lambda (v)
				    (raise-exception (list 'jump (k v)))))))))))
                 (else			;fn application
                  (letrec ((fn (compile-statement (car s) example-env))
                           (args (map (lambda (s) (compile-statement s example-env))
                                      (cdr s)))
                           (eval-args (lambda (args)
                                        (if (null? args)
                                            (lambda (env k) (k '()))
                                            (let ((f (car args))
                                                  (r (eval-args (cdr args))))
                                              (lambda (env k) (f env (lambda (f)
                                                                       (r env (lambda (r)
                                                                                (k (cons f r))))))))))))
                    (let ((evaled-args (eval-args args)))
                      ;; eval the function, then eval the args, then apply the fn and pass the result to k
                      (lambda (env k)
                        (fn env (lambda (fn)
                                  (evaled-args env (lambda (args)
                                                     (k (apply fn args)))))))))))))))


