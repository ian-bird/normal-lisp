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

(define (last seq) (car (last-pair seq)))

;; creates a lookup function to get the variable mentioned.
;; the lookup uses no counters and should be as fast as a car/cdr chain.
;; if the variable is not found, it returns a function that performs
;; a dynamic lookup for the variable.
(define (get-assoc env var)
  (if (any? (partial assoc var) env)
      (if (assoc var (car env))
          (let ((rest (let loop ((a-list (car env)))
			(if (eq? (caar a-list) var)
			    (lambda (al) (car al))
			    (let ((rest (loop (cdr a-list))))
			      (lambda (al) (rest (cdr al))))))))	    
            (lambda (env) (rest (car env))))
          (let ((rest (get-assoc (cdr env) var)))
            (lambda (env) (rest (cdr env)))))
      (begin (add-global-binding! env var)
	     (get-assoc env var))))

;; add an unbound definition to the global environment
;; since define can only run in the global level,
;; anything not in the lexical scope at compile time must be present here.
(define (add-global-binding! env var)
  (if (null? (car (last-pair env)))
      (set-car! (last-pair env) (list (list var)))
      (set-cdr! (last-pair (car (last-pair env))) (list (list var)))))

(define (map-args params args)
  (cond ((and (null? params) (null? args)) '())
	((symbol? params) (acons params args '()))
	(else (acons (car params) (car args) (map-args (cdr params) (cdr args))))))

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
                 (k (if (and p (not (null? (cdr p)))) (cdr p) (eval s (current-module))))))))
          ((any? (lambda (proc) (proc s)) (list boolean? string? number?) )
           ;; self-evaluating. pass value to k directly.
           (lambda (_ k) (k s)))
          ((list? s)
           (case (car s)
                 ((quote) (check-arity 1)
                  (let ((v (cadr s)))
                    ;; pass 2nd value to k directly.
                    (lambda (_ k) (k v))))
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
                                       (cons (map-args (cadr s) arg-vals) env)))
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
                                                      (lambda (env k) ((car statements) env (lambda (_) (r env k)))))))))
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
		  (when (> (length example-env) 1)
		    (error "use of define within non-global lexical scope"))
                  (let ((rval (compile-statement (caddr s) example-env)))
                    ;; eval argument, store it in env, then call k with null
                    (lambda (env k)
                      (rval env (lambda (r)
				  (let ((binding (assoc (cadr s) (last env))))
				    (if binding
					(if (null? (cdr binding))
					    (set-cdr! binding r)
					    (error (string-append (symbol->string (cadr s))
								  " is already defined!")))
					(begin (add-global-binding! env (cadr s))
					       (set-cdr! (assoc (cadr s) (car env)) r))))
                                  (k '()))))))
                 ((set!) (check-arity 2)
                  (let ((find-pair (get-assoc example-env (cadr s)))
                        (rval (compile-statement (caddr s) example-env)))
                    ;; eval argument, store it in the appropriate cell in env, then call k with null
                    (lambda (env k)
                      (rval env (lambda (r)
                                  (set-cdr! (find-pair env) r)
                                  (k '()))))))
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
