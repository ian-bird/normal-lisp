(define (some proc seq)
  (cond ((null? seq) #f)
	((proc (car seq)) (car seq))
	(else (some proc (cdr seq)))))

(define (any? proc seq)
  (if (some proc seq)
      #t
      #f))

;; creates a lookup function to get the variable mentioned.
;;
;; this returns a lambda that locates the variable in constant time,
;; by returning either a closure of the compile-time generated global
;; binding or a vector ref to the future location of the value in the
;; lexical environment.
;;
;; in this way, the binding strategy can be described as *deep
;; binding*, which means our memory usage and time complexity at
;; creation time is linear wrt to the number of lexical frames deep we
;; are. Shallow binding would make memory usage and creation time
;; complexity linear wrt the number of referenced variables closed.
(define (get-assoc env var)
  (let ((lexical-envs (car env))
	(get-vec-num (lambda (vec k)
		       (let loop ((n 0))
			 (cond ((>= n (vector-length vec)) #f)
			       ((eq? (car (vector-ref vec n)) k) n )
			       (else (loop (1+ n))))))))
    ;; it's compile time right now. If we can find the binding in the
    ;; lexical scope, we know exactly where it will appear at
    ;; runtime. so we can close those numbers for the frame and
    ;; binding, and return a fn that takes the runtime environment and
    ;; in 2 vector refs returns the correct binding. This guarantees
    ;; O(1) lookup for lexical variables.
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
	  ;; if we didn't find it there, it must be in the global
	  ;; environment. So we'll add an uninitialized slot for it if
	  ;; it isn't there, and (still at compile time) returning the
	  ;; binding as it appears in the global scope. At runtime,
	  ;; anything accessing this effectively has a pointer to the
	  ;; exact value they want.
	  (let ((binding (assoc var (cadr env))))
	    (unless binding
              (add-global-binding! env var)
	      (set! binding (assoc var (cadr env))))
	    (lambda (_env)
              binding))))))

(define (run-code . statements)
  (let ((env (list #() '() '()))
        (result '()))
    (for-each (lambda (statement)
		(set! result ((comp statement env) env identity)))
	      statements)
    result))



;; add an unbound definition to the global environment
;; since define can only run in the global level,
;; anything not in the lexical scope at compile time must be present here.
;; 
;; the exception that is raised should always be caught by a
;; non-unwinding exception handle. It's to be treated as a warning,
;; that code higher up in the dynamic stack has the ability to
;; intercept and modify on its way up to the final logger.
(define (add-global-binding! env var)
  (raise-exception var #:continuable? #t)
  (if (null? (cadr env))
      (set-car! (cdr env) (list (list var)))
      (set-cdr! (last-pair (cadr env)) (list (list var)))))

(define (add-macro-binding! env var)
  (raise-exception var #:continuable? #t)
  (if (null? (caddr env))
      (set-car! (cddr env) (list (list var)))
      (set-cdr! (last-pair (caddr env)) (list (list var)))))

(define (map-args params args)
  (let ((v (make-vector (let loop ((params params)
				   (c 0))
                          (cond ((null? params) c)
				((symbol? params) (1+ c))
				(else (loop (cdr params) (1+ c))))))))
    (do ((params params (if (symbol? params) params (cdr params)))
	 (args args (if (null? args) '() (cdr args)))
	 (i 0 (1+ i)))
	((>= i (vector-length v)) v)
      (vector-set! v i (if (symbol? params)
			   (list params args)
			   (list (car params) (car args)))))))



(define (vector-cons val vec)
  (let ((result (make-vector (1+ (vector-length vec)))))
    (vector-set! result 0 val)
    (vector-copy! result 1 vec)
    result))

;;  this wraps compile-statement in the appropriate error handling
;;  code.Warnings are caught, its determined whether the host has the
;;  capability to handle the unbound, the appropriate warning is
;;  emited and control passes back to the point where the warning was
;;  raised.
;;
;; This also creates the point for non-local exits to be taken after a
;; reified continuation returns a final value, and propogates all
;; other exceptions further up.
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
		  (format #t "warning: using host environment variable '~a'\n" exn)
		  (format #t "warning: potentially unbound variable '~a'\n" exn)))
	  (lambda ()
	    ((compile-statement s env) runtime-env k))))
      #:unwind? #t)))

;; analyzes the code, combining lambdas into a fn that produces the
;; desired behavior.  compiling thus splits syntactical analysis /
;; symbol location from executing the code.
;;
;;
;; note: define is only allowed at the global level. This a critical
;; restriction of the interpreter, and means that all the variables in
;; a lexical scope that exist at compile time are exactly the ones
;; that will exist at runtime. Additional bindings in the lexical
;; scope cannot be added at runtime precisely because of this
;; restriction.
;;
;; That means any missing binding at runtime can *only* exist in the
;; global scope, which allows us to, at compile time, replace that
;; missing symbol with a constant-time accessor to (at this point
;; allocated ) unbound cell that will hold the value, if the user
;; provides it.
(define (compile-statement s example-env)
  (let ((check-arity (lambda (n)
                       (unless (= (length s) (1+ n)) 
                         (error (format #f "arity mismatch: expected ~a, found ~a"
					(number->string n)
					(number->string (1- (length s)))))))))
    (cond ((symbol? s)
           (let ((find-pair (get-assoc example-env s)))
             ;; if found then pass to k, otherwise eval and pass to k.
             (lambda (env k) 
               (let ((p (find-pair env)))
                 (k (if  (null? (cdr p))
			 (begin
                           (when (assoc s (caddr env))
			     (error (format #f "cannot use macro '~a' as variable"
					    (symbol->string s))))
			   (eval s (current-module)))
			 (cadr p)))))))
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
                         (extended-env (extend-env example-env (make-list (let loop ((params (cadr s))
										     (n 0))
									    (cond ((null? params) n)
										  ((symbol? params) (1+ n))
										  (else (loop (cdr params)
											      (1+ n)))))
									  '())))
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
			   (unless (let loop ((params (cadr s))
					      (args args))
				     (cond ((null? params) (null? args))
					   ((symbol? params) #t)
					   ((null? args) #f)
					   (else (loop (cdr params) (cdr args)))))
                             (error "arity mismatch"))
                           ;; eval each statement and return the last
			   ;; as result, and eval them under the
			   ;; environment that existed when the lambda
			   ;; was created, not when it was compiled,
			   ;; or when it was ran.
                           (evaled-statements (extend-env creation-env args) identity))))))
                 ((define) (check-arity 2)
		  ;; thus, define must also differentiate between
		  ;; bound variables (whose redefinition is
		  ;; forbidden), and unbound variables, who exist in
		  ;; the global namespace but *can* be defined,
		  ;; because semantically, inside the language, there
		  ;; cannot be any observable difference between an
		  ;; existant but unbound variable and a non-existant one.
		  ;;
		  (when (positive? (vector-length (car example-env)))
		    (error "use of define within non-global scope"))
		  ;; we can detect an invalid use of a macro at compile time
		  (when (assoc (cadr s) (caddr example-env))
		    (error (format #f "cannot use macro '~a' as variable"
				   (symbol->string (cadr s)))))
                  (let* (		; catch self def looks for
					; exceptions raised for
					; potentially undefined
					; symbols referencing the one
					; were about to create. Any of
					; those we encounter we can supress.
			 (catch-self-def (lambda (maybe-throws)
					   (with-exception-handler
					       (lambda (exn)
						 (unless (symbol? exn)
						   (raise-exception exn))
						 (unless (eq? exn (cadr s))
						   (raise-exception exn #:continuable? #t)))
					     maybe-throws)))
			 (rval (catch-self-def (lambda ()
						 (compile-statement (caddr s) example-env)))))
		    ;; eval argument, store it in env, then call k with null
		    (lambda (env k)
                      (rval env (lambda (r)
				  (let ((binding (assoc (cadr s) (cadr env))))
				    ;;  if the binding exists and has
				    ;;  been bound, error. definition
				    ;;  to an existant value is
				    ;;  invalid.
				    (if binding
					(begin
					  (unless (null? (cdr binding))
					    (error (string-append (symbol->string (cadr s))
								  " is already defined!")))
					  ;; if its just uninitialized then we can define it
					  (set-cdr! binding (list r)))
					(catch-self-def
					 (lambda ()
					   ;;  add the global binding
					   ;;  to the current env
					   ;;  using the current name
					   ;;  and the evaluation
					   ;;  result of the 2nd arg
					   (add-global-binding! env (cadr s))
					   (set-cdr! (assoc (cadr s) (cadr env)) (list r)))))
				    (k '())))))))
		 ((define-macro)
		  (when (positive? (vector-length (car example-env)))
		    (error "use of define within non-global scope"))
                  (let* (		; catch self def looks for
					; exceptions raised for
					; potentially undefined
					; symbols referencing the one
					; were about to create. Any of
					; those we encounter we can supress.
			 (catch-self-def (lambda (maybe-throws)
					   (with-exception-handler
					       (lambda (exn)
						 (unless (symbol? exn)
						   (raise-exception exn))
						 (unless (eq? exn (cadr s))
						   (raise-exception exn #:continuable? #t)))
					     maybe-throws)))
			 (rval (catch-self-def (lambda ()
						 (compile-statement (caddr s) example-env)))))
		    ;; eval argument, store it in env, then call k with null
		    (lambda (env k)
                      (rval env (lambda (r)
				  (let ((binding (assoc (cadr s) (caddr env))))
                                    ;; unlike variables, macros can be
                                    ;; redefined, since set! does not work for them.
				    (if binding
                                        (set-cdr! binding (list r))
					(catch-self-def
					 (lambda ()
					   ;;  add the macro binding
					   ;;  to the current env
					   ;;  using the current name
					   ;;  and the evaluation
					   ;;  result of the 2nd arg
					   (add-macro-binding! env (cadr s))
                                           (set-cdr! (assoc (cadr s) (caddr env)) (list r)))))
				    (k '())))))))
                 ((set!) (check-arity 2)
		  (when (assoc (cadr s) (caddr example-env))
		    (error (format #f "cannot use macro '~a' as variable"
				   (symbol->string (cadr s)))))
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
			       ;; pass a continuation into f. This
			       ;; works because the current
			       ;; continuation is already fully
			       ;; reified due to the design of the
			       ;; interpreter. However, if this
			       ;; function is ever called, we need to
			       ;; take the result and return it
			       ;; immediately, no matter where we
			       ;; are. The other optional path of flow
			       ;; continuing as normal is aborted, and
			       ;; since we have the result already
			       ;; from the alternate path to k, we
			       ;; just need to jump out of the
			       ;; computation entirely and return
			       ;; that.
			       (f (lambda (v)
				    (raise-exception (list 'jump (k v)))))))))))
		 ((eval) (check-arity 1)
		  ;;  eval can only run in the global scope. This is a
		  ;;  concious design choice, since without local
		  ;;  defines could cause the lexical environment to
		  ;;  change at runtime, which would make it
		  ;;  impossible to determine the location of all
		  ;;  variables at compile-time.
		  (let ((code (compile-statement (cadr s) example-env)))
		    (lambda (env k)
		      ((compile-statement (code env identity) (cons #() (cdr env)))
		       (cons #() (cdr env))
		       k))))
                 (else			;fn or macro application
		  (if (or (and (symbol? (car s))
			       (or (assoc (car s) (cadr example-env))
				   (not (assoc (car s) (caddr example-env)))))
			  (list? (car s)))
		      ;; if we find the binding already defined in the
		      ;; global environment at compile-time or cannot
		      ;; find it in the macro environment,
		      ;;
		      ;; then compile it as a function like normal.
		      ;;
		      ;; otherwise expand the macro and resume
		      ;; compilation.
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
		       ;; eval the function, then eval the
		       ;; args, then apply the fn and pass
		       ;; the result to k
		       (lambda (env k)
			 (fn env (lambda (fn)
				   (evaled-args env (lambda (args)
						      (k (apply fn args)))))))))
		   (let* ((macro (cadr (assoc (car s) (caddr example-env))))
			  (args (cdr s))
			  (expansion (apply macro args)))
		     (compile-statement expansion example-env)))))))))
