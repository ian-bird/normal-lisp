;; env is a list of a-lists
(define (easy-eval statement env)
  (eval. statement env (lambda (result _) result)))

(define (eval. statement env k)
  (let ((check-arity (lambda (n)
                       (unless (= (count statement) (1+ n))
                         (error (string-append
                                 "arity mismatch: expected " 
                                 (number->string n)
                                 " found "
                                 (number->string (1- (count statement)))))))))
    (cond 
     ;; lookup other symbols in the environment
     ((symbol? statement)
      (k (lookup statement env) env))
     ;; these are self-evaluating
     ((any? (lambda (f) (f statement)) 
            (list number? string? boolean?))
      (k statement env))
     
     ;; if a list comes in, we need to see if the car is a special form
     ;; (i.e., a symbol with special evaluation rules)
     ((list? statement)
      (case (car statement)
            ;; quote doesnt eval its argument
            ((quote) (check-arity 1)
             (k (cadr statement) env))
            ;; if conditionally evals its args
            ((if) (check-arity 3)
             (eval. (cadr statement) env (lambda (pred env)
                                           (if pred
                                               (eval. (nth statement 2) env k)
                                               (eval. (nth statement 3) env k)))))
            ;; lambda has a special syntax and produces
            ;; a procedure that can be applied
            ((lambda)
             (k (list (cons 'body (cddr statement))
                      (cons 'arg-names (cadr statement))
                      (cons 'env env)) env))
            ;; define creates a new binding in the current environment
            ((define) (check-arity 2)
             (eval. (nth statement 2) env (lambda (rval env)
                                            (k '() (let ((p (assoc (cadr statement) (car env))))
                                                     (if p
                                                         (set-cdr! p rval)
                                                         (if (null? (car env))
                                                                    (set-car! env (acons (cadr statement)
                                                                                         rval
                                                                                         (car env)))
                                                             (set-cdr! (last-cons (car env))
                                                                       (acons (cadr statement) rval '()))))
                                                     env)))))
            ;; set! finds the nearest binding of an existing var and replaces its value
            ((set!) (check-arity 2)
             (eval. (nth statement 2) env (lambda (rval env)
                                            (k '() (update-val (cadr statement) rval env)))))
            
            ;; manual implementation of built-in functions
            ((car) (check-arity 1)
             (eval. (cadr statement) env (lambda (val env)
                                           (k (car val) env))))
            ((cdr) (check-arity 1)
             (eval. (cadr statement) env (lambda (val env)
                                           (k (cdr val) env))))
            ((cons) (check-arity 2)
             (eval. (cadr statement) env (lambda (head env)
                                           (eval. (nth statement 2) env (lambda (tail env)
                                                                          (k (cons head tail) env))))))
            ;; if none of the above, eval the car, then eval all the args, and apply the fn.
            (else 
             (eval. (car statement) env (lambda (proc env)
                                           (eval-many (cdr statement) env (lambda (args env)
                                                                             (k (apply. proc args) env)))))))))))

;; evals a list of statements and returns the list of their results, and the final resulting env.
;; passes values to the continuation provided.
(define (eval-many statements base-env k)
  (if (null? statements)
      (k '() base-env)
      (eval. (car statements) base-env (lambda (arg env)
                                    (eval-many (cdr statements) env (lambda (rest-args env)
                                                                      (k (cons arg rest-args) env)))))))

;; looks up a variable in an environment.
(define (lookup var env)
  (let ((result (reduce (lambda (acc frame)
                          (if (null? acc)
                              (let ((p (assoc var frame)))
                                (if p (cdr p) '()))
                              acc))
                        '()
                        env)))
    (if (null? result)
        (eval var)
        result)))

;; updates a variable's value in an environment.
(define (update-val what to in)
  (reduce (lambda (acc alist)
            (if acc
                acc
                (let ((p (assoc what alist)))
                  (if p
                      (begin (set-cdr! p to)
                             in)
                      #f))))
          #f
          in))

;; applies a function. Since functions are lexically scoped,
;; any changes to the environment caused by evaluating reflect only in
;; the environment stored with the code. 
;;
;; the main thing apply does is load an environment to execute
;; the body of code for a lambda in, then evals with that environment.
(define (apply. fn arg-vals)
  (if (procedure? fn)
      (apply fn arg-vals)
      (let* ((get-val (lambda (k) (cdr (assoc k fn))))
             (body (get-val 'body))
             (env (get-val 'env))
             (arg-names (get-val 'arg-names)))
        (unless (= (count arg-names) (count arg-vals))
          (error (string-append
                  "arity mismatch: expected " 
                  (number->string (count arg-names))
                  " found "
                  (number->string (count arg-vals)))))
        (last (map (lambda (statement) 
                     (eval. statement 
                            (cons (map (partial apply cons)
                                       (zip arg-names arg-vals))
                                  env) 
                            (lambda (result new-env)
                              (set-car! env (cadr new-env))
                              (set-cdr! env (cddr new-env))
                              result)))
                   body)))))

(define (last-cons seq)
  (if (null? (cdr seq))
      seq
      (last-cons (cdr seq))))

(define (acons k v a-list)
  (cons (cons k v) a-list))

;; creates a lookup function to get the variable mentioned.
;; the lookup uses no counters and should be as fast as a car/cdr chain.
;; if the variable is not found, it returns a function that performs
;; a dynamic lookup for the variable.
(define (get-assoc env var)
  (letrec ((1d (lambda (a-list)
                 (if (eq? (caar a-list) var)
                     (lambda (al) (car al))
                     (let ((rest (1d (cdr a-list))))
                           (lambda (al) (rest (cdr al))))))))
    (if (any? (lambda (a-list) (assoc var a-list)) env)
        (if (assoc var (car env))
            (let ((rest (1d (car env))))
              (lambda (env) (rest (car env))))
            (let ((rest (get-assoc (cdr env) var)))
              (lambda (env) (rest (cdr env)))))
        (lambda (env)
          (reduce (lambda (acc e)
                    (if acc acc (assoc var e)))
                  #f
                  env)))))

;; walks the code, combining lambdas into a fn that produces the desired behavior.
;; compiling thus splits syntactical analysis / symbol location from executing the code.
;; compilation yields a 5x speedup over naive interpretation.
(define (compile-statement s example-env)
  (let ((check-arity (lambda (n)
                       (unless (= (count s) (1+ n)) 
                         (error (string-append
                                 "arity mismatch: expected " 
                                 (number->string n)
                                 " found "
                                 (number->string (1- (count statement)))))))))
    (cond ((symbol? s)
           (let ((find-pair (get-assoc example-env s)))
             ;; if found then pass to k, otherwise eval and pass to k.
             (lambda (env k) 
               (let ((p (find-pair env)))
                 (k (if p (cdr p) (eval s)))))))
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
                    (lambda (env)
                      (a1 env (lambda (v1) (k (cdr v1)))))))
                 ((cons) (check-arity 2)
                  (let ((a1 (compile-statement (cadr s) example-env))
                        (a2 (compile-statement (nth s 2) example-env)))
                    ;; evaluate both args, cons them, then pass to k.
                    (lambda (env k)
                      (a1 env (lambda (v1) (a2 env (lambda (v2) (k (cons v1 v2)))))))))
                 ((if) (check-arity 3)
                  (let ((a1 (compile-statement (cadr s) example-env))
                        (a2 (compile-statement (nth s 2) example-env))
                        (a3 (compile-statement (nth s 3) example-env)))
                    ;; evaluate predicate, if valid, eval a2 otherwise eval a3
                    ;; with the continuation as k
                    (lambda (env k)
                      (a1 env (lambda (v1) ((if v1 a2 a3) env k))))))
                 ((lambda) 
                  (let* ((extend-env (lambda (arg-vals)
                                       (cons (map (partial apply cons) (zip (cadr s) arg-vals)) example-env)))
                         (extended-env (extend-env (map (constantly '()) (cadr s))))
                         (compiled-statements (map (lambda (s) (compile-statement s extended-env)) (cddr s))))
                    (letrec ((eval-statements (lambda (statements)
                                                (let ((statement (car statements)))
                                                (if (null? (cdr statements))
                                                    ;; if this is the last statement evaluate it with continuation
                                                    ;; as k.
                                                    (lambda (env k) (statement env k))
                                                    (let ((r (eval-statements (cdr statements))))
                                                      ;; if there's more statements, evaluate this one, discard the
                                                      ;; result and go to the next one.
                                                      (lambda (env k) (statements env (lambda (_) (r env k))))))))))
                      (let ((evaled-statements (eval-statements compiled-statements)))
                        ;; pass lambda to k directly
                        (lambda (_ k) (k (lambda args
                                           (unless (= (count (cadr s)) (count args))
                                             (error "arity mismatch"))
                                           ;; eval each statement and return the last as result.
                                           (evaled-statements (extend-env args) identity))))))))
                 ((define) (check-arity 2)
                  (let ((rval (compile-statement (nth s 2) example-env)))
                    ;; eval argument, store it in env, then call k with null
                    (lambda (env k)
                      (rval env (lambda (r)
                                  (if (null? (car env))
                                      (set-car! env (cons (cons (cadr s) r) '()))
                                      (set-cdr! (last-cons (car env)) (cons (cons (cadr s) r) '())))
                                  (k '()))))))
                 ((set!) (check-arity 2)
                  (let ((find-pair (get-assoc example-env (cadr s)))
                        (rval (compile-statement (nth s 2) example-env)))
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
