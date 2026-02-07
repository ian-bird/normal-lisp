(define (last-cons seq)
  (if (null? (cdr seq))
      seq
      (last-cons (cdr seq))))

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
