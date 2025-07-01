;;; eval. performs normal order evaluation of lisp 1.5 forms, with
;;; define being used in place of label. this allows for lazy
;;; evaluation throughout lisp, and permits the user to write
;;; functions that return infinite lists, which the program can handle
;;; so long as something takes a finite number of elements before a
;;; value is ultimately returned.
;;;
;;; It additionally allows for data with invalid elements or infinite
;;; loops, and as long as there's a way to calculate the final result
;;; without having to evaluate the faulty data.
;;;
;;; Normal evaluation also allows the user to write code that uses
;;; conditional evaluation without having to resort to macros. Or,
;;; and, xor can all be implemented as simple functions.
;;;
;;; Due to the nature of normal evaluation, there is currently no
;;; support for state. Any function that returns no value and is
;;; useful only due to its side effect is impossible to model, since
;;; the evaluator would detect its return value is never used and
;;; simply not evaluate the code.


;; evals a list. This is a top level wrapper for normal-eval-impl
;; since it performs some additional logic at the end.
(define (eval. exp)
  (let ((r (normal-eval-impl exp)))
    (if (list? r)
        (force-all r)
        r)))

;; implements normal evaluation. Evaluates all primitive special forms
;; and primitive functions.
(define (normal-eval-impl exp)
  (cond (;; numbers, bools and strings are self-evaluating
	 (any? (lambda (f) (f exp)) (list number? boolean? string?))
         exp)

	;; symbols get looked up
        ((symbol? exp) (lookup exp *env*))

	;; everything else should be a list, and we'll decide what to
	;; do next based off the first element of the list.
        ((list? exp)
         (case (car exp)
           ((quote)			; returns second element
					; unevaluated
	    (cadr exp))
	   
           ((cons) 			; creates a cons cell of its
					; arguments, marking them for
					; evaluation but delays
					; evaluation until requested.
	    (cons (list 'closure (nth exp 1))
                  (list 'closure (nth exp 2))))
	       
           ((car) 			; gets the first element of a
					; cons cell and forces it if
					; needed.
            (let ((r (car (normal-eval-impl (nth exp 1)))))
              (if (and (list? r)
                       (eq? (car r) 'closure))
                  (normal-eval-impl (cadr r))
                  r)))
	       
           ((cdr)                       ; gets the second element of a
					; cons cell and forces it if
					; needed
            (let ((r (cdr (normal-eval-impl (nth exp 1)))))
              (if (and (list? r)
                       (not (null? r)) (eq? (car r) 'closure))
                  (normal-eval-impl (cadr r))
                  r)))
	       
           ((if) 			; evaluates the first
					; argument, if it's true then
					; evaluates the 2nd arg and
					; returns it, otherwise
					; evaluates the 3rd arg and
					; returns that.
            (let ((pred (cadr exp))
                  (consq (nth exp 2))
                  (alt (nth exp 3)))
              (if (normal-eval-impl pred)
                  (normal-eval-impl consq)
                  (normal-eval-impl alt))))
	       
           ((lambda)           		; creates a new function
	    (list 'closure (nth exp 2) (nth exp 1)))
	       
           ((define)    		; binds a value to the symbol
					; table
	    (set! *env* (cons (cons (nth exp 1) (nth exp 2))
                              *env*)))
	       
           (else 			; its a funcall so apply the
					; rest of the arguments to the
					; first argument
            (apply-normal (normal-eval-impl (car exp)) (cdr exp)))))
        
        ((else ; unrecognized type
          panic))))

(define (apply-normal proc args)
  ;; if the first argument is a procedure in the underlying
  ;; implementation then call underlying apply after evaluating all
  ;; the args normally.  otherwise, substitute the unevaluated args in
  ;; to the function in place of the params and then evaluate it.
  (cond ((procedure? proc)
	 (apply proc (map normal-eval-impl args)))
	
        ((and (list? proc) 
              (eq? (car proc) 'closure))
         (normal-eval-impl (substitute (nth proc 1) 
                                       (map (partial apply cons)
                                            (zip (nth proc 2) args)))))
	
        (else
	 (normal-eval-impl (cons proc args)))))

(define (force-all exp)
  ;; forces evaluation recursively until no further computation can be done.
  (if (or (not (list? exp)) (null? exp) (null? (car exp)))
      exp
      (cons (if (and (list? (car exp)) 
                     (not (null? (car exp)))
                     (eq? (caar exp) 'closure))
                (force-all (normal-eval-impl (cadr (car exp))))
                (car exp))
            (if (not (null? (cdr exp)))
                (car (force-all (list (cdr exp))))
                '()))))

(define (lookup var env)
  ;; looks up the value associated with a symbol from the environment
  ;; passed in
  (let ((binding (assoc var env)))
        (if binding
            (cdr binding)
            (eval var))))

;; defines global variable used to store bindings for the evaluator
(define *env* '())

;; given a form and an a-list of substitutions, applies the
;; substitution recursively excluding data elements in primitive
;; special forms.
(define (substitute form substitutions)
  (let ((replacement (assoc form substitutions)))
    (cond (replacement
	   (cdr replacement))
	  
          ((list? form)
           (case (car form)
             ((quote)
	      form)
	     
             ((lambda)
	      `(lambda ,(nth form 1) ,(substitute (nth form 2) substitutions)))
	     
             ((define)
	      `(define ,(nth form 1) ,(substitute (nth form 2) substitutions)))
	     
             (else
	      (map (lambda (x) (substitute x substitutions)) form))))
          (else form))))

               
