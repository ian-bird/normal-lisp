;; implements left fold
(define (reduce proc base seq)
  (if (null? seq)
      base
      (reduce proc (proc base (car seq)) (cdr seq))))

;; short circuiting or over a list
(define (any? pred seq)
  (cond ((null? seq) #f)
        ((pred (car seq)) #t)
        (else (any? pred (cdr seq)))))

;; decrement
(define (1- n) (- n 1))

;; drops n elements from the front of a list
(define (drop seq n)
  (if (zero? n)
      seq
      (drop (cdr seq) (1- n))))

;; gets the nth element of a list
(define (nth seq n)
  (car (drop seq n)))
