#lang rosette/safe
(provide
 outputs=? deref contains?
 next-unique!)


(define (outputs=? a b)
  (andmap
   (lambda (w)
     (implies
      (contains? b (first w))
      (equal? (second w) (deref b (first w)))))
   a))

(define (deref t v)
  (define x (assoc v t))
  (second x))
(define (contains? t v)
  (not (false? (assoc v t))))

(define counter 0)
(define (next-unique!)
  (define x counter)
  (set! counter (add1 counter))
  x)