#lang rosette/safe
(provide
 outputs=? deref contains?
 next-unique!)


(define (outputs=? a b #:outputs [outputs #f])
  (andmap
   (lambda (w)
     (implies
      (if outputs
          (member (first w) outputs)
          (contains? b (first w)))
      (equal? (second w) (deref b (first w)))))
   a))

(define (deref t v)
  (define x (assoc v t))
  (second x))
(define (contains? t v)
  (not (false? (assoc v t))))

(require (only-in racket/base make-hash hash-update! hash-ref))
(define counter (make-hash))
(define (next-unique! x)
  (hash-update! counter x add1 (lambda () -1))
  (hash-ref counter x))