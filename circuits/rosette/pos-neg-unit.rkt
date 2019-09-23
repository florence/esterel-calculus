#lang rosette/safe
(provide pos-neg@)
(require "sem-sig.rkt"
         "interp-sig.rkt"
         "shared.rkt"
         racket/unit
         racket/match
         (only-in racket/format ~a))

(define-unit pos-neg@
  (import)
  (export sem^)
  (define (initialize-to-false i)
    (map (lambda (x)
           (if (and (list? x)
                    (equal? '- (first x)))
               (list x #t)
               (list x #f)))
         i))

  (define (f-or a b)
    (lambda (w)
      (or (a w) (b w))))
  (define (f-and a b)
    (lambda (w)
      (and (a w) (b w))))
  (define (f-not n)
    (lambda (w)
      (not (n w))))
  (define (symbolic-boolean name)
    (constant (~a name "$" (next-unique! name)) boolean?))
  (define (constraints I)
    (andmap
     (λ (x)
       (implies
        (and (list? x)
             (eq? (first (first x)) '+)
             (contains? I `(- ,(second (first x)))))
        (not (and (second x)
                  (deref I `(- ,(second (first x))))))))
     I))
  (define (constructive? P)
    (andmap
     (lambda (x)
       (implies 
        (and (list? x)
             (eq? (first (first x)) '+)
             (contains? P `(- ,(second (first x)))))
        (or (second x)
            (deref P `(- ,(second (first x)))))))
     P)))