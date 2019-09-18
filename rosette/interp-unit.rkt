#lang rosette/safe
(provide interp@)
(require "sem-sig.rkt"
         "interp-sig.rkt"
         "shared.rkt"
         racket/unit
         racket/match)
(module+ test (require rackunit))

(define-unit interp@
  (import sem^)
  (export interp^)

  (define (eval state formulas [wto? #f])
    (define (eval* state formulas bound)
      (if (zero? bound)
          state
          (eval* (step state formulas) formulas (sub1 bound))))
    (eval* state formulas (length formulas)))

  (define (step state formulas)
    (map 
     (lambda (w)
       (match-define (list name v) w)
       (define f
         (and (contains? formulas name)
              (deref formulas name)))
       (if f
           (list name (f state))
           w))
     state))

  (define (result=? a b)
    (and
     (outputs=? a b)
     (equal? (constructive? a)
             (constructive? b))))

  (define (verify-same P1 P2)
    (with-asserts
     (let ()
       (define inputs (symbolic-inputs (append P1 P2)))
       (verify
        #:assume
        (assert (constraints inputs))
        #:guarantee
        (assert
         (result=?
          (eval (build-state P1 inputs)
                (build-formula P1)
                #t)
          (eval (build-state P2 inputs)
                (build-formula P2)
                #t)))))))

  (define (build-formula P)
    (map
     (lambda (x)
       (match-define (list n '= e) x)
       (list n (build-expression e)))
     P))

  (define (build-expression e)
    (match e
      [`(and ,e1 ,e2)
       (f-and (build-expression e1)
              (build-expression e2))]
      [`(or ,e1 ,e2)
       (f-or (build-expression e1)
             (build-expression e2))]
      [`(not ,e1)
       (f-not (build-expression e1))]
      [`true (lambda (_) #t)]
      [`false (lambda (_) #f)]
      [`⊥ (lambda (_) '⊥)]
      [x
       (lambda (w) (deref w x))]))

  (define (build-state P inputs)
    (append
     (map
      (lambda (w) (list (first w) '⊥))
      P)
     inputs))
  (define (symbolic-inputs P)
    (map
     (lambda (x) (list x (symbolic-boolean x)))
     (FV P))))

(define (FV P)
  (remove-duplicates
   (remove* (map first P)
            (vars P))))
(define (vars P)
  (append-map get-vars (map third P)))
(define (get-vars e)
  (match e
    [`(and ,e1 ,e2)
     (append (get-vars e1) (get-vars e2))]
    [`(or ,e1 ,e2)
     (append (get-vars e1) (get-vars e2))]
    [`(not ,e1)
     (get-vars e1)]
    [`true (list)]
    [`false (list)]
    [`⊥ (list)]
    [x
     (list x)]))
    