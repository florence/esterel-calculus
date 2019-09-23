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

  (define (eval state formulas)
    (define (eval* state formulas bound)
      (if (zero? bound)
          state
          (let ([x (step state formulas)])
            (if (equal? x state)
                state
                (eval* x formulas (sub1 bound))))))
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

  (define (eval/multi states formulas in-registers out-registers)
    (reverse
     (let loop ([registers out-registers]
                [seen (list)]
                [states states])
       (cond
         [(empty? states) seen]
         [else
          (define next (eval (append registers (first states))
                             formulas))
          (if (or (not (constructive? next))
                  (member next seen))
              (cons next seen)
              (loop (map (lambda (in outpair)
                           (list (first outpair)
                                 (deref next in)))
                         in-registers
                         out-registers)
                    (cons next seen)
                    (rest states)))]))))

  (define (result=? a b #:outputs [outputs #f])
    (and
     (outputs=? a b #:outputs outputs)
     (equal? (constructive? a)
             (constructive? b))))

  (define (result=?/multi a b #:outputs [outputs #f])
    (and
     (equal? (length a) (length b))
     (andmap
      (lambda (a b o) (result=? a b #:outputs o))
      a
      b
      (or outputs
          (map (const #f) a)))))

  (define (verify-same P1 P2
                       #:register-pairs [register-pairs #f]
                       #:constraints [extra-constraints 'true]
                       #:outputs [outputs #f])
    (if register-pairs
        (/ 1 0)
        (verify-same/single P1 P2
                            #:constraints extra-constraints
                            #:outputs outputs)))
  (define (verify-same/single P1 P2
                              #:constraints [extra-constraints 'true]
                              #:outputs [outputs #f])
    
    (define-values (r _)
      (with-asserts
       (let ()
         (define inputs (symbolic-inputs (append P1 P2)))
         (define e1 (symbolic-repr P1 inputs))
         (define e2 (symbolic-repr P2 inputs))
         (define r
           (verify
            #:assume
            (assert
             (and
              ((build-expression extra-constraints) inputs)
              (constraints inputs)))
            #:guarantee
            (assert
             (result=? e1 e2
                       #:outputs outputs))))
         (if (unsat? r)
             r
             (list r (evaluate e1 r) (evaluate e2 r))))))
    r)
  (define (symbolic-repr P inputs)
    (eval (build-state P inputs)
          (build-formula P)))

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
    