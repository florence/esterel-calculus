#lang racket

(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         (only-in esterel-calculus/redex/test/binding CB)
         esterel-calculus/redex/model/calculus
         esterel-calculus/redex/model/lset
         esterel-calculus/redex/model/potential-function)

(provide ≡e Eval ⇀ → →*)

(module+ test (require rackunit))

(define-judgment-form esterel-eval
  #:mode (≡e I I I I O)
  #:contract (≡e (p ...) (C ...) (p ...) p q)

  [(→ (C ...) p q)
   ------------------------------ "step"
   (≡e any_sym (C ...) any_p p q)]

  [(≡e (p_1 ... p_2 ...) any_Cc any_ps p q) (CB p)
   ----------------------------------------------- "sym"
   (≡e (p_1 ... p p_2 ...) any_Cc any_ps q p)]

  [------------------------------- "ref"
   (≡e any_sym any_Cc any_ps p p)]

  [(≡e any_sym any_Cc () p_1 p_2) (≡e any_sym any_Cc (p_t2 ...) p_2 p_3)
   --------------------------------------------------------------------- "trn"
   (≡e any_sym any_Cc (p_2 p_t2 ...) p_1 p_3)])

(define-judgment-form esterel-eval
  #:mode (→ I I O)
  #:contract (→ (C ...) p p)
  [(⇀ p q)
   --------------------------------------------------- "context"
   (→ (C_1 ... C C_2 ...) (in-hole C p) (in-hole C q))])

(define-judgment-form esterel-eval
  #:mode (→* I I I O)
  #:contract (→* any (C ...) p q)

  [------------------- "ref"
   (→* () any_2 p p)]

  [(→ (C ...) p_1 p_2) (→* any (C ...) p_2 p_3)
   -------------------------------------------- "step"
   (→* (any) (C ...) p_1 p_3)])

(define-judgment-form esterel-eval
  #:mode (⇀ I O)
  #:contract (⇀ p p)
  [(where (p_1 ... q p_2 ...) ,(apply-reduction-relation R* (term p)))
   -----------
   (⇀ p q)])

(module+ test
  (test-judgment-holds (≡e () () ()
                           (seq pause nothing)
                           (seq pause nothing)))

  (test-judgment-holds (≡e () (hole) ()
                           (seq nothing pause)
                           pause))

  (test-judgment-holds (≡e () (hole (seq hole pause)) ((seq (exit 0) pause))
                           (seq (par nothing (exit 0)) pause)
                           (exit 0)))

  (test-judgment-holds (≡e ((seq nothing (exit 0))) ;; sym
                           (hole (seq hole pause)) ;; C
                           ((seq (exit 0) pause) (exit 0)) ;; trans

                           (seq (par nothing (exit 0)) pause)
                           (seq nothing (exit 0))))

  (test-judgment-holds (≡e ()
                           (hole
                            (ρ ({sig S unknown} ·) hole)
                            (ρ ({sig S present} ·) hole)
                            (ρ ({sig S unknown} ·) (seq hole (emit S)))
                            (ρ ({sig S present} ·) (seq hole (emit S))))
                           ((ρ ({sig S unknown} ·) (seq nothing (emit S)))
                            (ρ ((sig S unknown) ·) (emit S)))

                           (ρ ({sig S unknown} ·) (seq (par nothing nothing) (emit S)))
                           (ρ ((sig S present) ·) nothing)))

  (check-false (judgment-holds (≡e () (hole) (pause nothing) pause nothing))))


(define-judgment-form esterel-eval
  #:contract (Eval (p ...) (C ...) (p ...) p θ L-S)
  #:mode (Eval I I I I I O)
  [(≡e any (C ...) (p_trn ...) (ρ θ p) (ρ θ/c done))
   ------
   (Eval any (C ...) (p_trn ...) p θ (Lpresentin θ/c))])

(define-metafunction esterel-eval
  Lpresentin : θ/c -> L-S
  [(Lpresentin ·) ()]
  [(Lpresentin ({sig S present} θ)) (S (Lpresentin θ))]
  [(Lpresentin (env-v θ)) (Lpresentin θ)])

(module+ test

  (check-equal?
   (judgment-holds (Eval ()
                         ((ρ · hole)
                          (ρ · (seq hole pause)))
                         ((ρ · (seq (exit 0) pause)))
                         (seq (par nothing (exit 0)) pause)
                         ·
                         any) any)
   (list (term (L0set))))

  (check-equal?
   (judgment-holds (Eval ()
                         (hole
                          (ρ ({sig S unknown} ·) hole)
                          (ρ ({sig S present} ·) hole)
                          (ρ ({sig S unknown} ·) (seq hole (emit S)))
                          (ρ ({sig S present} ·) (seq hole (emit S))))
                         ((ρ ({sig S unknown} ·) (seq nothing (emit S)))
                          (ρ ((sig S unknown) ·) (emit S)))

                         (seq (par nothing nothing) (emit S))
                         ({sig S unknown} ·)
                         any)
                   any)
   (list (term (L1set S))))

  (test-judgment-holds (→* () () nothing nothing))

  (check-not-false
   (member
    (term (exit 3))
    (judgment-holds (→* ((()))
                        (hole (seq hole (exit 3)))
                        (seq (par nothing nothing) (exit 3))
                        any)
                    any))))