#lang racket
(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/lset
         esterel-calculus/redex/model/lmap
         esterel-calculus/redex/model/potential-function
         racket/random
         syntax/parse/define)
(provide (all-defined-out))
(module+ test (require rackunit
                       rackunit/text-ui
                       esterel-calculus/redex/rackunit-adaptor))
(define-syntax R (make-rename-transformer #'⟶))
(define-syntax R* (make-rename-transformer #'⇀))

(define ⇀
  (reduction-relation
   esterel-eval #:domain p
   (--> (par p q) (par q p)
        par-swap)
   (--> (par nothing done) done par-nothing)
   (--> (par (exit n) paused) (exit n) par-1exit)
   (--> (par (exit n_1) (exit n_2)) (exit (max-mf n_1 n_2)) par-2exit)

   (--> (ρ θ A (in-hole E (present S p q)))
        (ρ θ A (in-hole E p))
        (judgment-holds (θ-ref-S θ S present))
        is-present)

   (--> (ρ θ A (in-hole E (present S p q)))
        (ρ θ A (in-hole E q))
        (judgment-holds (L∈ S (Ldom θ)))
        (judgment-holds (θ-ref-S θ S unknown))
        (judgment-holds (L¬∈ S (->S (Can-θ (ρ θ A (in-hole E (present S p q))) ·))))
        is-absent)

   (--> (loop p)
        (loop^stop p p)
        loop)

   (--> (seq nothing q) q
        seq-done)

   (--> (seq (exit n) q) (exit n)
        seq-exit)
   
   (--> (loop^stop (exit n) q) (exit n)
        loop^stop-exit)

   (--> (suspend stopped S) stopped
        suspend)

   (--> (trap stopped) (harp stopped)
        trap)

   ;; lifting signals
   (--> (signal S p)
        (ρ (mtθ+S S unknown) WAIT p)
        signal)

   ;; shared state
   (-->
    (ρ θ A (in-hole E (shared s := e p)))
    (ρ θ A (in-hole E (ρ (mtθ+s s ev old) WAIT p)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole E (shared s := e p)))))
    (where ev (δ e θ))
    shared)
   (-->
    (ρ θ A (in-hole E (var x := e p)))
    (ρ θ A (in-hole E (ρ (mtθ+x x (δ e θ)) WAIT p)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole E (var x := e p)))))
    var)
   (-->
    (ρ θ A (in-hole E (:= x e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+x x (δ e θ)))) A (in-hole E nothing))
    (judgment-holds (L∈ x (Ldom θ)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole E (:= x e)))))
    set-var)
   
   ;; if
   (--> (ρ θ A (in-hole E (if x p q)))
        (ρ θ A (in-hole E q))
        (judgment-holds (θ-ref-x θ x 0))
        if-false)
   (--> (ρ θ A (in-hole E (if x p q)))
        (ρ θ A (in-hole E p))
        (judgment-holds (L∈ x (Ldom θ)))
        (judgment-holds (¬θ-ref-x θ x 0))
        if-true)


   (-->
    (ρ θ_1 A_1 (in-hole E (ρ θ_2 A_2 p)))
    (ρ (id-but-typeset-some-parens (<- θ_1 θ_2)) A_1 (in-hole E p))
    (side-condition (term (A->= A_1 A_2))) 
    merge)

   ;; control aware rules
   (--> (ρ θ GO (in-hole E (emit S)))
        (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S present))) GO (in-hole E nothing))
        (judgment-holds (θ-ref-S-∈ θ S (L2set present unknown)))
        emit)
   (-->
    (ρ θ GO (in-hole E (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (δ e θ) new))) GO (in-hole E nothing))
    (judgment-holds (θ-ref-s θ s _ old))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole E (<= s e)))))
    set-old)

   (-->
    (ρ θ GO (in-hole E (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (Σ ev (δ e θ)) new))) GO (in-hole E nothing))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (judgment-holds (θ-ref-s θ s _ new))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole E (<= s e)))))
    (where ev (δ e θ))
    set-new)))
(define ⟶ (compatible-closure ⇀ esterel-eval p))


(module+ test
  (check-equal?
   (apply-reduction-relation/tag-with-names
    ⟶
    (term
     (ρ ((sig S1 unknown) ·)
       WAIT
       (seq
        (present S1 pause nothing)
        (ρ ((sig S2 unknown) ·)
           WAIT
           (seq (emit S2) (present S2 nothing (emit S1))))))))
   '())
  (check-equal?
   (apply-reduction-relation/tag-with-names
    ⟶
    (term 
     (ρ
      ((shar s1 0 old) ·)
      WAIT
      (var
       x
       :=
       (+ s1)
       (ρ ((shar s2 0 old) ·) WAIT (seq (<= s2 (+ 0)) (<= s1 (+ s2))))))))
   empty))