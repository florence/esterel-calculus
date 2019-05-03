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
(define R ⟶)
(define R* ⇀)

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
        (judgment-holds (θ-ref-S θ S absent))
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
    (side-condition (term (all-ready? (LFV/e e) θ)))
    (where ev (δ e θ))
    shared)
   (-->
    (ρ θ A (in-hole E (var x := e p)))
    (ρ θ A (in-hole E (ρ (mtθ+x x (δ e θ)) WAIT p)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    var)
   (-->
    (ρ θ A (in-hole E (:= x e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+x x (δ e θ)))) A (in-hole E nothing))
    (judgment-holds (L∈ x (Ldom θ)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
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

   ;; progression
   (-->
    (ρ θ A p)
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S absent))) A p)
    (judgment-holds (L∈-OI S (Ldom θ)))
    (judgment-holds (L¬∈ S (->S (Can-θ (ρ θ A p) ·))))
    (judgment-holds (θ-ref-S θ S unknown))
    absence)
   (-->
    (ρ θ A p)
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s ev ready))) A p)
    (judgment-holds (L∈-OI s (Ldom θ)))
    (judgment-holds (L¬∈ s (->sh (Can-θ (ρ θ A p) ·))))
    (judgment-holds (θ-ref-s θ s ev shared-status))
    (judgment-holds (L∈ shared-status (L2set old new)))
    readyness)

   (-->
    (ρ θ_1 A_1 (in-hole E (ρ θ_2 A_2 p)))
    (ρ (id-but-typeset-some-parens (<- θ_1 θ_2)) A_1 (in-hole E p))
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
    (side-condition (term (all-ready? (LFV/e e) θ)))
    set-old)

   (-->
    (ρ θ GO (in-hole E (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (Σ ev (δ e θ)) new))) GO (in-hole E nothing))
    (judgment-holds (θ-ref-s θ s ev new))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    set-new)))
(define ⟶ (compatible-closure ⇀ esterel-eval p))