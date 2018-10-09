#lang racket
(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/lset
         esterel-calculus/redex/model/potential-function
         racket/random)
(provide (all-defined-out))
(module+ test (require rackunit))

(define R*
  (reduction-relation
   esterel-eval #:domain p

   (--> (par p q) (par q p) par-swap)
   (--> (par nothing done) done par-nothing)
   (--> (par (exit n) paused) (exit n) par-1exit)
   (--> (par (exit n_1) (exit n_2)) (exit (max-mf n_1 n_2)) par-2exit)

   (--> (ρ θ (in-hole E (present S p q)))
        (ρ θ (in-hole E p))
        (judgment-holds (θ-ref-S θ S present))
        is-present)

   (--> (ρ θ (in-hole E (present S p q)))
        (ρ θ (in-hole E q))
        (judgment-holds (θ-ref-S θ S absent))
        is-absent)

   (--> (ρ θ (in-hole E (emit S)))
        (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S present))) (in-hole E nothing))
        (judgment-holds (θ-ref-S-∈ θ S (L2set present unknown)))
        emit)

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
        (ρ (mtθ+S S unknown) p)
        signal)

   ;; shared state
   (-->
    (ρ θ (in-hole E (shared s := e p)))
    (ρ θ (in-hole E (ρ (mtθ+s s ev old) p)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    (where ev (δ e θ))
    shared)

   (-->
    (ρ θ (in-hole E (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (δ e θ) new))) (in-hole E nothing))
    (judgment-holds (θ-ref-s θ s _ old))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    set-old)

   (-->
    (ρ θ (in-hole E (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (Σ ev (δ e θ)) new))) (in-hole E nothing))
    (judgment-holds (θ-ref-s θ s ev new))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))

    set-new)
   ;; unshared state
   (-->
    (ρ θ (in-hole E (var x := e p)))
    (ρ θ (in-hole E (ρ (mtθ+x x (δ e θ)) p)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    var)
  (-->
   (ρ θ (in-hole E (:= x e)))
   (ρ (id-but-typeset-some-parens (<- θ (mtθ+x x (δ e θ)))) (in-hole E nothing))
   (judgment-holds (L∈ x (Ldom θ)))
   (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
   (side-condition (term (all-ready? (LFV/e e) θ)))
   set-var)
  ;; if
  (--> (ρ θ (in-hole E (if x p q)))
       (ρ θ (in-hole E q))
       (judgment-holds (θ-ref-x θ x 0))
       if-false)
  (--> (ρ θ (in-hole E (if x p q)))
       (ρ θ (in-hole E p))
       (judgment-holds (L∈ x (Ldom θ)))
       (judgment-holds (¬θ-ref-x θ x 0))
       if-true)

  ;; progression
  (-->
   (ρ θ p)
   (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S absent))) p)
   (judgment-holds (L∈-OI S (Ldom θ)))
   (judgment-holds (L¬∈ S (->S (Can-θ (ρ θ p) ·))))
   (judgment-holds (θ-ref-S θ S unknown))
   absence)
  (-->
   (ρ θ p)
   (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s ev ready))) p)
   (judgment-holds (L∈-OI s (Ldom θ)))
   (judgment-holds (L¬∈ s (->sh (Can-θ (ρ θ p) ·))))
   (judgment-holds (θ-ref-s θ s ev shared-status))
   (judgment-holds (L∈ shared-status (L2set old new)))
   readyness)

  (-->
   (ρ θ_1 (in-hole E (ρ θ_2 p)))
   (ρ (id-but-typeset-some-parens (<- θ_1 θ_2)) (in-hole E p))
   merge)))

(define R (compatible-closure R* esterel-eval p))

(module+ test
  (test-->
   R
   (term
    (ρ
     ((sig S1 unknown) ·)
     (loop^stop
      (present S1 pause pause)
      (present S1 pause pause))))
   (term
    (ρ
     ((sig S1 absent) ·)
     (loop^stop
      (present S1 pause pause)
      (present S1 pause pause)))))
  (test-->
   R*
   (term (ρ {(sig S present) ·} pause)))
  (test-->
   R*
   (term (signal S pause))
   (term (ρ {(sig S unknown) ·} pause)))
  (test-->
   R
   (term (ρ · (signal S pause)))
   (term (ρ · (ρ {(sig S unknown) ·} pause))))
  (test-->
   R*
   (term (ρ ((sig S unknown) ·) pause))
   (term (ρ ((sig S absent) ·) pause)))
  (test-->
   R
   (term (ρ ((sig S unknown) ·) pause))
   (term (ρ ((sig S absent) ·) pause)))
  (test-->>∃
   R
   (term (ρ {(sig So unknown) ·} (ρ {(sig Si unknown) ·} (present Si (emit So) nothing))))
   (term (ρ {(sig So absent) ·} (ρ {(sig Si unknown) ·} (present Si (emit So) nothing)))))
  (test-->
   R
   (term (loop^stop pause (loop pause)))
   (term (loop^stop pause (loop^stop pause pause))))
  (test-->>∃
   R
   (term (loop pause))
   (term (loop^stop pause pause)))
  (test-->>∃
   R
   (term (seq pause (loop pause)))
   (term (seq pause (loop^stop pause pause))))
  (test-->>∃
   R
   (term (seq nothing (loop pause)))
   (term (loop^stop pause pause)))
  (test-->>∃
   R
   (term (loop^stop (exit 0) (loop (exit 0))))
   (term (exit 0)))
  (test-->>∃
   R
   (term (loop^stop nothing (loop pause)))
   (term (loop^stop nothing (loop^stop pause pause))))
  (test-->>∃
   R
   (term (ρ {(sig Si unknown) {(sig So unknown) ·}} (present Si (emit So) nothing)))
   (term (ρ {(sig Si unknown) {(sig So absent) ·}} (present Si (emit So) nothing)))))
