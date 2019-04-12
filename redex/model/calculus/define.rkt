#lang debug racket
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

(define-metafunction esterel-eval
  done<? : p p -> boolean
  [(done<? (exit n) nothing) #t]
  [(done<? paused nothing) #t]
  [(done<? paused (exit n)) #t]
  [(done<? _ _) #f])

(define use-fast-par-swap? (make-parameter #f))

(define R-base
  (reduction-relation
   esterel-eval #:domain p
   (--> (par p q) (par q p)
        (side-condition/hidden
         (implies (use-fast-par-swap?)
                  (term (done<? p q))))
        par-swap)
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

(define-syntax R-write
  (syntax-parser
    [(_ P*)
     #:with P (datum->syntax #'P* 'P #f)
     #`(let-syntax ([P (make-rename-transformer #'P*)])
         (reduction-relation
          esterel-eval #:domain p
   
          (--> (in-hole C (ρ θ (in-hole E (emit S))))
               (in-hole C (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S present))) (in-hole E nothing)))
               (judgment-holds (θ-ref-S-∈ θ S (L2set present unknown)))
               (side-condition (term (P (in-hole C (ρ θ E)) S)))
               emit)
          (-->
           (in-hole C (ρ θ (in-hole E (<= s e))))
           (in-hole C (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (δ e θ) new))) (in-hole E nothing)))
           (judgment-holds (θ-ref-s θ s _ old))
           (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
           (side-condition (term (all-ready? (LFV/e e) θ)))
           (side-condition (term (P (in-hole C (ρ θ E)) s)))
           set-old)

          (-->
           (in-hole C (ρ θ (in-hole E (<= s e))))
           (in-hole C (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (Σ ev (δ e θ)) new))) (in-hole E nothing)))
           (judgment-holds (θ-ref-s θ s ev new))
           (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
           (side-condition (term (all-ready? (LFV/e e) θ)))
           (side-condition (term (P (in-hole C (ρ θ E)) S)))
           set-new)))]))

(define-metafunction esterel-eval
  reassemble : C V -> p
  [(reassemble C S) (in-hole C (emit S))]
  [(reassemble C S) (in-hole C (<= s (+ 1)))])                                                                                               

(define-simple-macro (MR P)
  (union-reduction-relations
   (compatible-closure R-base esterel-eval p)
   (R-write P)))
