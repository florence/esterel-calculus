#lang racket
(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/lset
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

   (--> (ρ θr A (in-hole E (present S p q)))
        (ρ θr A (in-hole E p))
        (judgment-holds (θ-ref-S θr S present))
        is-present)

   (--> (ρ θr A (in-hole E (present S p q)))
        (ρ θr A (in-hole E q))
        (judgment-holds (L∈ S (Ldom θr)))
        (judgment-holds (θ-ref-S θr S unknown))
        (judgment-holds (L¬∈ S (->S (Can-θ (ρ θr A (in-hole E (present S p q))) ·))))
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
    (ρ θr A (in-hole E (shared s := e p)))
    (ρ θr A (in-hole E (ρ (mtθ+s s ev old) WAIT p)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
    (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (shared s := e p)))))
    (where ev (δ e θr))
    shared)
   (-->
    (ρ θr A (in-hole E (var x := e p)))
    (ρ θr A (in-hole E (ρ (mtθ+x x (δ e θr)) WAIT p)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
    (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (var x := e p)))))
    var)
   (-->
    (ρ θr A (in-hole E (:= x e)))
    (ρ (id-but-typeset-some-parens (<- θr (mtθ+x x (δ e θr)))) A (in-hole E nothing))
    (judgment-holds (L∈ x (Ldom θr)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
    (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (:= x e)))))
    set-var)
   
   ;; if
   (--> (ρ θr A (in-hole E (if x p q)))
        (ρ θr A (in-hole E q))
        (judgment-holds (θ-ref-x θr x 0))
        if-false)
   (--> (ρ θr A (in-hole E (if x p q)))
        (ρ θr A (in-hole E p))
        (judgment-holds (L∈ x (Ldom θr)))
        (judgment-holds (¬θ-ref-x θr x 0))
        if-true)


   (-->
    (ρ θr_1 A_1 (in-hole E (ρ θr_2 A_2 p)))
    (ρ (id-but-typeset-some-parens (<- θr_1 θr_2)) A_1 (in-hole E p))
    (side-condition (term (A->= A_1 A_2))) 
    merge)

   ;; control aware rules
   (--> (ρ θr GO (in-hole E (emit S)))
        (ρ (id-but-typeset-some-parens (<- θr (mtθ+S S present))) GO (in-hole E nothing))
        (judgment-holds (L∈ S (Ldom θr)))
        emit)
   (-->
    (ρ θr GO (in-hole E (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θr (mtθ+s s (δ e θr) new))) GO (in-hole E nothing))
    (judgment-holds (θ-ref-s θr s _ old))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
    (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (<= s e)))))
    set-old)

   (-->
    (ρ θr GO (in-hole E (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θr (mtθ+s s (Σ ev (δ e θr)) new))) GO (in-hole E nothing))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
    (judgment-holds (θ-ref-s θr s ev new))
    (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (<= s e)))))
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