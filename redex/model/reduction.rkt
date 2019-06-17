#lang racket
(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/lset
         esterel-calculus/redex/model/potential-function)

(provide esterel-standard
         R
         blocked-or-done
         blocked
         blocked-e
         good)

(module+ test (require rackunit))

(define-extended-language esterel-standard esterel-eval
  (D ::= E))

(define R
  (reduction-relation
   esterel-standard #:domain p
   (--> (ρ θ A (in-hole D (par stopped done))) (ρ θ A (in-hole D (par-⊓ stopped done)))
        (judgment-holds (good θ A D))
        parr)
   ;; TODO this and other rule are not symetric
   (--> (ρ θ A (in-hole D (par paused stopped))) (ρ θ A (in-hole D (par-⊓ paused stopped)))
        (judgment-holds (good θ A D))
        parl)
   (--> (ρ θ A (in-hole D (present S p q)))
        (ρ θ A (in-hole D p))
        (judgment-holds (good θ A D))
        (judgment-holds (θ-ref-S θ S present))
        is-present)
   (--> (ρ θ A (in-hole D (present S p q)))
        (ρ θ A (in-hole D q))
        (judgment-holds (good θ A D))
        (judgment-holds (θ-ref-S θ S absent))
        is-absent)
   (--> (ρ θ GO (in-hole D (emit S)))
        (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S present))) GO (in-hole D nothing))
        (judgment-holds (good θ GO D))
        (judgment-holds (θ-ref-S-∈ θ S (L2set present unknown)))
        emit)
   (--> (ρ θ A (in-hole D (loop p)))
        (ρ θ A (in-hole D (loop^stop p p)))
        (judgment-holds (good θ A D))
        loop)
   (--> (ρ θ A (in-hole D (seq nothing q)))
        (ρ θ A (in-hole D q))
        (judgment-holds (good θ A D))
        seq-done)
   (--> (ρ θ A (in-hole D (seq (exit n) q))) (ρ θ A (in-hole D (exit n)))
        (judgment-holds (good θ A D))
        seq-exit)
   (--> (ρ θ A (in-hole D (loop^stop (exit n) q))) (ρ θ A (in-hole D (exit n)))
        (judgment-holds (good θ A D))
        loop^stop-exit)
   (--> (ρ θ A (in-hole D (suspend stopped S))) (ρ θ A (in-hole D stopped))
        (judgment-holds (good θ A D))
        suspend)
   ;; traps
   (--> (ρ θ A (in-hole D (trap stopped))) (ρ θ A (in-hole D (harp stopped)))
        (judgment-holds (good θ A D))
        trap)
   ;; lifting signals
   (--> (ρ θ A (in-hole D (signal S p)))
        (ρ θ A (in-hole D (ρ (mtθ+S S unknown) WAIT p)))
        (judgment-holds (good θ A D))
        signal)
   ;; shared state
   (-->
    (ρ θ A (in-hole D (shared s := e p)))
    (ρ θ A (in-hole D (ρ (mtθ+s s ev old) WAIT p)))
    (judgment-holds (good θ A D))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    (where ev (δ e θ))
    shared)
   (-->
    (ρ θ GO (in-hole D (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (δ e θ) new))) GO (in-hole D nothing))
    (judgment-holds (good θ GO D))
    (judgment-holds (θ-ref-s θ s _ old))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    set-old)
   (-->
    (ρ θ GO (in-hole D (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (Σ ev (δ e θ)) new))) GO (in-hole D nothing))
    (judgment-holds (good θ GO D))
    (judgment-holds (θ-ref-s θ s ev new))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    set-new)
   ;; unshared state
   (-->
    (ρ θ A (in-hole D (var x := e p)))
    (ρ θ A (in-hole D (ρ (mtθ+x x (δ e θ)) WAIT p)))
    (judgment-holds (good θ A D))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    var)
   (-->
    (ρ θ A (in-hole D (:= x e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+x x (δ e θ)))) A (in-hole D nothing))
    (judgment-holds (good θ A D))
    (judgment-holds (L∈ x (Ldom θ)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    set-var)
   ;; if
   (--> (ρ θ A (in-hole D (if x p q)))
        (ρ θ A (in-hole D q))
        (judgment-holds (good θ A D))
        (judgment-holds (θ-ref-x-but-also-rvalue-false-is-ok-if-ev-is-zero θ x 0))
        if-false)
   (--> (ρ θ A (in-hole D (if x p q)))
        (ρ θ A (in-hole D p))
        (judgment-holds (good θ A D))
        (judgment-holds (L∈ x (Ldom θ)))
        (judgment-holds (¬θ-ref-x-and-also-not-rvalue-false θ x 0))
        if-true)
   ;; lifting
   (-->
    (ρ θ_1 A_1 (in-hole D (ρ θ_2 A_2 p)))
    (ρ (id-but-typeset-some-parens (<- θ_1 θ_2)) (A-⊓ A_1 A_2) (in-hole D p))
    (judgment-holds (good θ_1 A_1 D))
    merge)

   ;; progression
   (-->
    (ρ θ A p)
    (ρ (Lresort (Lset-all-absent2 θ 𝕊)) A p)
    (judgment-holds (blocked-or-done θ A p))
    (where 𝕊 (Lset-sub (Lget-unknown-signals θ) (->S (Can p θ))))
    (side-condition (term (different 𝕊 (L0set))))
    absence)

   (-->
    (ρ θ A p)
    (ρ (Lset-all-ready θ 𝕊_2) A p)
    (judgment-holds (blocked-or-done θ A p))
    (side-condition (term (same (Lset-sub (Lget-unknown-signals θ) (->S (Can p θ))) (L0set))))
    (where 𝕊_1 (Lget-unready-shared θ))
    (where 𝕊_2 (Lset-sub 𝕊_1 (->sh (Can p θ))))
    (side-condition (term (different 𝕊_2 (L0set))))
    readyness)))

(module+ test
  (check-true
   (redex-match?
    esterel-standard
    (ρ θ A p)
    `(ρ ((shar s 1 new) ·) GO (shared s2 := (+ s) pause))))
  (check-true (judgment-holds
               (blocked ((shar s 1 new) ·)
                        GO
                        (shared s2 := (+ s) pause))))
  )

(define-judgment-form esterel-standard
  #:mode     (good I I I)
  #:contract (good θ A D)
  [---------- "hole"
   (good θ A hole)]

  [(good θ A D)
   ---------- "seq"
   (good θ A (seq D q))]

  [(good θ A D)
   ---------- "loop^stop"
   (good θ A (loop^stop D q))]

  [(good θ A D)
   ---------- "parl"
   (good θ A (par D q))]

  [(good θ A D)
   ---------- "par-done"
   (good θ A (par done D))]

  [(good θ A D) (blocked θ A p)
   ---------- "par-blocked"
   (good θ A (par p D))]

  [(good θ A D)
   ---------- "suspend"
   (good θ A (suspend D S))]

  [(good θ A D)
   ---------- "trap"
   (good θ A (trap D))])

(define-judgment-form esterel-standard
  #:mode     (blocked-or-done I I I)
  #:contract (blocked-or-done θ A p)
  [---------- "done"
   (blocked-or-done θ A done)]
  [(blocked θ A p)
   --------- "blocked"
   (blocked-or-done θ A p)])

(define-judgment-form esterel-standard
  #:mode     (blocked I I I)
  #:contract (blocked θ A p)
  [(θ-ref-S θ S unknown)
   ---------- "present"
   (blocked θ A (present S p q))]

  [(blocked θ A p) (blocked θ A q)
   ---------- "par-both"
   (blocked θ A (par p q))]

  [(blocked θ A p)
   ---------- "parl"
   (blocked θ A (par p done))]

  [(blocked θ A q)
   ---------- "parr"
   (blocked θ A (par done q))]

  [(blocked θ A p)
   --------- "seq"
   (blocked θ A (seq p q))]

  [(blocked θ A p)
   --------- "loop^stop"
   (blocked θ A (loop^stop p q))]

  [(blocked θ A p)
   --------- "suspend"
   (blocked θ A (suspend p S))]

  [(blocked θ A p)
   --------- "trap"
   (blocked θ A (trap p))]

  [(blocked-e θ e)
   -------- "shared"
   (blocked θ A (shared s := e p))]

  [(blocked-e θ e)
   -------- "set-shared"
   (blocked θ A (<= s e))]
  
  [-------- "set-shared-wait"
   (blocked θ WAIT (<= s e))]
  
  [-------- "emit-wait"
   (blocked θ WAIT (emit S))]

  [(blocked-e θ e)
   -------- "var"
   (blocked θ A (var x := e p))]

  [(blocked-e θ e)
   -------- "set-seq"
   (blocked θ A (:= x e))])

(module+ test
  (check-false
   (judgment-holds (blocked-e · (+)))))

(define-judgment-form esterel-eval
  #:mode     (blocked-e I I)
  #:contract (blocked-e θ e)
  [(L∈-OI s (LFV/e e)) (θ-ref-s θ s ev new)
   ------------ "new"
   (blocked-e θ e)]
  [(L∈-OI s (LFV/e e)) (θ-ref-s θ s ev old)
   ------------ "old"
   (blocked-e θ e)])

(module+ test
  (check-true
   (judgment-holds
    (blocked-e ((shar ss 1 new) ·)
               (+ ss)))))

(module+ test
  (check-true
   (judgment-holds
    (blocked
     ((sig SJ absent)
      ((sig SP unknown)
       ((sig SQ unknown)
        ((sig Sb unknown)
         ((sig Sdp unknown)
          ((sig Sg unknown)
           ((sig Sk unknown)
            ((sig Sl unknown)
             ((shar srandom-shared1620 0 old)
              ((shar srandom-shared1621 0 old)
               ((sig Srandom-signal1618 unknown)
                ((sig Srandom-signal1619 unknown)
                 ((sig Ss unknown)
                  ((sig Sw unknown)
                   ((sig Sxw unknown) ·)))))))))))))))
     GO
     (seq (present Srandom-signal1618 pause nothing) nothing))))
  (check-true
   (judgment-holds
    (blocked
     ((sig SJ absent)
      ((sig SP unknown)
       ((sig SQ unknown)
        ((sig Sb unknown)
         ((sig Sdp unknown)
          ((sig Sg unknown)
           ((sig Sk unknown)
            ((sig Sl unknown)
             ((shar srandom-shared1620 0 old)
              ((shar srandom-shared1621 0 old)
               ((sig Srandom-signal1618 unknown)
                ((sig Srandom-signal1619 unknown)
                 ((sig Ss unknown)
                  ((sig Sw unknown)
                   ((sig Sxw unknown) ·)))))))))))))))
     WAIT
     (seq (present Srandom-signal1618 pause nothing) nothing))))
  (check-true
   (judgment-holds
    (blocked
     ((sig SJ absent)
      ((sig SP unknown)
       ((sig SQ unknown)
        ((sig Sb unknown)
         ((sig Sdp unknown)
          ((sig Sg unknown)
           ((sig Sk unknown)
            ((sig Sl unknown)
             ((shar srandom-shared1620 0 old)
              ((shar srandom-shared1621 0 old)
               ((sig Srandom-signal1618 unknown)
                ((sig Srandom-signal1619 unknown)
                 ((sig Ss unknown)
                  ((sig Sw unknown)
                   ((sig Sxw unknown) ·)))))))))))))))
     GO
     (suspend
      (present Srandom-signal1618 pause nothing)
      Srandom-signal1618))))
  (check-true
   (judgment-holds
    (blocked
     ((sig SJ absent)
      ((sig SP unknown)
       ((sig SQ unknown)
        ((sig Sb unknown)
         ((sig Sdp unknown)
          ((sig Sg unknown)
           ((sig Sk unknown)
            ((sig Sl unknown)
             ((shar srandom-shared1620 0 old)
              ((shar srandom-shared1621 0 old)
               ((sig Srandom-signal1618 unknown)
                ((sig Srandom-signal1619 unknown)
                 ((sig Ss unknown)
                  ((sig Sw unknown)
                   ((sig Sxw unknown) ·)))))))))))))))
     WAIT
     (suspend
      (present Srandom-signal1618 pause nothing)
      Srandom-signal1618))))

  (check-true
   (judgment-holds
    (good
     ·
     GO
     (par
      (suspend
       (seq hole nothing)
       Srandom-signal2266)
      nothing))))
  (check-true
   (judgment-holds
    (good
     ·
     WAIT
     (par
      (suspend
       (seq hole nothing)
       Srandom-signal2266)
      nothing))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     GO
     (suspend
      (seq (present Srandom-signal2266 pause nothing) nothing)
      Srandom-signal2266))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     WAIT
     (suspend
      (seq (present Srandom-signal2266 pause nothing) nothing)
      Srandom-signal2266))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig SS unknown) ·)
     WAIT
     (par
      (present SS nothing nothing)
      nothing))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig SS unknown) ·)
     GO
     (par
      (present SS nothing nothing)
      nothing))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     GO
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) nothing)
       Srandom-signal2266)
      nothing))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     WAIT
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) nothing)
       Srandom-signal2266)
      nothing))))

  (check-false
   (judgment-holds
    (blocked-or-done
     ·
     GO
     (par pause nothing))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ·
     WAIT
     (par pause nothing))))

  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig SGo present)
      ((sig SR present)
       ((sig SSV present)
        ((sig Sd present)
         ((sig Se present)
          ((shar sg3233 0 new)
           ((sig Sr unknown)
            ((sig SsA unknown) ·))))))))
     GO
     (suspend (<= sg3233 (+ 9)) SA))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig SGo present)
      ((sig SR present)
       ((sig SSV present)
        ((sig Sd present)
         ((sig Se present)
          ((shar sg3233 0 new)
           ((sig Sr unknown)
            ((sig SsA unknown) ·))))))))
     WAIT
     (suspend (<= sg3233 (+ 9)) SA))))

  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (present Sx pause pause))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
     (present Sx pause pause))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (trap (var xv := ((rfunc ,+) sa) (if xv pause pause))))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
     (trap (var xv := ((rfunc ,+) sa) (if xv pause pause))))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv pause pause)))
               (loop pause))
          (present Sx pause pause)))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv pause pause)))
               (loop pause))
          (present Sx pause pause))))))


(module+ test
  (check-equal?
   `(<- ((var· x 1) ·) {(var· x 2) ·})
   `((var· x 2) ·))
  (check-equal?
   (apply-reduction-relation*
    R
    `(ρ ((var· x 1) ·) GO (:= x ((rfunc ,add1) x))))
   `((ρ ((var· x (rvalue 2)) ·) GO nothing)))
  (test-judgment-holds
   (blocked-or-done
    ((sig S1 unknown) ·)
    GO
    (loop^stop
     (present S1 pause pause)
     (present S1 pause pause))))
  (test-judgment-holds
   (blocked-or-done
    ((sig S1 unknown) ·)
    WAIT
    (loop^stop
     (present S1 pause pause)
     (present S1 pause pause))))
  (check-equal?
   (apply-reduction-relation
    R
    (term
     (ρ
      ((sig S1 unknown) ·)
      WAIT
      (loop^stop
       (present S1 pause pause)
       (present S1 pause pause)))))
   (list
    (term
     (ρ
      ((sig S1 absent) ·)
      WAIT
      (loop^stop
       (present S1 pause pause)
       (present S1 pause pause))))))
  (check-equal?
   (apply-reduction-relation*
    R
    `(ρ {(sig SC unknown) ·} WAIT (seq (present SC nothing nothing) (ρ {(sig Si unknown) ·} WAIT (present Si (emit SC) nothing)))))
   `((ρ  {(sig SC absent) {(sig Si absent) ·}}
         WAIT
         nothing)))
  (check-equal?
   (apply-reduction-relation*
    R
    `(ρ {(sig SC unknown) ·} GO (seq (present SC nothing nothing) (ρ {(sig Si unknown) ·}  WAIT (present Si (emit SC) nothing)))))
   `((ρ  {(sig SC absent) {(sig Si absent) ·}}
         GO
         nothing)))
  ;;
  (check-equal?
   (apply-reduction-relation*
    R
    (term
     (ρ ((sig SI present) ((sig ST unknown) ·)) GO
        (signal S
          (loop (seq (emit S)
                     (seq (present SI pause nothing)
                          (seq (present S (emit ST) nothing)
                               (present SI pause nothing)))))))))
   (term
    ((ρ ((sig S present) ((sig SI present) ((sig ST absent) ·))) GO
        (loop^stop
         (seq pause
              (seq (present S (emit ST) nothing)
                   (present SI pause nothing)))
         (seq (emit S)
              (seq (present SI pause nothing)
                   (seq (present S (emit ST) nothing)
                        (present SI pause nothing))))))))))
