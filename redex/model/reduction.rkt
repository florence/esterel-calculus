#lang racket
(require esterel-calculus/redex/rackunit-adaptor
         racket/require
         (subtract-in redex/reduction-semantics
                      esterel-calculus/redex/rackunit-adaptor)
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/lset
         esterel-calculus/redex/model/potential-function)

(provide esterel-standard
         R
         blocked-or-done
         blocked
         blocked-e
         leftmost)

(module+ test (require rackunit))

(define-extended-language esterel-standard esterel-eval
  (D ::= E))

(define R
  (reduction-relation
   esterel-standard #:domain p
   (--> (ρ θ A (in-hole D (par stopped done))) (ρ θ A (in-hole D (par-⊓ stopped done)))
        (judgment-holds (leftmost θ A (par stopped done) D))
        parr)
   (--> (ρ θ A (in-hole D (par paused stopped))) (ρ θ A (in-hole D (par-⊓ paused stopped)))
        (judgment-holds (leftmost θ A (par paused stopped) D))
        parl)
   (--> (ρ θ A (in-hole D (present S p q)))
        (ρ θ A (in-hole D p))
        (judgment-holds (leftmost θ A (present S p q) D))
        (judgment-holds (θ-ref-S θ S present))
        is-present)
   (--> (ρ θ A (in-hole D (present S p q)))
        (ρ θ A (in-hole D q))
        (judgment-holds (leftmost θ A (present S p q) D))
        (judgment-holds (L∈-OI S (Ldom θ)))
        (judgment-holds (θ-ref-S θ S unknown))
        (judgment-holds (L¬∈ S (->S (Can-θ (ρ θ A (in-hole D (present S p q))) ·))))
        is-absent)
   (--> (ρ θ GO (in-hole D (emit S)))
        (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S present))) GO (in-hole D nothing))
        (judgment-holds (leftmost θ GO (emit S) D))
        (judgment-holds (θ-ref-S-∈ θ S (L2set present unknown)))
        emit)
   (--> (ρ θ A (in-hole D (loop p)))
        (ρ θ A (in-hole D (loop^stop p p)))
        (judgment-holds (leftmost θ A (loop p) D))
        loop)
   (--> (ρ θ A (in-hole D (seq nothing q)))
        (ρ θ A (in-hole D q))
        (judgment-holds (leftmost θ A (seq nothing q) D))
        seq-done)
   (--> (ρ θ A (in-hole D (seq (exit n) q))) (ρ θ A (in-hole D (exit n)))
        (judgment-holds (leftmost θ A (seq (exit n) q) D))
        seq-exit)
   (--> (ρ θ A (in-hole D (loop^stop (exit n) q))) (ρ θ A (in-hole D (exit n)))
        (judgment-holds (leftmost θ A (loop^stop (exit n) q) D))
        loop^stop-exit)
   (--> (ρ θ A (in-hole D (suspend stopped S))) (ρ θ A (in-hole D stopped))
        (judgment-holds (leftmost θ A (suspend stopped S) D))
        suspend)
   ;; traps
   (--> (ρ θ A (in-hole D (trap stopped))) (ρ θ A (in-hole D (harp stopped)))
        (judgment-holds (leftmost θ A (trap stopped) D))
        trap)
   ;; lifting signals
   (--> (ρ θ A (in-hole D (signal S p)))
        (ρ θ A (in-hole D (ρ (mtθ+S S unknown) WAIT p)))
        (judgment-holds (leftmost θ A (signal S p) D))
        signal)
   ;; shared state
   (-->
    (ρ θ A (in-hole D (shared s := e p)))
    (ρ θ A (in-hole D (ρ (mtθ+s s ev old) WAIT p)))
    (judgment-holds (leftmost θ A (shared s := e p) D))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole D (shared s := e p)))))
    (where ev (δ e θ))
    shared)
   (-->
    (ρ θ GO (in-hole D (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (δ e θ) new))) GO (in-hole D nothing))
    (judgment-holds (leftmost θ GO (<= s e) D))
    (judgment-holds (θ-ref-s θ s _ old))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole D (<= s e)))))
    set-old)
   (-->
    (ρ θ GO (in-hole D (<= s e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (Σ ev (δ e θ)) new))) GO (in-hole D nothing))
    (judgment-holds (leftmost θ GO (<= s e) D))
    (judgment-holds (θ-ref-s θ s ev new))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole D (<= s e)))))
    set-new)
   ;; unshared state
   (-->
    (ρ θ A (in-hole D (var x := e p)))
    (ρ θ A (in-hole D (ρ (mtθ+x x (δ e θ)) WAIT p)))
    (judgment-holds (leftmost θ A (var x := e p) D))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole D (var x := e p)))))
    var)
   (-->
    (ρ θ A (in-hole D (:= x e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+x x (δ e θ)))) A (in-hole D nothing))
    (judgment-holds (leftmost θ A (:= x e) D))
    (judgment-holds (L∈ x (Ldom θ)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ (in-hole D (:= x e)))))
    set-var)
   ;; if
   (--> (ρ θ A (in-hole D (if x p q)))
        (ρ θ A (in-hole D q))
        (judgment-holds (leftmost θ A (if x p q) D))
        (judgment-holds (θ-ref-x-but-also-rvalue-false-is-ok-if-ev-is-zero θ x 0))
        if-false)
   (--> (ρ θ A (in-hole D (if x p q)))
        (ρ θ A (in-hole D p))
        (judgment-holds (leftmost θ A (if x p q) D))
        (judgment-holds (L∈ x (Ldom θ)))
        (judgment-holds (¬θ-ref-x-and-also-not-rvalue-false θ x 0))
        if-true)
   ;; lifting
   (-->
    (ρ θ_1 A_1 (in-hole D (ρ θ_2 A_2 p)))
    (ρ (id-but-typeset-some-parens (<- θ_1 θ_2)) A_1 (in-hole D p))
    (judgment-holds (leftmost θ_1 A_1 (ρ θ_2 A_2 p) D))
    (side-condition (term (A->= A_1 A_2)))
    merge)))

(module+ test
  (check-true
   (redex-match?
    esterel-standard
    (ρ θ A p)
    `(ρ ((shar s 1 new) ·) GO (shared s2 := (+ s) pause))))
  (check-false (judgment-holds
                (blocked ((shar s 1 new) ·)
                         GO
                         (shared s2 := (+ s) pause)
                         (shared s2 := (+ s) pause))))
  (check-true (judgment-holds
               (blocked ((shar s 1 new) ·)
                        GO
                        (shared s2 := (+ s) (<= s (+ 1)))
                        (shared s2 := (+ s) (<= s (+ 1))))))
  )


(define-judgment-form esterel-standard
  #:mode     (leftmost I I I I)
  #:contract (leftmost θ A p D)
  [(leftmost* θ A (in-hole D p) D)
   ---------- 
   (leftmost θ A p D)])

(define-judgment-form esterel-standard
  #:mode     (leftmost* I I I I)
  #:contract (leftmost* θ A p D)
  [---------- "hole"
   (leftmost* θ A p hole)]

  [(leftmost* θ A p D)
   ---------- "seq"
   (leftmost* θ A p (seq D q))]

  [(leftmost* θ A p D)
   ---------- "loop^stop"
   (leftmost* θ A p (loop^stop D q))]

  [(leftmost* θ A p D)
   ---------- "parl"
   (leftmost* θ A p (par D q))]

  [(leftmost* θ A p D)
   ---------- "par-done"
   (leftmost* θ A p (par done D))]

  [(leftmost* θ A q D) (blocked θ A q p)
   ---------- "par-blocked"
   (leftmost* θ A q (par p D))]

  [(leftmost* θ A p D)
   ---------- "suspend"
   (leftmost* θ A p (suspend D S))]

  [(leftmost* θ A p D)
   ---------- "trap"
   (leftmost* θ A p (trap D))])

(define-judgment-form esterel-standard
  #:mode     (blocked-or-done I I I I)
  #:contract (blocked-or-done θ A p p)
  [---------- "done"
   (blocked-or-done θ A p done)]
  [(blocked θ A q p)
   --------- "blocked"
   (blocked-or-done θ A q p)])

(define-judgment-form esterel-standard
  #:mode     (blocked I I I I)
  #:contract (blocked θ A p p)
  [(θ-ref-S θ S unknown)
   (L∈ S (->S (Can-θ (ρ θ A q_outer) ·)))
   ---------- "present"
   (blocked θ A q_outer (present S p q))]

  [(blocked θ A q_outer p) (blocked θ A q_outer q)
   ---------- "par-both"
   (blocked θ A q_outer (par p q))]

  [(blocked θ A q_outer p)
   ---------- "parl"
   (blocked θ A q_outer (par p done))]

  [(blocked θ A q_outer q)
   ---------- "parr"
   (blocked θ A q_outer (par done q))]

  [(blocked θ A q_outer p)
   --------- "seq"
   (blocked θ A q_outer (seq p q))]

  [(blocked θ A q_outer p)
   --------- "loop^stop"
   (blocked θ A q_outer (loop^stop p q))]

  [(blocked θ A q_outer p)
   --------- "suspend"
   (blocked θ A q_outer (suspend p S))]

  [(blocked θ A q_outer p)
   --------- "trap"
   (blocked θ A q_outer (trap p))]

  [(blocked-e θ A q_outer e)
   -------- "shared"
   (blocked θ A q_outer (shared s := e p))]

  [(blocked-e θ A q_outer e)
   -------- "set-shared"
   (blocked θ A q_outer (<= s e))]
  
  [-------- "set-shared-wait"
   (blocked θ WAIT q_outer (<= s e))]
  
  [-------- "emit-wait"
   (blocked θ WAIT q_outer (emit S))]

  [(blocked-e θ A q_outer e)
   -------- "var"
   (blocked θ A q_outer (var x := e p))]

  [(blocked-e θ A q_outer e)
   -------- "set-seq"
   (blocked θ A q_outer (:= x e))])

(module+ test
  (check-false
   (judgment-holds (blocked-e · GO (<= s (+)) (+)))))

(define-judgment-form esterel-eval
  #:mode     (blocked-e I I I I)
  #:contract (blocked-e θ A p e)
  [(L∈-OI s (LFV/e e))
   (L∈ s (->sh (Can-θ (ρ θ A p) ·)))
   ------------ "not ready"
   (blocked-e θ A p e)])

(module+ test
  (check-false
   (judgment-holds
    (blocked-e ((shar ss 1 new) ·)
               GO
               (<= s1 (+ ss))
               (+ ss))))
  (check-true
   (judgment-holds
    (blocked-e ((shar ss 1 new) ·)
               GO
               (<= ss (+ ss))
               (+ ss)))))

(module+ test
  (check-false
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
     (seq (present Srandom-signal1618 pause nothing) nothing)
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
     (seq (present Srandom-signal1618 pause nothing) (emit Srandom-signal1618))
     (seq (present Srandom-signal1618 pause nothing) (emit Srandom-signal1618)))))
  (check-false
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
     (seq (present Srandom-signal1618 pause nothing) nothing)
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
     (seq (present Srandom-signal1618 pause nothing) (emit Srandom-signal1618))
     (seq (present Srandom-signal1618 pause nothing) (emit Srandom-signal1618)))))
  (check-false
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
      Srandom-signal1618)
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
     GO
     (suspend
      (present Srandom-signal1618 pause (emit Srandom-signal1618))
      Srandom-signal1618)
     (suspend
      (present Srandom-signal1618 pause (emit Srandom-signal1618))
      Srandom-signal1618))))
  (check-false
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
      Srandom-signal1618)
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
      (present Srandom-signal1618 pause (emit Srandom-signal1618))
      Srandom-signal1618)
     (suspend
      (present Srandom-signal1618 pause (emit Srandom-signal1618))
      Srandom-signal1618))))

  (check-true
   (judgment-holds
    (leftmost
     ·
     GO
     nothing
     (par
      (suspend
       (seq hole nothing)
       Srandom-signal2266)
      nothing))))
  (check-true
   (judgment-holds
    (leftmost
     ·
     WAIT
     nothing
     (par
      (suspend
       (seq hole nothing)
       Srandom-signal2266)
      nothing))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     GO
     (suspend
      (seq (present Srandom-signal2266 pause nothing) nothing)
      Srandom-signal2266)
     (suspend
      (seq (present Srandom-signal2266 pause nothing) nothing)
      Srandom-signal2266))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     GO
     (suspend
      (seq (present Srandom-signal2266 pause nothing) (emit Srandom-signal2266))
      Srandom-signal2266)
     (suspend
      (seq (present Srandom-signal2266 pause nothing) (emit Srandom-signal2266))
      Srandom-signal2266))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     WAIT
     (suspend
      (seq (present Srandom-signal2266 pause nothing) nothing)
      Srandom-signal2266)
     (suspend
      (seq (present Srandom-signal2266 pause nothing) nothing)
      Srandom-signal2266))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     WAIT
     (suspend
      (seq (present Srandom-signal2266 pause nothing) (emit Srandom-signal2266))
      Srandom-signal2266)
     (suspend
      (seq (present Srandom-signal2266 pause nothing) (emit Srandom-signal2266))
      Srandom-signal2266))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig SS unknown) ·)
     WAIT
     (par
      (present SS nothing nothing)
      nothing)
     (par
      (present SS nothing nothing)
      nothing))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig SS unknown) ·)
     WAIT
     (par
      (present SS nothing nothing)
      (emit SS))
     (par
      (present SS nothing nothing)
      (emit SS)))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig SS unknown) ·)
     GO
     (par
      (present SS nothing nothing)
      nothing)
     (par
      (present SS nothing nothing)
      nothing))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig SS unknown) ·)
     GO
     (par
      (present SS nothing nothing)
      (emit SS))
     (par
      (present SS nothing nothing)
      (emit SS)))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig SS unknown) ·)
     GO
     (par
      (present SS nothing (emit SS))
      nothing)
     (par
      (present SS nothing (emit SS))
      nothing))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     GO
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) nothing)
       Srandom-signal2266)
      nothing)
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) nothing)
       Srandom-signal2266)
      nothing))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     GO
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) nothing)
       Srandom-signal2266)
      (emit Srandom-signal2266))
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) nothing)
       Srandom-signal2266)
      (emit Srandom-signal2266)))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     GO
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) (emit Srandom-signal2266))
       Srandom-signal2266)
      nothing)
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) (emit Srandom-signal2266))
       Srandom-signal2266)
      nothing))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     WAIT
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) nothing)
       Srandom-signal2266)
      nothing)
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
      (emit Srandom-signal2266))
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) nothing)
       Srandom-signal2266)
      (emit Srandom-signal2266)))))

  (check-false
   (judgment-holds
    (blocked-or-done
     ·
     GO
     (par pause nothing)
     (par pause nothing))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ·
     WAIT
     (par pause nothing)
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
     (suspend (<= sg3233 (+ 9)) SA)
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
     (suspend (<= sg3233 (+ 9)) SA)
     (suspend (<= sg3233 (+ 9)) SA))))
  

  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (present Sx pause pause)
     (present Sx pause pause))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (present Sx pause (emit Sx))
     (present Sx pause (emit Sx)))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
     (present Sx pause pause)
     (present Sx pause pause))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
     (present Sx pause (emit Sx))
     (present Sx pause (emit Sx)))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (trap (var xv := ((rfunc ,+) sa) (if xv pause pause)))
     (trap (var xv := ((rfunc ,+) sa) (if xv pause pause))))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (trap (var xv := ((rfunc ,+) sa) (<= sa (+))))
     (trap (var xv := ((rfunc ,+) sa) (<= sa (+)))))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
     (trap (var xv := ((rfunc ,+) sa) (if xv pause pause)))
     (trap (var xv := ((rfunc ,+) sa) (if xv pause pause))))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
     (trap (var xv := ((rfunc ,+) sa) (<= sa (+))))
     (trap (var xv := ((rfunc ,+) sa) (<= sa (+)))))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv pause pause)))
               (loop pause))
          (present Sx pause pause))
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv pause pause)))
               (loop pause))
          (present Sx pause pause)))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv nothing pause)))
               (loop (seq (<= sa (+)) pause)))
          (present Sx pause pause))
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv nothing pause)))
               (loop (seq (<= sa (+)) pause)))
          (present Sx pause pause)))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv nothing pause)))
               (loop (seq (<= sa (+)) (seq (emit Sx) pause))))
          (present Sx pause pause))
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv nothing pause)))
               (loop (seq (<= sa (+)) (seq (emit Sx) pause))))
          (present Sx pause pause)))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv pause pause)))
               (loop pause))
          (present Sx pause pause))
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv pause pause)))
               (loop pause))
          (present Sx pause pause)))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv nothing pause)))
               (loop (seq (<= sa (+)) (seq (emit Sx) pause))))
          (present Sx pause pause))
     (par (seq (trap (var xv := ((rfunc ,+) sa) (if xv nothing pause)))
               (loop (seq (<= sa (+)) (seq (emit Sx) pause))))
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
  (test-judgment-does-not-hold
   (blocked-or-done
    ((sig S1 unknown) ·)
    GO
    (loop^stop
     (present S1 pause pause)
     (present S1 pause pause))
    (loop^stop
     (present S1 pause pause)
     (present S1 pause pause))))
  (test-judgment-holds
   (blocked-or-done
    ((sig S1 unknown) ·)
    GO
    (loop^stop
     (present S1 pause (emit S1))
     (present S1 pause pause))
    (loop^stop
     (present S1 pause pause)
     (present S1 pause pause))))
  (test-judgment-does-not-hold
   (blocked-or-done
    ((sig S1 unknown) ·)
    WAIT
    (loop^stop
     (present S1 pause pause)
     (present S1 pause pause))
    (loop^stop
     (present S1 pause pause)
     (present S1 pause pause))))
  (test-judgment-holds
   (blocked-or-done
    ((sig S1 unknown) ·)
    WAIT
    (loop^stop
     (seq
      (present S1 nothing pause)
      (emit S1))
     (present S1 pause pause))
    (loop^stop
     (seq
      (present S1 pause pause)
      (emit S1))
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
      ((sig S1 unknown) ·)
      WAIT
      (loop^stop
       pause
       (present S1 pause pause))))))
  (check-equal?
   (apply-reduction-relation*
    R
    `(ρ {(sig SC unknown) ·} WAIT
        (seq (present SC nothing nothing)
             (ρ {(sig Si unknown) ·} WAIT
                (present Si (emit SC) nothing)))))
   `((ρ  {(sig SC unknown) {(sig Si unknown) ·}}
         WAIT
         nothing)))
  (check-false
   (term (is-complete?
          (ρ  {(sig SC unknown) {(sig Si unknown) ·}}
              WAIT
              nothing))))
  (check-true
   (term (is-complete?
          (ρ  {(sig SC unknown) {(sig Si unknown) ·}}
              GO
              nothing))))
  (check-equal?
   (apply-reduction-relation*
    R
    `(ρ {(sig SC unknown) ·} GO
        (seq (present SC nothing nothing)
             (ρ {(sig Si unknown) ·}
                WAIT
                (present Si (emit SC) nothing)))))
   `((ρ  {(sig SC unknown) {(sig Si unknown) ·}}
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
    ((ρ ((sig S present) ((sig SI present) ((sig ST unknown) ·))) GO
        (loop^stop
         (seq pause
              (seq (present S (emit ST) nothing)
                   (present SI pause nothing)))
         (seq (emit S)
              (seq (present SI pause nothing)
                   (seq (present S (emit ST) nothing)
                        (present SI pause nothing)))))))))
  (check-true
   (term
    (is-complete?
     (ρ ((sig S present) ((sig SI present) ((sig ST unknown) ·))) GO
        (loop^stop
         (seq pause
              (seq (present S (emit ST) nothing)
                   (present SI pause nothing)))
         (seq (emit S)
              (seq (present SI pause nothing)
                   (seq (present S (emit ST) nothing)
                        (present SI pause nothing))))))))))
