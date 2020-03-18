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
         blocked-pure
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
        (judgment-holds (L∈ S (Ldom θ)))
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
                         hole
                         (shared s2 := (+ s) pause))))
  (check-true (judgment-holds
               (blocked ((shar s 1 new) ·)
                        GO
                        hole
                        (shared s2 := (+ s) (<= s (+ 1))))))
  )


(define-judgment-form esterel-standard
  #:mode     (leftmost I I I I)
  #:contract (leftmost θ A p D)
  [(leftmost* θ A p hole D)
   ---------- 
   (leftmost θ A p D)])

(define-judgment-form esterel-standard
  #:mode     (leftmost* I I I I I)
  #:contract (leftmost* θ A p E D)
  [---------- "hole"
   (leftmost* θ A p_o E hole)]

  [(leftmost* θ A p_o (in-hole E (seq hole q)) D)
   ---------- "seq"
   (leftmost* θ A p_o E (seq D q))]

  [(leftmost* θ A p_o (in-hole E (loop^stop hole q)) D)
   ---------- "loop^stop"
   (leftmost* θ A p_o E (loop^stop D q))]

  [(leftmost* θ A p_o (in-hole E (par hole q)) D)
   ---------- "parl"
   (leftmost* θ A p_o E (par D q))]

  [(leftmost* θ A p_o (in-hole E (par done hole)) D)
   ---------- "par-done"
   (leftmost* θ A p_o E (par done D))]

  [(leftmost* θ A p_o (in-hole E (par p hole)) D) (blocked θ A (in-hole E (par hole (in-hole D p_o))) p)
   ---------- "par-blocked"
   (leftmost* θ A p_o E (par p D))]

  [(leftmost* θ A p_o (in-hole E (suspend hole S)) D)
   ---------- "suspend"
   (leftmost* θ A p_o E (suspend D S))]

  [(leftmost* θ A p_o (in-hole E (trap hole)) D)
   ---------- "trap"
   (leftmost* θ A p_o E (trap D))])

(define-judgment-form esterel-standard
  #:mode     (blocked-or-done I I I)
  #:contract (blocked-or-done θ A p)
  [---------- "done"
   (blocked-or-done θ A done)]
  [(blocked θ A hole p)
   --------- "blocked"
   (blocked-or-done θ A p)])

(define-judgment-form esterel-standard
  #:mode     (blocked-pure I I I I)
  #:contract (blocked-pure θr A E p)
  [(θ-ref-S θr S unknown) (L∈ S (->S (Can-θ (ρ θr A (in-hole E (present S p q))) ·)))
   ---------- "if"
   (blocked-pure θr A E (present S p q))]

  [(blocked-pure θr A (in-hole E (par hole q)) p) (blocked-pure θr A (in-hole E (par p hole)) q)
   ---------- "par-both"
   (blocked-pure θr A E (par p q))]

  [(blocked-pure θr A (in-hole E (par hole done)) p)
   ---------- "parl"
   (blocked-pure θr A E (par p done))]

  [(blocked-pure θr A (in-hole E (par done hole)) q)
   ---------- "parr"
   (blocked-pure θr A E (par done q))]

  [(blocked-pure θr A (in-hole E (seq hole q)) p)
   --------- "seq"
   (blocked-pure θr A E (seq p q))]

  [(blocked-pure θr A (in-hole E (loop^stop hole q)) p)
   --------- "loop^stop"
   (blocked-pure θr A E (loop^stop p q))]

  [(blocked-pure θr A (in-hole E (suspend hole S)) p)
   --------- "suspend"
   (blocked-pure θr A E (suspend p S))]

  [(blocked-pure θr A (in-hole E (trap hole)) p)
   --------- "trap"
   (blocked-pure θr A E (trap p))]
  [-------- "emit-wait"
   (blocked-pure θr WAIT E (emit S))])


(define-extended-judgment-form esterel-standard blocked-pure
  #:mode     (blocked I I I I)
  #:contract (blocked θr A E p)
  [(blocked-e θr A (in-hole E (shared s := e p)) e)
   -------- "shared"
   (blocked θr A E (shared s := e p))]
  [(blocked-e θr A (in-hole E (<= s e)) e)
   -------- "set-shared"
   (blocked θr A E (<= s e))]
  [-------- "set-shared-wait"
   (blocked θr WAIT E (<= s e))]
  [(blocked-e θr A (in-hole E (var x := e p)) e)
   -------- "var"
   (blocked θr A E (var x := e p))]

  [(blocked-e θr A (in-hole E (:= x e)) e)
   -------- "set-seq"
   (blocked θr A E (:= x e))])

(module+ test
  (check-false
   (judgment-holds (blocked-e · GO (<= s (+)) (+)))))

(define-judgment-form esterel-eval
  #:mode     (blocked-e I I I I)
  #:contract (blocked-e θr A p e)
  [(L∈-OI s (LFV/e e)) (L∈ s (->sh (Can-θ (ρ θr A p) ·)))
   ------------ "not ready"
   (blocked-e θr A p e)])

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
     ((sig SJ unknown)
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
     hole
     (seq (present Srandom-signal1618 pause nothing) nothing))))
  (check-true
   (judgment-holds
    (blocked
     ((sig SJ unknown)
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
     hole
     (seq (present Srandom-signal1618 pause nothing) (emit Srandom-signal1618)))))
  (check-false
   (judgment-holds
    (blocked
     ((sig SJ unknown)
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
     hole
     (seq (present Srandom-signal1618 pause nothing) nothing))))
  (check-true
   (judgment-holds
    (blocked
     ((sig SJ unknown)
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
     hole
     (seq (present Srandom-signal1618 pause nothing) (emit Srandom-signal1618)))))
  (check-false
   (judgment-holds
    (blocked
     ((sig SJ unknown)
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
     hole
     (suspend
      (present Srandom-signal1618 pause nothing)
      Srandom-signal1618))))
  (check-true
   (judgment-holds
    (blocked
     ((sig SJ unknown)
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
     hole
     (suspend
      (present Srandom-signal1618 pause (emit Srandom-signal1618))
      Srandom-signal1618))))
  (check-false
   (judgment-holds
    (blocked
     ((sig SJ unknown)
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
     hole
     (suspend
      (present Srandom-signal1618 pause nothing)
      Srandom-signal1618))))
  (check-true
   (judgment-holds
    (blocked
     ((sig SJ unknown)
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
     hole
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
      Srandom-signal2266))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     GO
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
      Srandom-signal2266))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     WAIT
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
      nothing))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig SS unknown) ·)
     WAIT
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
      nothing))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig SS unknown) ·)
     GO
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
      nothing))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Srandom-signal2266 unknown) ·)
     GO
     (par
      (suspend
       (seq (present Srandom-signal2266 pause nothing) nothing)
       Srandom-signaql2266)
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
      (emit Srandom-signal2266)))))

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
  

  (check-false
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
     GO
     (present Sx pause (emit Sx)))))
  (check-false
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
     WAIT
     (present Sx pause (emit Sx)))))
  (check-false
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
     GO
     (trap (var xv := ((rfunc ,+) sa) (<= sa (+)))))))
  (check-false
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
     WAIT
     (trap (var xv := ((rfunc ,+) sa) (<= sa (+)))))))
  (check-false
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
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
          (present Sx pause pause)))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     GO
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
          (present Sx pause pause)))))
  (check-true
   (judgment-holds
    (blocked-or-done
     ((sig Sx unknown)
      ((shar sa 0 old) ·))
     WAIT
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
     (present S1 pause pause))))
  (test-judgment-does-not-hold
   (blocked-or-done
    ((sig S1 unknown) ·)
    GO
    (loop^stop
     (present S1 pause pause)
     (present S1 pause pause))))
  (test-judgment-does-not-hold
   (blocked-or-done
    ((sig S1 unknown) ·)
    WAIT
    (loop^stop
     (present S1 pause pause)
     (present S1 pause pause))))
  (test-judgment-does-not-hold
   (blocked-or-done
    ((sig S1 unknown) ·)
    WAIT
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
