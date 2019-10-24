#lang racket
(require rackunit
         "../compiler.rkt"
         (except-in circuitous FV)
         redex/reduction-semantics)

(check-equal?
 (circuit-term (compile-esterel (term nothing)))
 (term ((K0 = GO) (SEL = false))))
(check-equal?
 (circuit-term (compile-esterel (term (exit 0))))
 (term ((K2 = GO) (SEL = false))))
(check-equal?
 (circuit-term (compile-esterel (term (emit Ss))))
 (sort
  (term ((K0 = GO)
         (Ss = GO)
         (SEL = false)))
  variable<?
  #:key first))
(check-equal?
 (circuit-term (compile-esterel (term (seq nothing nothing))))
 (sort
  (term ((K0 = K0-internal)
         (K0-internal = GO)
         (SEL = (or false false))))
  variable<?
  #:key first))
(check-equal?
 (circuit-term (compile-esterel (term pause)))
 (sort
  (term ((K1 = GO)
         (K0 = (and reg-out RES))
         (SEL = reg-out)
         (reg-in = (and (not KILL) do-sel))
         (do-sel = (or GO resel))
         (resel = (and SUSP SEL))))
  variable<?
  #:key first))
(check-equal?
 (circuit-term (compile-esterel (term (suspend nothing S))))
 (sort
  (term ((susp-res = (and (not S) do-res))
         (do-res = (and susp-sel RES))
         (SEL = susp-sel)
         (susp-susp = (or SUSP do-susp))
         (do-susp = (and S do-res))
         (K1 = (or do-susp false))
         (susp-sel = false)
         (K0 = GO)))
  variable<?
  #:key first))
(check-equal?
 (circuit-term (compile-esterel (term (seq (exit 3) (nts q 6)))))
 (sort
  (term
   ((K5 = (or GO qK5))
    (q-GO = false)
    (q-SUSP = SUSP)
    (q-KILL = KILL)
    (q-RES = RES)
    (SEL = (or false q-SEL))
    (K0 = qK0)
    (K1 = qK1)
    (K2 = qK2)
    (K3 = qK3)
    (K4 = qK4)
    (K6 = qK6)))
  variable<?
  #:key first))
(check-equal?
 (circuit-term (compile-esterel (term (par nothing nothing))))
 (sort
  (term
   ((killout = KILL)
    (lem1 = (or lem lname))
    (rem1 = (or rem rname))
    (both = (or lname rname))
    (K0 = (and lem1 (and rem1 both)))
    (lem = (and SEL (and RES (not psel))))
    (rem = (and SEL (and RES (not qsel))))
    (SEL = (or psel qsel))
    (psel = false)
    (qsel = false)
    (lname = GO)
    (rname = GO)))
  variable<?
  #:key first))