#lang racket
(require rackunit
         "../compiler.rkt"
         (except-in circuitous FV)
         redex/reduction-semantics)

(check-pred
 unsat?
 (verify-same
  (compile-esterel/guard  (term (seq nothing nothing)))
  (compile-esterel  (term (seq nothing nothing)))))
(check-pred
 list?
 (verify-same
  (compile-esterel/guard (term pause))
  (compile-esterel (term pause))))
(check-pred
 unsat?
 (verify-same
  #:constraints '(implies --SEL (not GO))
  (compile-esterel/guard (term pause))
  (compile-esterel (term pause))))
(check-pred
 list?
 (verify-same
  (compile-esterel/guard (term (par pause pause)))
  (compile-esterel (term (par pause pause)))))
(check-pred
 unsat?
 (verify-same
  #:constraints '(implies --SEL (not GO))
  (compile-esterel/guard (term (par pause pause)))
  (compile-esterel (term (par pause pause)))))