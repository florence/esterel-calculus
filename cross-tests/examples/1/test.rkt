#lang racket
(require esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/calculus
         redex/reduction-semantics
         rackunit)

(check-equal?
 (apply-reduction-relation*
  R
  (term (signal S (seq (emit S) (present S pause nothing)))))
 '((ρ ((sig S present) ·)  pause)))
