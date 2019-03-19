#lang racket
(require esterel-calculus/redex/model/calculus/define
         esterel-calculus/redex/model/shared
         redex/reduction-semantics)
(provide (all-defined-out))

(define-metafunction esterel-eval
  E-C : (in-hole C (ρ θ E)) V -> boolean
  [(E-C (in-hole E_1 (ρ θ E_2)) _)
   #t]
  [(E-C _ _)
   #f])

(define-metafunction esterel-eval
  empty-C : (in-hole C (ρ θ E)) V -> boolean
  [(empty-C (ρ θ E) _) #t]
  [(empty-C _ _) #f])

(define R* (union-reduction-relations R-base (R-write empty-C)))
(define R-empty (MR empty-C))
(define R-E (MR E-C))
(define R (compatible-closure R* esterel-eval p))