#lang racket
(provide esterel/typeset
         of
         compile
         =
         =/checked
         not-=
         not-=/checked
         ≃
         =>
         outputs
         inputs
         parens
         binds)

(require
  redex/reduction-semantics
  esterel-calculus/redex/model/shared)

(define-extended-language esterel/typeset
  esterel-eval
  (p-pure q-pure ::=
          nothing
          pause
          (seq p-pure p-pure)
          (par p-pure p-pure)
          (trap p-pure)
          (exit n)
          (signal S p-pure)
          (suspend p-pure S)
          (present S p-pure p-pure)
          (emit S)
          (loop p-pure)
          (loop^stop p-pure q-pure)
          (ρ θ A p-pure))
             
  (p-unex q-unex ::=
          nothing pause
          (seq p-unex q-unex) (par p-unex p-unex)
          (loop p-unex)
          (trap p-unex) (exit n)
          (signal S p-unex) (emit S)
          (suspend p-unex S) (present S p-unex p-unex))
  (wire w ::= variable)
  (wire-value
   ::=
   w
   0 1
   (and wire-value wire-value ...)
   (or wire-value wire-value ...)
   (not wire-value)))


(define-metafunction esterel/typeset
  of : circuit w -> wire-value
  [(of circuit w) w])

(define-metafunction esterel/typeset
  [(compile p) circuit]
  [(compile θ) circuit]
  [(compile status) wire-value]
  [(compile #f) wire-value])

(define-metafunction esterel/typeset
  = : any ... -> any
  [(= _ ...) 1])

(define-metafunction esterel/typeset
  =/checked : any ... -> any
  [(=/checked any any) 1]
  [(=/checked any any any_r ...)
   (=/checked any any_r ...)])

(define-metafunction esterel/typeset
  [(≃ circuit circuit) 1]
  [(≃ p-pure q-pure) 1])

(define-metafunction esterel/typeset
  => : any ... -> boolean
  [(=> _ ...) #t])

(define-metafunction esterel/typeset
  not-= : any any -> any
  [(not-= _ _) 1])

(define-metafunction esterel/typeset
  not-=/checked : any any -> any
  [(not-=/checked any_1 any_!_1) 1])

(define-metafunction esterel/typeset
  outputs : circuit -> L
  [(outputs _) ()])

(define-metafunction esterel/typeset
  inputs : circuit -> L
  [(inputs _) ()])

(define-metafunction esterel/typeset
  parens : any -> any
  [(parens any) any])

(define-metafunction esterel/typeset
  binds : circuit θ -> boolean
  [(binds _ _) #t])
  