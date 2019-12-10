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
         binds
         check
         eval^circuit
         eval^esterel
         ≃^circuit
         ≃^esterel
         ⟶^r
         ⟶^s)

(require
  redex/reduction-semantics
  esterel-calculus/redex/model/shared
  scribble/examples
  (only-in esterel-calculus/redex/model/reduction
           blocked)
  (for-syntax syntax/parse))

(define evalor
  (make-base-eval '(require circuitous esterel-calculus/circuits/compiler redex/reduction-semantics)))

(define-syntax check
  (syntax-parser
    [(_ t)
     #'(examples
        #:eval evalor
        t)]))

(define-extended-language esterel/typeset
  esterel-eval
  (p-pure q-pure r-pure ::=
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
  (c circuit ::= (circ ((w = wire-value) ...) I O))
  (I O ::= (w ...))
  (wire-value
   ::=
   w 0 1
   (not wire-value)
   (and wire-value wire-value ...)
   (or wire-value wire-value ...)))


(define-metafunction esterel/typeset
  [(of circuit w) w])

(define-metafunction esterel/typeset
  [(compile p) (circ () () ())]
  [(compile θ) (circ () () ())]
  [(compile status) 0]
  [(compile #f) 0])

(define-metafunction esterel/typeset
  = : any any any ... -> any
  [(= _ ...) 1])

(define-metafunction esterel/typeset
  =/checked : any any any ... -> any
  [(=/checked any any) 1]
  [(=/checked any any any_r ...)
   (=/checked any any_r ...)])

(define-metafunction esterel/typeset
  [(≃ c_1 c_2) 1]
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
  ;binds : circuit θ -> boolean
  [(binds circuit θ) #t]
  [(binds circuit A) #t])

(define-metafunction esterel/typeset
  eval^esterel : p -> any
  [(eval^esterel p) 1])
(define-metafunction esterel/typeset
  eval^circuit : circuit -> any
  [(eval^circuit circuit) 1])

(define-metafunction esterel/typeset
  [(≃^circuit c_1 c_2) 1])
(define-metafunction esterel/typeset
  ≃^esterel : p q -> any
  [(≃^esterel _ _) 1])
(define-metafunction esterel/typeset
  ⟶^r : p q -> p
  [(⟶^r p q) q])

(define-metafunction esterel/typeset
  ⟶^s : p q -> p
  [(⟶^s p q) q])

(define-judgment-form esterel/typeset
  #:contract (not-blocked θ A E p)
  #:mode     (not-blocked I I I I)
  [(where #f ,(judgment-holds (blocked θ A E p)))
   -------------------
   (not-blocked θ A E p)])
