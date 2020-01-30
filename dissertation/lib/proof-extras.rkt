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
         ⟶^s
         DR
         restrict
         closed)

(require
  redex/reduction-semantics
  esterel-calculus/redex/model/shared
  esterel-calculus/redex/model/lset
  (only-in esterel-calculus/dissertation/lib/util
           lift-to-compile-time-for-effect!)
  (only-in esterel-calculus/redex/test/binding
           closed)
  scribble/examples
  (only-in esterel-calculus/redex/model/reduction
           blocked)
  (for-syntax syntax/parse))

(define evalor
  (make-base-eval '(require circuitous esterel-calculus/circuits/compiler redex/reduction-semantics
                            esterel-calculus/redex/model/shared)))

(define-syntax check
  (syntax-parser
    [(_ t)
     #'(examples
        #:eval evalor
        t)]))

(define-extended-language esterel/typeset
  esterel-eval
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
  (bool ::= tt ff)
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
  eval^esterel : O p -> (tup L-S bool)
  [(eval^esterel O p)
   (tup (restrict θr O p) tt)
   (where/hidden q p)
   (side-condition (term (closed p)))
   (side-condition (term (≡ p q)))
   (where (ρ θr GO done) q)
   (side-condition (term (complete-with-respect-to θr done)))]
  [(eval^esterel O p)
   (tup (restrict θr O p) ff)
   (where/hidden q p)
   (side-condition (term (closed p)))
   (side-condition (term (≡ p q)))
   (where (ρ θr A r) q)]
  [(eval^esterel O p)
   (tup (L0set) ff)])

(define-metafunction esterel/typeset
  restrict : θ O p -> L-S
  [(restrict · O p) ()]
  [(restrict ((sig S status) θ) (w_r ... S w_r ...) p)
   ((sig S (DR status S p)) (restrict θ (w_r ... S w_r ...)) p)]
  [(restrict (_ θ) O p)
   (restrict θ O p)])

(define-metafunction esterel/typeset
  DR : status S p -> status
  [(DR unknown S p)
   absent
   (judgment-holds (L¬∈ S (Can-θ p ·)))]
  [(DR status S p)
   status])
  
   
(define-metafunction esterel/typeset
  eval^circuit : O circuit -> any
  [(eval^circuit O circuit) 1])

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
