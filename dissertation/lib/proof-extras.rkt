#lang racket
(provide esterel/typeset
         of
         compile
         =
         =/checked
         not-=
         not-=/checked
         ≃
         ¬≃
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
         closed
         Goes
         K i o
         (rename-out [L∈2 L∈])
         (except-out
          (all-from-out esterel-calculus/redex/model/lset
                        esterel-calculus/redex/model/shared
                        esterel-calculus/redex/model/count
                        esterel-calculus/redex/model/potential-function)
          quasiquote
          L∈))

(require
  redex/reduction-semantics
  esterel-calculus/redex/model/shared
  esterel-calculus/redex/model/lset
  esterel-calculus/redex/model/count
  esterel-calculus/redex/model/potential-function
  (only-in esterel-calculus/redex/model/reduction
           blocked-pure)
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
  (c circuit ::= (circ EQ I O))
  (cs ::= ((w = B⊥) ...))
  (I O ::= (w ...))
  (EQ ::= ((w = wire-value) ...))
  (bool ::= tt ff)
  (So Si ::= S)
  (P Path Pnc ::= (w ...))
  (i ::= n)
  (Cc1 ::=
       (not hole)
       (and w ... hole w ...)
       (or w ... hole w ...))
  (B⊥ ::= 0 1 ⊥)
  (wire-value
   ::=
   w 0 1
   (not wire-value)
   (and wire-value wire-value ...)
   (or wire-value wire-value ...)))

(define-extended-judgment-form esterel/typeset L∈
  #:mode (L∈2 I I))

(define-metafunction esterel/typeset
  Goes : p-pure -> L
  [(Goes p-pure) ()])

(define-metafunction esterel/typeset
  K : n -> w
  [(K n) ,(string->symbol (~a "K" (term n)))])

(define-metafunction esterel/typeset
  i : S -> w
  [(i S) ,(string->symbol (~a (term n) "i"))])
(define-metafunction esterel/typeset
  o : S -> w
  [(o S) ,(string->symbol (~a (term n) "o"))])


(define-metafunction esterel/typeset
  [(of circuit w) w]
  [(of cs w) 0]
  [(of Path i) a-wire-name])

(define-metafunction esterel/typeset
  [(Path∈ w P) #t])

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

(define-judgment-form esterel/typeset
  #:contract (≃ wire-value wire-value)
  #:mode     (≃ I I)
  [(where #t #f)
   ---------------
   (≃ wire-value_1 wire-value_2)])

(define-judgment-form esterel/typeset
  #:contract (¬≃ circuit wire-value)
  #:mode     (¬≃ I I)
  [(where #t #f)
   ---------------
   (¬≃ circuit wire-value)])

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
  [(eval^esterel O (ρ θr_1 GO p-pure))
   (tup (restrict θr_2 O (ρ θr_2 GO done)) tt)
   (where/hidden q-pure p-pure)
   (side-condition (term (≡ (ρ θr_1 GO p-pure) (ρ θr_2 GO done))))
   (side-condition (term (complete-with-respect-to θr_2 done)))]
  [(eval^esterel O (ρ θr_1 GO p-pure))
   (tup (restrict θr O (ρ θr_2 GO q-pure)) ff)
   (where/hidden (ρ θr_2 GO q-pure) (ρ θr_1 GO p-pure) )
   (side-condition (term (≡ (ρ θr_1 GO p-pure) (ρ θr_2 GO q-pure))))
   (judgment-holds (blocked-pure θr_2 GO hole q-pure))])

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
