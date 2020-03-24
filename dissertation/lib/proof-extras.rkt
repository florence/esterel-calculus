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
         ⟶^c
         eval^boolean 
         ≡j
         ⇀j
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
         ⇀2
         DR
         restrict
         closed
         Goes
         K i o
         guard
         (rename-out [L∈2 L∈])
         (except-out
          (all-from-out redex/reduction-semantics)
          nothing)
         (except-out
          (all-from-out esterel-calculus/redex/model/lset
                        esterel-calculus/redex/model/shared
                        esterel-calculus/redex/model/count
                        esterel-calculus/redex/model/potential-function
                        esterel-calculus/redex/model/calculus)
          quasiquote
          L∈))

(require
  redex/reduction-semantics
  esterel-calculus/redex/model/shared
  esterel-calculus/redex/model/lset
  esterel-calculus/redex/model/count
  esterel-calculus/redex/model/potential-function
  
  racket/stxparam
  racket/pretty
  (only-in esterel-calculus/redex/model/reduction
           blocked-pure)
  (only-in esterel-calculus/dissertation/lib/util
           lift-to-compile-time-for-effect!)
  scribble/examples
  (only-in esterel-calculus/redex/model/reduction
           blocked)
  (only-in esterel-calculus/redex/model/calculus ⇀)
  (for-syntax syntax/parse))

(define evalor
  (make-base-eval '(require circuitous esterel-calculus/circuits/compiler redex/reduction-semantics
                            esterel-calculus/redex/model/shared)))

(define-syntax check
  (syntax-parser
    [(_ t ...)
     #'(examples
        #:eval evalor
        t ...)]))

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
  (cs ::= (cstate circuit (w ↦ B⊥) ...))
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
  (B ::= 0 1)
  (wire-value
   ::=
   w B
   (not wire-value)
   (and wire-value wire-value ...)
   (or wire-value wire-value ...)))


(define-judgment-form esterel-eval
  #:mode (wire-in O I)
  [----------
   (wire-in w (cstate _ _ ... (w = _) _ ...))])

(define ⟶^c
  (reduction-relation
   esterel/typeset
   #:domain cs
   (--> cs (update cs w B)
        (judgment-holds (wire-in w cs))
        (where ⊥ (of cs w))
        (judgment-holds (eval^boolean cs (of (circuit-of cs) w) B)))))

(define-judgment-form esterel/typeset
  #:mode (eval^boolean I I O)
  [---------
   (eval^boolean cs B B)]
  [---------
   (eval^boolean cs w (of cs w))]
  ;; not
  [(eval^boolean cs wire-value 0)
   ---------
   (eval^boolean cs (not wire-value) 1)]
  [(eval^boolean cs wire-value 1)
   ---------
   (eval^boolean cs (not wire-value) 0)]
  ;; and
  [(eval^boolean cs wire-value_1 0)
   ---------
   (eval^boolean cs (and wire-value_1 wire-value_2) 0)]
  [(eval^boolean cs wire-value_2 0)
   ---------
   (eval^boolean cs (and wire-value_1 wire-value_2) 0)]
  [(eval^boolean cs wire-value_1 1) (eval^boolean cs wire-value_2 1)
   ---------
   (eval^boolean cs (and wire-value_1 wire-value_2) 1)]
  ;; or
  [(eval^boolean cs wire-value_1 1)
   ---------
   (eval^boolean cs (or wire-value_1 wire-value_2) 1)]
  [(eval^boolean cs wire-value_2 1)
   ---------
   (eval^boolean cs (or wire-value_1 wire-value_2) 1)]
  [(eval^boolean cs wire-value_1 0) (eval^boolean cs wire-value_2 0)
   ---------
   (eval^boolean cs (and wire-value_1 wire-value_2) 0)])
  


(define-metafunction esterel/typeset
  update : cs w B⊥ -> cs
  [(update
    (cstate c
           (w_1 ↦ B⊥_1) ...
           (w ↦ _)
           (w_2 ↦ B⊥_2) ...)
    w B⊥)
   (cstate c
           (w_1 ↦ B⊥_1) ...
           (w  ↦ B⊥)
           (w_2 ↦ B⊥_2) ...)])
(define-metafunction esterel/typeset
  circuit-of : cs -> c
  [(circuit-of (cstate c _ ...)) c])

(define-metafunction esterel/typeset
  guard : c -> c
  [(guard c) c])

(define-judgment-form esterel/typeset
  #:mode     (closed I)
  #:contract (closed p-pure+GO)
  [(where (ρ θr GO q-pure) p-pure+GO) (side-condition (= (FV p-pure+GO) (L0set)))
   -----
   (closed p-pure+GO)])

(define-extended-judgment-form esterel/typeset L∈
  #:mode (L∈2 I I))

(define-metafunction esterel/typeset
  Goes : p-pure -> L
  [(Goes p-pure) ()])

(define-metafunction esterel/typeset
  K : any -> w
  [(K n) ,(string->symbol (~a "K" (term n)))]
  [(K κ) ,(string->symbol (~a "K" (term κ)))])

(define-metafunction esterel/typeset
  i : S -> w
  [(i S) ,(string->symbol (~a (term n) "i"))])
(define-metafunction esterel/typeset
  o : S -> w
  [(o S) ,(string->symbol (~a (term n) "o"))])


(define-metafunction esterel/typeset
  [(of (circ (_ ... (w = e) _ ...) _ _) w) e]
  [(of (cstate c _ ... (w ↦ e) _ ...) w) e]
  [(of circuit w) w]
  [(of cs w) 0]
  [(of Path i) a-wire-name])

(define-metafunction esterel/typeset
  [(compile p-pure+GO) (circ () () ())]
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
  eval^esterel : O p -> (tup θ bool)
  [(eval^esterel O (ρ θr_1 GO p-pure))
   (tup (restrict θr_2 O (ρ θr_2 GO done)) tt)
   (where/hidden q-pure p-pure)
   (side-condition (term (≡ (ρ θr_1 GO p-pure) (ρ θr_2 GO done))))
   (side-condition (term (complete-with-respect-to θr_2 done)))]
  [(eval^esterel O (ρ θr_1 GO p-pure))
   (tup (restrict θr_2 O (ρ θr_2 GO q-pure)) ff)
   (where/hidden (ρ θr_2 GO q-pure) (ρ θr_1 GO p-pure) )
   (side-condition (term (≡ (ρ θr_1 GO p-pure) (ρ θr_2 GO q-pure))))
   (judgment-holds (blocked-pure θr_2 GO hole q-pure))])

(define-metafunction esterel/typeset
  restrict : θ O p -> θ
  [(restrict · O p) ·]
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
  eval^circuit : O circuit -> (tup θ bool)
  [(eval^circuit O circuit) (tup · ff)])
   

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

(define ⇀2
  (reduction-relation
   esterel/typeset

   (--> (ρ GO (in-hole E (present S p q)))
        (ρ GO (in-hole E p))
        (where (in-hole E_1 (emit S)) (in-hole E (present S p q)))
        is-present)

   (--> (in-hole E (emit S)) (par (emit S) (in-hole E nothing))
        emit)))

(define-judgment-form esterel/typeset
  #:contract (≡j p q)
  [----------------- HOLE
   (≡j p q)]
  [----------------- PREMISE
   (≡j p q)]
  [(⇀j p q string)
   ----------------- step
   (≡j p q)]
  [(≡j p q)
   ----------------- ctx
   (≡j (in-hole C p) (in-hole C q))]
  [----------------- refl
   (≡j p p)]
  [(≡j q p)
   ----------------- sym
   (≡j p q)]
  [(≡j p r) (≡j r q)
   ----------------- trans
   (≡j p q)])
(define-judgment-form esterel/typeset
  #:contract (⇀j p q string)
  [(where (_ ... (string q) _ ...) ,(apply-reduction-relation/tag-with-names ⇀ (term p)))
   ---------
   (⇀j p q string)])

 

   
