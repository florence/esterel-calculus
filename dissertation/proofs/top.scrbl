#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/calculus
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style]{Core Theorems}

This section contains the core proofs to justify soundness
and adequacy of the calculus with respect to the compilation
function. The core theorem for soundness is
@proof-ref["soundness"], however the most informative
theorem is @proof-ref["Soundness-step"]. The core theorem
for adequacy is @proof-ref["comp-ad"], but the most
informative theorems are
@proof-ref["strongly-cannibalizing"],
@proof-ref["e-v-is-c-v"], and @proof-ref["adequacy-of-can"].


@proof[#:label "soundness"
       #:title "Soundness"
       #:statement
       @list{For all @es[p-pure] and @es[q-pure],
        if @es[(CB p-pure)],
        @es[(≡ p-pure q-pure)],
        @es[(= (of (compile p-pure) SEL) 0)], and
        @es[(= (of (compile q-pure) SEL) 0)]
        then
        @es[(≃^circuit (compile p) (compile q))]}
       #:interpretation @list{This theorem says that, at least for the
        first instant/cycle @es[≡] agrees with @es[≃^circuit]. Therefore
        any change to a program which can be proven correct by @es[≡]
        is correct under @es[≃^circuit].}
       #:type 'theorem]{
 @cases[#:of/count ≡ 5
        #:language esterel/typeset
        #:simple-cases]{
  @#:case[sym]{
   In this case we have @es[(≡ p-pure q-pure)]
   because @es[(≡ q-pure p-pure)]. This
   case follows by induction and by @proof-ref["circ-sym"].}
  @#:case[trans]{
   In this case we have @es[(≡ p-pure q-pure)] there exists
   some @es[r-pure] where @es[(≡ p-pure r-pure)] and
   @es[(≡ r-pure q-pure)]. This case
   case follows induction and by @proof-ref["circ-trans"].}
  @#:case[refl]{
   In this case we have @es[(≡ p-pure q-pure)] because
   @es[(= p-pure q-pure)]. This
   case follows by @proof-ref["circ-refl"].
  }
  @#:case[ctx]{
   @es[(≡ p-pure q-pure)] because
   @es[(= p-pure (in-hole C-pure p-pure_i))],
   @es[(= q-pure (in-hole C-pure q-pure_i))], and
   @es[(≡ p-pure_i q-pure_i)].
   
   This case follows by @proof-ref["soundness-of-ctx"], and induction on
   @es[(≡ p-pure_i q-pure_i)].}
  @#:case[step]{
   In this case we have
   @es[(≡ p-pure q-pure)] because @es[(⇀ p-pure q-pure)].
   This case is given by @proof-ref["Soundness-step"].}}
}


@proof[#:title "Computational Adequacy"
       #:label "comp-ad"
       #:type 'theorem
       #:statement @list{
        For all @es[p-pure], @es[O],
        if @es[(closed p-pure)] and @es[(≃ (of (compile p-pure) SEL) 0)]
        then
        @es/unchecked[(= (eval^esterel O p-pure) (tup θ bool))] if and only if
        @es[(= (eval^circuit O (compile p-pure)) (tup θ bool))]}
       #:interpretation @list{This theorem states that the calculus
        can defined an evaluator which is the same an evaluator
        for Esterel which we take as the ground-truth semantics.}]{
 @sequenced{
  @#:step[value]{

   By @proof-ref["strongly-cannibalizing"]
   and 
   @proof-ref["step-is-v"]
   we the fact that @es[⟶] is a subrelation
   of @es[≡], and the fact that @es[p-pure] is closed,
   we can conclude that
   there exists some @es[(= q (ρ θr GO r-pure))],
   where @es[(≡ p q)],
   such that either @es/unchecked[(L∈ r-pure done)] and
   @es[(complete-with-respect-to θr r-pure)],
   or @es[(blocked-pure θr GO hole r-pure)].
  }
  
  @#:step[bools]{
   @cases[#:of/count @value 2
          #:litteral
          #:no-check
          #:language esterel/typeset]{
    @#:case[(L∈ r-pure done)]{
                         
     By the definition of @es[eval^esterel], it must return
     @es[tt] for the constructiveness of @es[p-pure]. By
     @proof-ref["done-is-constructive"], @es[eval^circuit] must
     do the same.

     By @proof-ref["soundness"],
     both evaluators must
     agree on the value of the signal wires, and thus give back
     the same @es[θ].
     
    }
    @#:case[(blocked-pure θr GO hole r-pure)]{
     The constructiveness of both
     evaluators follows direclty from @es["blocked-is-nc"].
     By @proof-ref["soundness"],
     both evaluators must
     agree on the value of the signal wires, and thus give back
     the same @es[θ]. }
   }
  }
 }
}

@proof[#:title "Consistency of Eval"
       #:label "consistent"
       #:type 'theorem
       #:statement @list{For all @es[p-pure] and  @es[O],
        if @es/unchecked[(= (eval^esterel O p-pure) (tup θ_1 bool_1))]
        and @es/unchecked[(= (eval^esterel O p-pure) (tup θ_2 bool_2))],
        the @es[(= (tup θ_1 bool_1) (tup θ_2 bool_2))].}
       #:interpretation @list{This theorem states that @es[eval^esterel] is
        a function.}]{
                     
 This follows directly from @proof-ref["comp-ad"]. As @proof-ref["comp-ad"]
 states that the relations defined by @es[eval^esterel] and @es[(∘ eval^circuit compile)],
 thus as @es[eval^circuit] and @es[compile] are functions, @es[eval^esterel] must be as well.
 
}