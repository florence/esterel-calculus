#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          redex/pict
          pict
          (except-in esterel-calculus/redex/model/shared FV FV/e θ-get-S)
          esterel-calculus/redex/test/binding
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/count
          esterel-calculus/redex/model/potential-function
          esterel-calculus/redex/model/count
          (only-in esterel-calculus/redex/model/reduction
                   blocked-pure)
          (except-in scribble-abbrevs/latex definition))


@title[#:style paper-title-style]{Adequacy}

The goal of this section is to prove computational adequacy of the calculus
with respect to the circuit translation. That is:

@proof[#:title "Computational Adequacy"
       #:label "comp-ad"
       #:statement @list{
        For all @es[p], @es[O],
        if @es[(closed p)]
        then
        @es[(= (eval^esterel O p) (tup θ bool))] if and only if
        @es[(= (eval^circuit O (compile p)) (tup θ bool))]}]{
 @sequenced{
  @#:step[value]{

   By @proof-ref["strongly-cannibalizing"]
   and 
   @proof-ref["step-is-v"]
   we the fact that @es[⟶] is a subrelation
   of @es[≡], and the fact that @es[p] is closed,
   we can conclude that
   there exists some @es[(= q (ρ θr GO r))]
   such that either @es/unchecked[(L∈ r done)] and
   @es[(complete-with-respect-to θr r)],
   or @es[(blocked-pure θr GO hole r)].
  }
   
  @#:step[unknown]{
   By @proof-ref["blocked-implies-can-rho"],
   if we are in the case where
   @es[(blocked-pure θr GO hole r)],
   there there exists some @es[S_u] such that
   @es[(L∈ S (->S (Can-θ (ρ θr GO r) ·)))].
  }
  
  @#:step[bools]{
   @cases[#:of/count @value 2
          #:litteral
          #:no-check
          #:language esterel/typeset]{
    @#:case[(L∈ r done)]{
                         
     By the definition of @es[eval^esterel], it must return
     @es[tt] for the constructiveness of @es[p]. By
     @proof-ref["done-is-constructive"], @es[eval^circuit] must
     do the same.

     By the definitino of
     @es[(complete-with-respect-to θr r)], all signals wires must
     be @es[present] or @es[absent]. By @proof-ref["Soundness"],
     both evaluators must
     agree on the value of the signal wires, and thus give back
     the same @es[θ].
     
    }
    @#:case[(blocked-pure θr GO hole r)]{}
   }
  }
 }
}


@proof[#:title "Strongly Canonicalizing"
       #:label "strongly-cannibalizing"
       #:statement
       @list{For all @es[p], @es[q],
        if @es[(⟶^r p q)],
        then @es[(> (count p) (count q))].}
       #:interpretation
       @list{As @es[count] only returns
        natural numbers, by this we can conclude that
        eventually all terms will reach a state
        where there can only reduce by @es[⟶^s].}]{
 @cases[#:of/count ⟶^r 2
        #:induction
        #:language esterel/typeset
        #:simple-cases]{
                                    
  @#:case[(⇀^r p-pure q-pure)]{
   This case is given by @proof-ref["cannibalize-compatible-closure"]. }
  @#:case[(⟶^r (in-hole C p-pure_i) (in-hole C q-pure_i))]{
                  
   In this case we have @es[(⟶^r p-pure_i q-pure_i)]. By induction @es[(> (count p-pure_i) (count q-pure_i))].
   Thus by  @proof-ref["cannibalize-compatible-closure"]
   we can conclude that @es[(> (count (in-hole C p-pure_i)) (count (in-hole C q-pure_i)))].
                        
  }
 }
}

@proof[#:title "Strongly Canonicalizing on Compatible Closure"
       #:label "cannibalize-compatible-closure"
       #:statement @list{For all @es[C-pure], @es[p-pure], @es[q-pure],
        if @es[(> (count p-pure) (count q-pure))] then
        @es[(> (count (in-hole C-pure p-pure)) (count (in-hole C-pure q-pure)))]}]{
                                                               
 This follows by a trivial induction over @es[C-pure], as
 each case of @es[(count p)] only addes constants to the
 @es[count] of the subterms.
  
}

@proof[#:title "Strongly Canonicalizing on single step"
       #:label "cannibalize-step"
       #:statement @list{For all @es[p], @es[q],
        if @es[(⇀^r p q)]
        then @es[(> (count p) (count q))].}]{
}

@include-section["adequacy/positive.scrbl"]
@include-section["adequacy/negative.scrbl"]