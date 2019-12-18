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
          esterel-calculus/redex/model/potential-function
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
   such that either @es/unchecked[(L∈ r done)],
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
          #:no-check
          #:language esterel/typeset]{
    @#:case[(L∈ r done)]{}@;{"done-is-constructive"}
    @#:case[(L∈ S (->S (Can-θ (ρ θr GO r) ·)))]{}
   }
  }
 }
}


@proof[#:title "Strongly Canonicalizing"
       #:label "strong-cannibalizing"
       #:statement
       @list{For all @es[p], @es[q],
        if @es[(⟶^r p q)],
        then @es[(> (count p) (count q))].}
       #:interpretation
       @list{As @es[count] only returns
        natural numbers, by this we can conclude that
        eventually all terms will reach a state
        where there can only reduce by @es[⟶^s].}]{
}

@include-section["adequacy/positive.scrbl"]
@include-section["adequacy/negative.scrbl"]