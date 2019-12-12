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
        @es[(= (eval^esterel O p) R)] if and only if
        @es[(= (eval^circuit O (compile p)) R)]}]{
}


@include-section["adequacy/positive.scrbl"]
@include-section["adequacy/negative.scrbl"]