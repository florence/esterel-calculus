#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style]{Core Theorems}

This section contains the core proofs to justify soundness of the calculus
with respect to the compilation function. The core theorem @proof-ref["Soundness"],
however the most informative theorem is @proof-ref["Soundness-step"].

@proof[#:label "Soundness"
       #:title "Soundness"
       #:statement
       @list{For all @es[p] and @es[q], @es[(CB p)] and @es[(≡ p q)] implies that
        @es[(≃ (compile p) (compile q))]}
       #:interpretation "is it really?"
       #:type 'theorem]{
 TODO
}


@proof[#:label "Soundness-step"
       #:title "Soundness of Step"
       #:statement
       @list{For all @es[p] and @es[q], @es[(CB p)] and @es[(⇀ p q)] implies that
        @es[(≃ (compile p) (compile q))]}
       #:interpretation "is it really?"
       #:type 'theorem]{
 next we do
 @cases[#:of/unchecked @list{derivation of @es[(⇀ p q)]}
        #:language esterel/typeset
        @#:case["TODO"]{TODO}]
}

TODO prove that ≃ is a equivalence relation