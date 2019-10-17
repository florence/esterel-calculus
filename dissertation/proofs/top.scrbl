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
with respect to the compilation function. The core theorem @proof-ref["FullyAbstract"],
however the most informative theorem is @proof-ref["FullStep"].

@proof[#:label "FullyAbstract"
       #:title "Fully Abstract Compilation"
       #:statement
       @list{For all @es[p] and @es[q], @es[(CB p)] and @es[(≡ p q)] implies that
        @es[(≃ (compile p) (compile q))]}
       #:interpretation "is it really?"
       #:type 'theorem]{
 TODO
}


@proof[#:label "FullStep"
       #:title "Fully Abstract Compilation of Step"
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
