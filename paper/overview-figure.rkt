#lang at-exp racket
(require "redex-rewrite.rkt"
         "util.rkt"
         redex/reduction-semantics
         redex/pict
         pict
         (only-in slideshow/base para current-main-font current-font-size)
         esterel-calculus/redex/model/eval
         esterel-calculus/redex/model/lset
         (prefix-in S: esterel-calculus/redex/model/reduction)
         (only-in esterel-calculus/redex/test/binding CB)
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/potential-function)
(provide overview-figure)

(define Eval-signature
  (hbl-append (es Eval)
              (words " : ")
              (es p)
              (words " ")
              (es θ)
              (words " ")
              (es →)
              (words " (Setof ")
              (es S)
              (words ")")))

(define (add-comments p . more)
  (parameterize ([current-main-font Linux-Liberterine-name]
                 [current-font-size (get-the-font-size)])
    (vl-append p (indent (apply para #:width 400 more)))))

(define overview-figure
 (with-paper-rewriters
     (vl-append
      8
      @add-comments[Eval-signature]{
 Runs the program for a single instant and returns the emitted signals
}
      @add-comments[(render-metafunction next-instant #:only-contract? #t)]{
 Transforms a fully-reduced program to prepare it for the next instant
}
      @add-comments[(es (⇀ p q))]{
 Our notion of reduction; the primitive computational steps
 of our calculus
}
      @add-comments[(es (≡e () () () p q))]{
 The reflexive, transitive, symmetric, context closure of @es[⇀]
}
      @add-comments[(render-metafunction Can #:only-contract? #t)]{
 Determines the signals an expression can emit
}
      @add-comments[(es (CB p))]{
 A well-formedness condition on programs ensuring that signals and
 variables are well-behaved
 })))