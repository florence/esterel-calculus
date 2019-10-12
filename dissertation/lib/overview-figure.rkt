#lang at-exp racket
(require "redex-rewrite.rkt"
         "util.rkt"
         redex/reduction-semantics
         redex/pict
         pict
         (only-in slideshow/base para current-main-font current-font-size
                  current-line-sep)
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

(define (add-comments p #:width [width 200] . more)
  (parameterize ([current-main-font Linux-Liberterine-name]
                 [current-font-size (get-the-font-size)]
                 [current-line-sep 1])
    (vl-append p (indent (apply para #:width width more)))))

(define part-append 3)

(define overview-figure
 (with-paper-rewriters
    (ht-append
     15
     (vl-append
      part-append
      @add-comments[(es (⇀ p q)) #:width 250]{
 Our notion of reduction; the primitive computational steps
 of our calculus
}
      @add-comments[(render-metafunction Can #:only-contract? #t) #:width 250]{
 Determines the signals an expression can emit
}
      @add-comments[(es (CB p)) #:width 250]{
 A well-formedness condition on programs ensuring that signals and
 variables are well-behaved
}
      )
     (vl-append
      part-append
      @add-comments[(es (≡e () () () p q))]{
 The reflexive, transitive, symmetric, context closure of @es[⇀]
}
      @add-comments[Eval-signature]{
 Runs the program for a single instant and returns the emitted signals
}
      @add-comments[(render-metafunction next-instant #:only-contract? #t)]{
 Prepares a fully-reduced program for the next instant
 }))))
