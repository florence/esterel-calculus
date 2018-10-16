#lang scribble/acmart @acmsmall @review
@(require
          "cite.rkt"
          "util.rkt"
          "agda-fact.rkt")


@title[#:style paper-title-style]{A Calculus for Esterel}
@subtitle{@subtitle-font-adjust{“If can, can. If no can, no can.”  —Hawaiian pidgin proverb}}
@(define (ath email name)
   @author[#:affiliation (affiliation #:institution "Northwestern University")
           #:email (format "~a@eecs.northwestern.edu" email)]{@name})
@ath["spencer.florence"]{Spencer P. Florence}
@ath["shu-hung.you"]{Shu-Hung You}
@ath["jesse"]{Jesse A. Tov}
@ath["robby"]{Robert Bruce Findler}
 
@abstract{
          
 The language Esterel has found success in many
 safety-critical applications, such as fly-by-wire systems
 and nuclear power plant control software. Its imperative
 style is natural to programmers building such systems and
 its precise semantics makes it work well for reasoning about
 programs.

 Existing semantics of Esterel generally fall into two
 categories: translation to Boolean circuits, or operational
 semantics that give a procedure for running a whole program.
 In contrast, equational theories enable reasoning about
 program behavior via equational rewrites at the source
 level. Such theories form the basis for proofs of
 transformations inside compilers or for program refactorings,
 and defining program evaluation syntactically.

 This paper presents the first such equational calculus for Esterel.
 It also illustrates the calculus’s usefulness with a series of
 example equivalences and discuss how it enabled us to find bugs
 in Esterel implementations.
}

@include-section["intro.scrbl"]
@include-section["sense-of-esterel.scrbl"]
@include-section["the-calculus.scrbl"]
@include-section["constructiveness.scrbl"]
@include-section["examples.scrbl"]
@include-section["testing.scrbl"]
@include-section["standard-reduction.scrbl"]
@include-section["related.scrbl"]

@(generate-bibliography)

@(unless (getenv "SKIPAGDA") (check-the-examples))
