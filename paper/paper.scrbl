#lang scribble/acmart @acmsmall @screen
@(require
          (only-in scribble/core element style)
          "cite.rkt"
          "util.rkt"
          "agda-fact.rkt")


@title[#:style paper-title-style]{A Calculus for Esterel}
@subtitle{@subtitle-font-adjust{“If can, can. If no can, no can.”  —Hawaiian pidgin proverb}}
@(define (ath email name #:email-style [email-style '()])
   (define address
     (element
      (style #f email-style)
      (format "~a@eecs.northwestern.edu" email)))
   @author[#:affiliation (affiliation #:institution "Northwestern University"
                                      #:country "U.S.A.")
           #:email address]{@name})
@ath["spencer.florence"]{Spencer P. Florence}
@ath["shu-hung.you" #:email-style '(exact-chars)]{Shu-Hung You}
@ath["jesse"]{Jesse A. Tov}
@ath["robby"]{Robert Bruce Findler}

@acmPrice{}
@acmDOI{10.1145/3290374}
@acmYear{2019}
@acmJournal{PACMPL}
@acmVolume{3}
@acmNumber{POPL}
@acmArticle{61}
@acmMonth{1}
 
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

@; The blank lines are necessary
@CCSXML|{

<ccs2012>
<concept>
<concept_id>10003752.10010124.10010131.10010134</concept_id>
<concept_desc>Theory of computation~Operational semantics</concept_desc>
<concept_significance>300</concept_significance>
</concept>
</ccs2012>

}|
@ccsdesc[#:number 300]{Theory of computation~Operational semantics}
@keywords{Esterel, Synchronous Reactive Programming, Semantics}

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
