#lang scribble/book

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/cite.rkt"
          (only-in scribble/core style make-style make-part))

@title[#:style paper-title-style]{A Constructive Calculus for Esterel}

@para[#:style (style "abstract" '())]{
                                      
 The language Esterel has found success in many
 safety-critical applications, from aircraft landing
 gear to digital signal processors. Its unique
 combination of powerful control operations,
 deterministic concurrency, and real time
 execution bounds are indispensable
 to programmer in these kinds of safety-critical
 domains. However these features lead to an interesting
 facet of the language, called Constructivity.

 Constructivity is a non-local property of Esterel programs
 which makes defining semantics for the language subtle.
 Existing semantics tend to sacrifice some desirable facet of
 a language semantics to handle this. Many sacrifice
 locality, and only work on whole programs. Some sacrifice
 adequacy, allowing them to describe transformations to
 programs at the cost of being able to actually run programs.
 Still more decide to work in a domain other than Esterel,
 such as circuits, making Constructivity easier to capture,
 but forcing users of these semantics to reason in a domain
 which they are not programming in.

 This dissertation provides the first semantics for Esterel
 which captures all of the above facets, while still describing
 Constructivity.

}

@para[#:style (style "acknowledgements" '())]{

 These acknowledgements can by no means be complete.
 Completing a PhD is a challenging prospect, and so to
 complete them would be to create a list of names akin to
 book 3 of the Illiad, and no one wants that. So here are
 some highlights.

 TODO actually write these

}

@(define (index-section #:title [title "Index"] #:tag [tag #f])
   (make-part #f
              `((part ,(or tag "doc-index")))
              (list title)
              (make-style #f '(unnumbered))
              null
              (list (index-block))
              null))

@table-of-contents[]
@include-section["intro.scrbl"]
@include-section["background/background.scrbl"]
@include-section["calculus-start.scrbl"]
@include-section["proofs.scrbl"]
@include-section["full-kernel.scrbl"]
@include-section["related/related.scrbl"]
@include-section["future/future.scrbl"]
@generate-bibliography[]
@include-section["notations.scrbl"]
@include-section["proofs/proofs.scrbl"]
@include-section["solver.scrbl"]
@include-section["proofs/equations.scrbl"]
@index-section[]