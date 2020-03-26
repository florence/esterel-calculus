#lang scribble/book

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/proof-extras.rkt"
          "lib/misc-figures.rkt"
          "lib/rule-figures.rkt"
          "lib/jf-figures.rkt"
          "lib/cite.rkt"
          (only-in "notations.scrbl")
          (only-in "proofs/proofs.scrbl")
          esterel-calculus/redex/model/shared
          scriblib/figure
          redex/pict
          syntax/parse/define
          esterel-calculus/redex/model/deps
          (for-syntax racket/base)
          pict)


@title[#:style paper-title-style
       #:tag "sec:proofs"]{Proving the calculus correct}


The five properties I promise the Calculus for Esterel would
have are: Syntactic, Local, Consistent, Sound, and Adequate.
This section justifies that the calculus has each of these
properties. This section relies heavily on the background
given in @secref["background-circuits"], as well as the
descriptions of the properties given in @secref["intro"].

@include-section["justification/setup.scrbl"]
@include-section["justification/soundness.scrbl"]
@include-section["justification/adequacy.scrbl"]