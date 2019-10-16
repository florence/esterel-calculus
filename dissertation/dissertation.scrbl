#lang scribble/book

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/cite.rkt")

@title[#:style paper-title-style]{A Calculus for Esterel}


@include-section["intro.scrbl"]
@include-section["notations.scrbl"]
@include-section["proofs/proofs.scrbl"]
@generate-bibliography[]