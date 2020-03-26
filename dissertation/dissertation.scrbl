#lang scribble/book

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/cite.rkt")

@title[#:style paper-title-style]{A Calculus for Esterel}

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