#lang scribble/book

@[require "lib/util.rkt"]

@title[#:style paper-title-style #:tag "just"]{Justifying the Calculus}

The five properties I promise the Calculus for Esterel would have are:
Syntactic, Local, Consistent, Sound, and Adequate. This section justifies that
the calculus has each of these properties.


@include-section["justification/syntactic.scrbl"]
@include-section["justification/local.scrbl"]
@include-section["justification/consistent.scrbl"]
@include-section["justification/setup.scrbl"]
@include-section["justification/soundness.scrbl"]
@include-section["justification/adequacy.scrbl"]
@;@include-section["justification/together.scrbl"]