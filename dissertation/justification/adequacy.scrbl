#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          "../lib/proof-extras.rkt"
          (only-in "../proofs/proofs.scrbl")
          (only-in "../notations.scrbl")
          (only-in scribble/manual racket)
          scriblib/figure
          racket/match)

@title[#:style paper-title-style #:tag "just:adequacy"]{Justifying Adequacy}

Adequacy is the statement that a calculus can define an evaluator for
it's language. In this case, we want Computation Adequacy, which is the statement
that an evaluator defined by the calculus is equivalent to the evaluator
for the ground-truth semantics:

@proof-splice["comp-ad"]

The full proof can be found at @proof-ref["comp-ad"]. The first premise of this theorem
requires that the program be closed, as the evaluator is only really meant to work on full programs.
However closed here is slightly different from the usual definition of close, because it restricts
programs to those which will also generate closed circuits. Which is to say:

@extract-definition["closed"]

TODO explain this.

The next premise is the usual statement that we are only observing the first instant of execution.

The final clause states that the output signals and constructivity of the two 

@section[#:tag "just:adq:sketches"]{proof sketches}

@section[#:tag "just:adequacy-and-consistency"]{Adequacy and Consistency}
