#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          (only-in
           "../lib/circuit-diagrams.rkt"
           emit-pict nothing
           compile-def
           esterel-interface)
          "../lib/proof-extras.rkt"
          (only-in "../proofs/proofs.scrbl")
          (only-in "../notations.scrbl")
          (only-in scribble/manual racket)
          scriblib/figure
          racket/match)

@title[#:style paper-title-style #:tag "just:consistent"]{Justifying Consistency}

Consistency, at it's core, means that a theory cannot
disagree with itself. In the case of programming language semantics
this can be boiled down to a single property: That @es[eval^esterel] is a function.
Or, more formally:

@proof-splice["consistent"]

The full proof is given in the appendices as
@proof-ref["consistent"]. Usually, consistency is proven
using the confluence of the underlying reduction semantics.
However, in this case proving confluence is not necessary:
consistency here follows as a corollary of the soundness and adequacy of
the calculus.