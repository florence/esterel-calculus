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

@title[#:style paper-title-style #:tag "just:local"]{Justifying Local}

Intuitively, the notion of locality the calculus enables
reasoning anywhere in a program, even when the full program
is not known. The definition of the @es[≡] relation is
closed under program contexts, which meets the letter of
this intuition. Some rules, like @rule["emit"] and
@rule["is-present"], require some information about their
external context, but this is limited to the scope of the
variable they are reasoning about. If the binder of that
signal is visible, the rules will still apply in any outer
context.