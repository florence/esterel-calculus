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

Justifying that the calculus allows for local reasoning is
not difficult. The relation @es[≡] contains a context rule
which states that the the rules of the calculus apply in any
program context. I would argue that this is the definition
of locality in terms of calculi.