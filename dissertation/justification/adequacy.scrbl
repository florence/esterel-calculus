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

@title[#:style paper-title-style #:tag "just:adequacy"]{Justifying Adequacy}

@proof-splice["comp-ad"]

@section[#:tag "just:adq:sketches"]{proof sketches}

@section[#:tag "just:adequacy-and-consistency"]{Adequacy and Consistency}.
