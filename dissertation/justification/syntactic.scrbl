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

@title[#:style paper-title-style #:tag "just:syntactic"]{Justifying Syntactic}

The calculus uses the syntax of Kernel Esterel with two additions:
the @es[loop^stop] and @es[ρ] forms.

The @es[loop^stop] form is necessary for handling
instantaneous loops dynamically: an instantaneous loops result
in a stuck program. In addition this form is for needed for @es[Can],
which should not analyze the body of a loop which cannot be
reached, information which is tracked by @es[loop^stop].@note{
 A similar form of loop annotations is used by the COS, which
 marks loops as @es[STOP] or @es[GO], which tracks if the
 loop may restart or not.}

The @es[ρ] form is necessary to enable local reasoning about
signal state. The @es[θ] portion of the environment exists
as a convenience: it can be reduced to an empty environment,
essentially removing it, by running the @rule["merge"],
@rule["signal"], and @rule["emit"] rules backwards. The
@es[A] part cannot be removed when @es[(= A GO)]. This is
because @es[GO] represents information external to the term
that the calculus cannot know without having access to the
entire program.