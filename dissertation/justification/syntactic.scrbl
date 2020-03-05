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

One could argue that the Calculus is not syntactic, in that it
does not literally talk about the syntax of the programs one writes
in Full Esterel. However I would argue that it is ``syntactic enough'',
which is to say it is purely syntactic except in a few places where
something new has been added by necessity.

The first place it steps outside the syntax of normal
Esterel is in adding @es[GO].@note{Not that environments
 that contain @es[WAIT] can be completely removed by running
 the @rule["emit"] and @rule["signal"] rules backwards,
 therefore they will never show up at the "end" of a chain of
 reasoning.} The calculus needs @es[GO] to be sound and
adequate because it needs to localize the notion of whether
or on control reaches a particular point. So while this is a
minor deviation from the syntax of normal Esterel, it is
necessary@note{In fact, I would argue that the @es[GO] is
 the novel element I have added it make a calculus which is
 sound @italic{and} adequate in the first place.} and does
not stray to far from the syntax of programs.

The same can be said of @es[loop^stop]: while it is not part
of the original Esterel syntax, it is necessary to reason about programs
which have not been proven to contain instantaneous loops. In essence
@es[loop^stop] lets us track potential instantaneous loop errors
my adding a new form. As this is a minor, and necessary, addition
I do not find that it detracts from the overall syntacticness of
the calculus.

TODO How to talk about full esterel and missing features in the context