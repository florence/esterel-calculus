#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          "../lib/misc-figures.rkt"
          "../lib/rule-figures.rkt"
          "../lib/jf-figures.rkt"
          "../lib/cite.rkt"
          "../notations.scrbl"
          "../lib/proof-rendering.rkt"
          (only-in "../proofs/equations.scrbl")
          (only-in racket/list empty)
          esterel-calculus/redex/model/shared
          scriblib/figure
          redex/pict
          syntax/parse/define
          esterel-calculus/redex/model/deps
          (for-syntax racket/base syntax/parse)
          pict
          racket/stxparam
          racket/math)



@title{Using the calculus, by example}

The calculus is designed to prove equivalences between
program fragments because any two expressions that are
@es[≡e]. This section is designed to give some examples of
how this is done, and some examples which cannot be proved
in the calculus, to give some sense of its limits.

The proofs for the equalities in this section are given in
appendix D. The proves themselves are written in a DSL which
checks them against the equations of the calculus, then
generates the prose in that section.


The first example proof is that adjacent signals can be
swapped:
@proof-splice["swap-sigs"]
The full proof is given
in @proof-ref["swap-sigs"]. This proof mainly relies on the
@rule["merge"] and @rule["signal"] axioms of @es[⇀], as well
as the transitivity and symmetry of the equality relation.

The second proof shows that we can take the else branch of an @es[if] whenever
we can determine the signal cannot be emitted:
@proof-splice["else-branch"]
The full proof is given is @proof-ref["else-branch"].