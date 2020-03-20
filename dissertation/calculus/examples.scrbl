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
The full proof is given in @proof-ref["else-branch"].


The next proof demonstrates some of the weaknesses of the calculus. Specifically, in order
to lift a signal out of an evaluation context an out environment is needed:
@proof-splice["lift-signals"]
The full proof is given in @proof-ref["lift-signals"]. This is because
the only rule that allows for moving environments around is the @rule["merge"]
rule, which requires two environments. This however, could be
fixed by adding the axiom @es[(≡ p (ρ · WAIT p))]. Such an axiom should
be easy to prove sound, as will be seen in @secref["just:sound:compiler"],
because the compilation of @es[p] and @es[(ρ · WAIT p)] should be identical.

Next, we another weakness in the calculus. The next theorem should be true,
but cannot be proven in the calculus:
@proof[#:label "unprovable-lifting"
       #:title "Lift Signal Emission (Unprovable)"
       #:no-proof #t
       #:type 'theorem
       #:statement
       @list{For all @es[E], @es[S],
        @es[(≃^esterel (in-hole E (emit S)) (par (emit S) (in-hole E nothing)))]
        }]
In fact it cannot prove even this weaker statement:
@proof[#:label "unprovable-lifting2"
       #:title "Lift Signal Emission, with Binder (Unprovable)"
       #:type 'theorem
       #:no-proof #t
       #:statement @list{
        For all @es[E], @es[S],
        @es[(≃^esterel (signal S (in-hole E (emit S))) (signal S (par (emit S) (in-hole E nothing))))]
        }]
This is because in order to lift up an @es[emit] we must run the @es[emit], putting a @es[present]
in an environment, then using @rule["sym"] run the @es[emit] backwards to place it elsewhere. However
this can only be done if the environment has a @es[GO], which the calculus cannot insert. Possible solutions
to this, to strengthen the calculus, are discussed in @secref["future:remove"].