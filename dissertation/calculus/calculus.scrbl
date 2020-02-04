#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/misc-figures.rkt"
          "../lib/rule-figures.rkt"
          esterel-calculus/redex/model/shared
          scriblib/figure
          redex/pict)

@title[#:style paper-title-style
       #:tag "sec:calculus"]{A Calculus for Esterel}


@section{Kernel Esterel}

@figure["pure-kernel" "Pure fragment of Kernel Esterel"
        lang/pure]

@subsection{Expressiveness of Kernel vs Full}



@section{The Calculus}

This section will walk through the rules of the calculus to explain their function.
The rules can, broadly, be broken up into three categories: Administrative reduction which
shuffle the term around to find the next redex;
Signal Reductions, which manipulate and read signal states; and State rules which give Esterel's interaction with the
Host language.

@subsection{Administrative rules}

To begin, the administrative rules rely on three categories of programs
that represent various ways a program fragment may be in a completed state:

@[centered
  (with-paper-rewriters
   (parameterize ([render-language-nts '(done paused stopped)])
     (render-language esterel-eval)))]

Terms which are @es[stopped] can no longer evaluate and will do
nothing further in future instants. Paused terms @es[paused] are
terms which will not reduce further this instant, but will evaluate further in
future instants. Terms which are @es[done] are stopped or paused.

The first two rules deal with sequencing:@(linebreak)
@[render-specific-rules '(seq-done seq-exit)]@(linebreak)
The first rule reduces to the second part of the sequence when the first
part has completed and will not preempt the whole sequence. The second rule
preempts the sequence when the first part reduces to an @es[exit].

The next rule handles @es[traps]:@(linebreak)
@[render-specific-rules '(trap)]@(linebreak)
This rule reduces when the inner program can reduce no more, via the metafunction:
@[centered @es[(with-paper-rewriters (render-metafunction harp #:contract? #t))]]
which will decrement a @es[exit] by one, unless the @es[exit] is bound by this trap,
in which case it reduces to @es[nothing], allowing execution to continue from this point.

The next rules handle @es[par]:@(linebreak)
@[render-specific-rules '(par-swap par-nothing par-1exit par-2exit)]@(linebreak)
The first rule swaps the two branches of an @es[par]. This rule is useful for exposing redexes
to the next three rules.

The second rule allows an @es[par] to reduce to its second branch when the first is @es[done].
Combined with @rule["par-swap"], it means that the program will progress with the behavior
of one branch if the other is @es[nothing].

The last two rules handle @es[exit]s in @es[par]s. In short, an @es[exit] will preempt
a paused term, and two @es[exit]s will abort to the which ever one is bound higher up.

It should be noted that all of the @es[par] administrative reductions only take effect when
both branches have completed. This is because @es[par]s act a join points, synchronizing the results
of both branches, and giving us determinism.

Next us is @es[suspend]:@(linebreak)
@[render-specific-rules '(suspend)]@(linebreak)
Which just states that the suspension of a @es[stopped] term is equivalent to just that
term. Because this @es[⇀] only works within one instant, and @es[suspend]
has different behaviors on initial versus future instants, this is the only rule
that touches @es[suspend]. The rest of @es[suspend]'s behavior will be handled by the inter-instant
translation function @es[next-instant].

The final administrative rules handle loops:@(linebreak)
@[render-specific-rules '(loop loop^stop-exit)]@(linebreak)
TODO


@subsection{Signal rules}

Evaluation Contexts, Environments, GO, Can
@[render-specific-rules '(signal)]
@[render-specific-rules '(emit)]
@[render-specific-rules '(is-present)]
@[render-specific-rules '(is-absent)]

@subsection{State rules}
@[render-specific-rules '(shared set-old set-new)]
@[render-specific-rules '(var set-var if-true if-false)]


@section{Auxiliary Judgments}

@subsection{Schizophrenia}

@section{Eval & Future Instants}

@section{Existing Semantics}


