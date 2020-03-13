#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/misc-figures.rkt"
          "../lib/rule-figures.rkt"
          "../lib/cite.rkt"
          esterel-calculus/redex/model/shared
          scriblib/figure
          redex/pict
          syntax/parse/define
          esterel-calculus/redex/model/deps
          (for-syntax racket/base)
          pict)

@(define-simple-macro (code+graph {~alt
 {~optional {~seq #:ignore-start? qq}}
 {~once e}} ...)
   (with-bar (es e) (flow/pict 'e #:ignore-start? (~? qq #t))))


@(define (with-bar p1 p2)
   (hc-append
    p1
    (vline 30 (max (pict-height p1) (pict-height p2)))
    p2))

@title[#:style paper-title-style
       #:tag "sec:calculus"]{A Calculus for Esterel}


@section{Kernel Esterel}

@figure["pure-kernel" "Pure fragment of Kernel Esterel"
        lang/pure]

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
@[centered (with-paper-rewriters (render-metafunction harp #:contract? #t))]
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

The signals rules are where the calculus get's a little tricky.
Essentially reasoning about state, which is difficult to do in a local way.
To handle this, we need need three new pieces: Environments, Evaluation Contexts,
and @es[Can].

@subsubsection{Environments}

Environments represent state information that is local to a portion of the programs.
In full environments look like:

@[centered lang/env]

Local environments @es[(ρ θr A p)] contain maps @es[θr] of signals
that in scope of the term @es[p] to their status.@note{You
 may notice that these three statuses correspond to wire
 values in Circuits. This is because signals correspond
 exactly to wire in compilation, and this fact will be
 crucial in proving soundness of the calculus.}@note{These environments are adapted
from the @citet[felleisen-hieb] state calculus.}
The maps that use for local stores are restricted maps, which only
map to a subset of signal statuses. Other parts of the calculus will use full maps
@es[θ].

Using restricted environments @es[θr] allow us to syntactically eliminate
terms which are incoherent---terms that fall in the @italic{must} and @italic{cannot}
sections of @figure-ref["back:lattice"]. The simplest example of such a term
would be @es[(ρ (mtθ+S S1 absent) GO (emit S1))], which clearly must emit @es[S1],
but has an environment which marks that @es[S1] cannot be emitted. Such incoherence
is prevented by simply not allowing @es[0] to be recorded into the environment. Note
that a term that swaps things around, recording that something must be emitted
but cannot emit it (e.g. @es[(ρ (mtθ+S S1 present) GO nothing)]) does not contain a contraction,
because the @es[1] in the environment records that at some point in the reduction sequence
prior to the current state @es[S1] must be emitted. Therefore it is the case that
this program actually states that @es[S1] must be emitted. This is yet another manifestation
of the asymmetry between @italic{must} and @italic{can}.


@[figure
  "nc-example"
  "A non-constructive program"
  (code+graph
   (signal S1
     (present S1
              (signal S2
                (seq (emit S2)
                     (present S2 nothing (emit S1))))
              nothing)))]

Environments also contain a control state @es[A], which
tracks whether or not control has reached this point in the
program. This control variable is needed because signal
emissions represent what must happen in the program. However
this is inherently a non-local property. This can be seen
through the program in @figure-ref["nc-example"]. This
program has a cycle between the test of @es[S1], the test of @es[S2],
and the emit of @es[S1]. This cycle cannot be broken, therefore this program is non-constructive:
evaluation would demand a value for @es[S1] before determining a value for @es[S2], which cannot happen.
However we might try to reason about a fragment of this program locally, ignoring it's context. For example
we might ignore the context:
@[centered
  @es[(signal S1 (if S1 hole nothing))]]
and focus on the fragment
@[centered
  @es[(signal S2
        (seq (emit S2)
             (present S2 nothing (emit S1))))]]
However when we look at this fragment it looks like we can @es[emit] the @es[S2], allowing the
fragment to reduce to
@[centered
  @es[(signal S2 nothing)]]
which, when plugged back into its context gives us the program in @figure-ref["broken-local"].
But this program no longer has the non-constructive cycle! Therefore this local reasoning was not valid:
we did not know that the @es[(emit S2)] must be reached, so it was not safe to @es[emit] it. 

@[figure
  "broken-local"
  "Breaking the cycle, illegally"
  (code+graph
   (signal S1
     (present S1
              (signal S2 nothing)
              nothing)))]


But when using a calculus we can never assume that we have full knowledge of the program: there may
always been an outer context, meaning we can never know for sure if a term will be reached or not.
To handle this the control variable @es[A] adds local information that tells us if the program term
must be reached or not. When @es[A] is @es[GO], this means that the term will be executed. If @es[A]
is @es[WAIT] the term may or may not be executed.@note{These control variables are adapted from an as-yet
unpublished microstep semantics for Esterel by Lionel Rieg. His semantics defines an evaluator
for Esterel which tracks execution state via three colors: Red (@es[0]/Cannot), Green (@es[1]/Must), and Gray(@es[⊥]/unknown). My adaptation
makes these colors local, which allows the Red color to be discarded. Green corresponds to @es[GO],
and Grey corresponds to @es[WAIT].}

The calculus itself will never introduce @es[GO]'s, but rather only propagate them through the program.
A @es[GO] can only safely be introduce by the evaluator---as it knows the whole program---and, I believe, when
the whole program is guaranteed to be acyclic. My semantics assumes that @es[GO] is only at the top of
the program, and therefore while a programmer may add @es[GO] to acyclic programs doing so is not proven
to be sound.

A small example of how environments work can be seen in the rule:@(linebreak)
@[render-specific-rules '(signal)]@(linebreak)
which transforms a signal into a local environment. The map in this environment
contains only the signal, mapped to @es[unknown], representing that we do not
yet know its value. The control variable is set to @es[WAIT] as we cannot know if this
program fragment will be executed yet or not.


@subsubsection{Evaluation Contexts}

The next set of rules require evaluation contexts. Like evaluation contexts in the lambda calculus,
these control where evaluation may take place (and therefore where state is valid), however,
they in this case our evaluation contexts can decompose non-deterministically because of @es[par]:

@[centered lang/eval]

With these in hand we can now look at the next three rules. Firstly, local environments
may be merged together if they are with an evaluation context of each other:@(linebreak)
@[render-specific-rules '(merge)]@(linebreak)
This merge overwrites bindings in the outer map with the inner one. In addition this merge may
only happen if it would not expose the outer environment to more control information
that it had before. That is, @es[(A->= GO WAIT)]. So the merge will happen if the outer environment has
a @es[GO], or if both environments have a @es[WAIT].

Next we may emit a signal when that signal is in an evaluation context relative to its
binder, and when we know control will reach this point in the program:@(linebreak)
@[render-specific-rules '(emit)]@(linebreak)
Emission is accomplished by updating the environment to map @es[S] to @es[present], and
replacing the emit with @es[nothing].

Once there is a @es[present] in the environment we may reduce to the then branch of a conditional:@(linebreak)
@[render-specific-rules '(is-present)]@(linebreak)

TODO transition

@subsubsection{Can} But, if @es[0] cannot be put intro restricted environments,
how are we to take the else branch? The answer lies the meaning of @es[0]. A signal is @es[0]
only when it has not been emitted (that is, is not @es[1]) and @italic{cannot} be emitted.
Thus to take the else branch we analyze the program for what can be emitted. This is done by the
metafunctions in @figure-ref["Can"] and @figure-ref["Can-rho"].

@figure["Can"
        "Can"
        Can-pict]
@figure["Can-rho"
        "Can rho"
        Canθ-pict]
TODO explain.

With this we may then write the rule:@(linebreak)
@[render-specific-rules '(is-absent)]@(linebreak)

@subsection{State rules}
@[render-specific-rules '(shared set-old set-new)]@(linebreak)
@[render-specific-rules '(var set-var if-true if-false)]@(linebreak)


@section{Auxiliary Judgments}

@subsection[#:tag "calc:eql"]{The equality relation}

@subsection[#:tag "binding"]{Correct Binding}

@subsection{Schizophrenia}

@section{Eval & Future Instants}

@section{Existing Semantics}


