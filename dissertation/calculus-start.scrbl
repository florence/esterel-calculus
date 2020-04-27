#lang scribble/book

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/proof-extras.rkt"
          "lib/misc-figures.rkt"
          "lib/rule-figures.rkt"
          "lib/jf-figures.rkt"
          "lib/cite.rkt"
          (only-in "notations.scrbl")
          (only-in "proofs/proofs.scrbl")
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
       #:tag "sec:free-and-pure"]{Loop-free, pure Esterel}

With the background out of the way, this section dives
directly into describing the calculus for Esterel.
Specifically this describes the calculus for single instants of Pure
Esterel without loops. This section relies heavily on the
background given in @secref["background-esterel"] and
@secref["background-calculi"].

@section{The Constructive Calculus}

This section will walk through the rules of the calculus to explain their function.
The calculus is built around the relation @es[⇀], which
defines the notions of reduction for the the equality
relation @es[≡]. These relations work within a single
instance of execution, which will lead the evaluator
@es[eval^esterel] to be an evaluator for a single instant.
Multi-instant evaluation is described in
@secref["sec:calc:future"].

The rules of @es[⇀], broadly, be broken up into three
categories: Administrative reductions which shuffle the term
around to find the next redex; Signal Reductions, which
manipulate and read signal states; and Host language rules
which give Esterel's interaction with the Host language. The
description here is incremental, introducing concepts as it
goes along, and only the administrative and signal rules are
described here. The host language rules are given in
@secref["sec:full:host"]. The complete rules and grammars
can be found in one place in Appendix A.



@subsection{Administrative rules}

To begin, the administrative rules rely on three categories of programs
that represent various ways a program fragment may be in a completed state:
@[centered
  (with-paper-rewriters
   (parameterize ([render-language-nts '(done paused stopped)])
     (render-language esterel-eval)))]
Stopped terms (@es[stopped]) can no longer evaluate and will do
nothing further in future instants. Paused terms (@es[paused]) are
terms which will not reduce further this instant, but will evaluate further in
future instants. Done terms (@es[done]) are stopped or paused. A @es[done]
term is analogous to a value in other languages. A @es[stopped] is analogous
to a primitive value (e.g. a number), in that it is atomic, and contains
no future behaviors. A @es[paused] term is analogous to a @es[λ] term
in the @es[λ]-calculus in that it is a value which is awaiting input, and once
that input is received it can continue reducing. The major difference
between @es[paused] and @es[λ] is that @es[paused] can only receive
its awaited signals in the next instant.


The first two rules deal with sequencing:@(linebreak)
@[render-specific-rules '(seq-done seq-exit)]@(linebreak)
The first rule reduces to the second part of the sequence when the first
part has completed and will not preempt the whole sequence. The second rule
preempts the sequence when the first part reduces to an @es[exit], by discarding
the second part of the @es[seq] and reducing to the @es[exit].

The next rule handles @es[traps]:@(linebreak)
@[render-specific-rules '(trap)]@(linebreak)
This rule reduces when the inner program can reduce no more, via the metafunction:
@[centered (with-paper-rewriters (render-metafunction harp #:contract? #t))]
which will decrement a @es[exit] by one, unless the @es[exit] is bound by this trap,
in which case it reduces to @es[nothing], allowing execution to continue from this point.

The next rules handle @es[par]:@(linebreak)
@[render-specific-rules '(par-swap par-nothing par-1exit par-2exit)]@(linebreak)
The first rule swaps the two branches of a @es[par]. This rule is useful for exposing redexes
to the next three rules.
The second rule allows a @es[par] to reduce to its second branch when it is @es[done]
and the other branch has completed.
Combined with @rule["par-swap"], it means that the program will progress with the behavior
of one branch if the other is @es[nothing].
The last two rules handle @es[exit]s in @es[par]s. In short, an @es[exit] will preempt
a paused term, and two @es[exit]s will abort to the which ever one is bound higher up.

It should be noted that all of the @es[par] administrative reductions only take effect when
both branches have completed. This is because @es[par]s acts akin to a fork/join, synchronizing the results
of both branches, which gives us determinism in that we cannot observe which branch completes first.

Next up is @es[suspend]:@(linebreak)
@[render-specific-rules '(suspend)]@(linebreak) Which just
states that the suspension of a @es[stopped] term is
equivalent to just that term. Because this @es[⇀] only works
within one instant, and @es[suspend] has different behaviors
on initial versus future instants. This is the only rule
that touches @es[suspend]. The rest of @es[suspend]'s
behavior is not handled by these rules, but is rather
handled by the inter-instant translation function
@es[next-instant], which is discussed in
@secref["sec:calc:future"].


@subsection{Signal rules}

The signals rules are where the calculus get subtle.
They must reason about state, which is difficult
to do in a local way. To handle this, we need need to add
three new pieces: Environments, Evaluation Contexts, and
the metafunction @es[Can].

@subsubsection{Environments}

Environments represent state information that is local to a portion of a program.
In full environments look like:
@[centered lang/env]
Local environments @es[ρ] contain two parts: a map @es[θr], and a control variable @es[A].
The information contained in these environments is scoped to the program fragment @es[p].
The map @es[θr] maps signals
that are in scope of the term @es[p] to their status.
The maps that use for local stores are restricted maps, which only
map to a subset of signal statuses.f Other parts of the calculus will use full maps
@es[θ].@note{You
 may notice that these three statuses correspond to wire
 values in Circuits. This is because signals correspond
 exactly to wire in compilation, and this fact will be
 crucial in proving soundness of the calculus.}

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

The control variable @es[A] tracks whether or not control
has reached this point in the program. This control variable
is needed because signal emissions represent what must
happen in the program. However, as discussed in
@secref["back:esterel:cannot"], this is inherently a
non-local property. Therefore we add a new piece to the
environment, @es[A], which will be @es[GO] if control will
reach the portion of the program inside the @es[ρ], or @es[WAIT],
if it might not. In essence this tracks a @es[1] propegating
through the control edges of the causality graphs discussed
in @secref["back:esterel:cannot"].

To understand why this is needed in the setting of the calculus specifically, consider the program in
in @figure-ref["nc-example"]. This
program has a cycle between the test of @es[S1], the test of @es[S2],
and the emit of @es[S1]. This cycle cannot be broken, therefore this program is non-constructive:
evaluation would demand a value for @es[S1] before determining a value for @es[S2], which cannot happen.
However we might try to reason about a fragment of this program locally, ignoring it's context. For example
we might ignore the context:
@[centered
  @es[(signal S1 (present S1 hole nothing))]]
and focus on the fragment
@[centered
  @es[(signal S2
        (seq (emit S2)
             (present S2 nothing (emit S1))))]]
If we live in a world without the control variable @es[A], then we
must assume that control reaches this part of the program. Therefore
we can @es[emit] the @es[S2], allowing the
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
must be reached or not. When @es[A] is @es[GO], this means that the term @italic{must} be executed. If @es[A]
is @es[WAIT] the term may or may not be executed.@note{These control variables are adapted from an as-yet
unpublished microstep semantics for Esterel by Lionel Rieg. His semantics defines an evaluator
for Esterel which tracks execution state via three colors: Red (@es[0]/Cannot), Green (@es[1]/Must), and Gray(@es[⊥]/unknown). My adaptation
makes these colors local, which allows the Red color to be discarded. Green corresponds to @es[GO],
and Grey corresponds to @es[WAIT].}

The calculus itself will never introduce @es[GO]'s, but
rather only propagate them through the program. A @es[GO]
can only safely be introduced by the evaluator---as it knows
the whole program---and, theoretically, when the whole
program is guaranteed to be acyclic. However, the calculus
assumes that @es[GO] is only at the top of the program, and
therefore while a programmer may choose to add @es[GO] to
acyclic programs doing, so is not proven to be sound.

To understand why restricted maps @es[θr] are necessary,
cast your eye back to  @figure-ref["back:lattice"] from @secref["back:esterel:cannot"].
That @italic{must} and @italic{cannot} corner of that diagram
is an nonsensical state. If we used unrestricted maps for environments,
however, the syntax of the language would allow for representing
such program. Consider the program
@centered[@es[(ρ (mtθ+S S1 absent) GO (emit S1))]]
The @es[GO] and @es[(emit S1)] tells us that this program @italic{must}
emit @es[S1]. However the @es[absent] in the environment tells us
that @es[S1] @italic{cannot} be emitted. This is the exact contradiction we wish to avoid.
Therefore the calculus forbids directly recording @es[absent] in the environment.
While such a program should never be reachable from a program without environments,
it makes proofs about the calculus simpler to exclude such programs from
the grammar altogether.
@Secref["calc:can"] explains how @es[absent] is recorded in the calculus.

Note that a term that swapping things around, recording that
something @italic{must} be emitted in a program that
@italic{ cannot} emit it (e.g.
@es[(ρ (mtθ+S S1 present) GO nothing)]) does not contain a
contraction. This is because the @es[1] in the environment
records that at some point in the reduction sequence prior
to the current state @es[S1] must have been emitted.
Therefore it is the case that this program actually states
that @es[S1] must be emitted (and resp. @italic{can} be
emitted). This is a manifestation of the asymmetry
between @italic{must} and @italic{can}.


A small example of how environments work can be seen in the rule:@(linebreak)
@[render-specific-rules '(signal)]@(linebreak)
which transforms a signal into a local environment. The map in this environment
contains only the signal, mapped to @es[unknown], representing that we do not
yet know its value. The control variable is set to @es[WAIT] as we cannot know if this
program fragment will be executed yet or not.


@subsubsection{Evaluation Contexts}

The next set of rules require evaluation contexts. Like the evaluation contexts we saw in @secref["background-calculi"],
these control where evaluation may take place (and therefore where state is valid), however,
in this case the evaluation contexts can decompose non-deterministically because of @es[par]:

@[centered lang/eval]

With these in hand we can now look at the next three rules. Firstly, local environments
may be merged together if they are within an evaluation context of each other:@(linebreak)
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
These @rule["emit"] and @rule["is-present"] rules together describe how the calculus handles
signals that @italic{must} be emitted. The handling of signals that @italic{cannot} be emitted
requires a different mechanism altogether.

@subsubsection[#:tag "calc:can"]{Can} If @es[0] cannot be put intro restricted environments,
how are we to take the else branch? The answer lies the meaning of @es[0]. A signal is @es[0]
only when it has not been emitted (that is, is not @es[1]) and @italic{cannot} be emitted.
Thus to take the else branch we analyze the program for what can be emitted. This is done by the
metafunctions in @figure-ref["Can"] and @figure-ref["Can-rho"].

@figure["Can"
        "Can on pure, loop free terms"
        Can-pict]

@[begin
 (define S (with-paper-rewriters (text "S" (default-style))))
 (define K (with-paper-rewriters (text "K" (default-style))))
 (define sh (with-paper-rewriters (text "sh" (default-style))))]

The first metafunction, @es[Can], computes what might happen
during the execution of a program, given an environment of
signals. The metafunction @es[Can] returns three sets.
The first set
@S is a set
of the signals that might be emitted during execution. The
second set @K is a set of return codes (@es[κ]), which
describe in what ways the in which the program might
terminate. The code @es[0] means the program may reduce to
@es[nothing]. The code @es[1] means the program might pause
(reduce to @es[paused]). A code of @es[(= κ 2)] or greater
means the program might reduce to @es[(exit (- κ 2))]. The
final set @sh is a set of shared variables which may be
written to during execution of the program. This third set
is discussed when the host language portion of the calculus
is introduced in @secref["sec:full:host:can"].

I will note accessing only one of these sets will a
superscript: @es/unchecked[(->S Can)] for the @S set,
@es/unchecked[(->K Can)] for the @K set, and
@es/unchecked[(->sh Can)] for the @sh set.

Note that @es[Can] takes in an map @es[θ] not a
restricted map @es[θr]. This is because while @es[Can] will record
@es[0]s into this map, and it cannot arrive at a
contraction. This because it only temporarily records a signal @es[S] as @es[0] in the map
if @es[S] cannot be emitted, therefore it cannot enter the contradictory corner
of @figure-ref["back:lattice"].

While I will explain this version of @es[Can] here, a much
more detailed explanation can be found in chapters 4 and 5
of @cite/title[compiling-esterel], from which this version
of @es[Can] is adapted.

The first three clauses of @es[Can] handle the return codes
for irreducible terms: @es[nothing] gets @es[0], etc. The @S
and @sh sets are empty for these, as they can neither emit signals
nor write to shared variables.

The next clause, for @es[emit], puts @es[S] in the @S set, and @es[0] in the @K set,
as @es[(emit S)] can reduce to only @es[nothing], and can emit only @es[S].

The next three clauses handle @es[if]. When @es[θ] knows that @es[S] is @es[present],
then @es[Can] will only inspect the @es[p] branch, as the @es[q] branch cannot be reached.
The reverse is true when @es[θ] maps @es[S] to @es[absent]. Otherwise, both branches are analyzed
and, as both branches can happen, their result sets are unioned.

The next clause handles @es[suspend], which just gives the
result of analyzing the body of the @es[suspend]. This is
because @es[suspend] does nothing on the first instant, and
the inter-instant metafunction @es[next-instant] will transform
@es[suspend] into other forms, therefore
no special reasoning is needed.

The next two clauses handle @es[seq]. If @es[0] is not in
the possible return codes of the first part of the @es[seq],
we know that it cannot reduce to @es[nothing], therefore the
@es[q] can never be reached. Therefore in this case @es[Can]
only analyzes @es[p]. If @es[0] is in the possible return
codes of @es[p], @es[Can] analyzes both parts, and unions
the results. However @es[0] is removed from the return codes
of @es[p], as if @es[p] does in fact reduce to @es[nothing] then the return
code will given by only @es[q].

Next is @es[par]. The @S and @sh sets are just the union
of the sets from the recursive calls. The return codes are
give by the set of pairwise @es[max] of each possible return
code of the subterm. This mimics exactly what the
@rule["par-nothing"], @rule["par-1exit"], and
@rule["par-2exit"] rules do.

The next clause handles @es[trap]. Again the @S and @sh sets
are the same as the sets for the subterm. The return codes
are given by the metafunction @es[↓], which does for return
codes what @es[harp] does for terms.

The next two clauses handle @es[signal] forms. If the signal
@es[S] cannot be emitted by the body @es[p], then the term
is re-analyzed with @es[S] set to @es[0], as this refined
information may give a more accurate result of what the term
can do. Otherwise the recursive call is used as is. In both
cases @es[S] is removed from the result set, as its name
may not be unique and thus emissions from within this
@es[signal] form need to be hidden to avoid conflicts with
other signals of the same name.

The clause for @es[ρ] delegates to the @es[Can-θ] metafunction. Like the @es[signal] case, it
removes all of its bound variables from its result.
The @es[Can-θ] function handles the analysis of @es[ρ]
forms. It essentially behaves as if the form was made of
nested @es[signal] forms: for each signal, if the signal is
@es[unknown] and not in the @S set of the recursive call
then the form is re-analyzed with that signal set to
@es[absent]. Otherwise the signal's value remains unchanged.
The primary difference between this and the signal rule is
that the bound variables are not removed from the resulting
@S set---this is handled by @es[Can].

@figure["Can-rho"
        "Can rho"
        Canθ-pict]

We can understand why this is by looking at the rule which
uses @es[Can-θ]:@(linebreak)
@[render-specific-rules '(is-absent)]@(linebreak) This rule
says that we may take the else branch of an @es[if] only when
the signal is bound in an environment in a relative
evaluation context to the conditional, an the signal cannot
be emitted by the program. If the signals in @es[θr] were
removed from the result of @es[Can-θ] this rule would always
fire.


@subsection{The equality relation}

As a calculus should be congruent equality relation. The relation @es[⇀]
generates this relation via its symmetric, transitive, reflexive,
compatible closure, seen in @figure-ref["eql-rel"].

@figure["eql-rel" "The full equality relation" ≡j-pict]

@section[#:tag "calc:eql"]{The evaluator}

The evaluator defined by the calculus is a partial function which
evaluates one instant of execution.
Its signature is similar to that of the circuit evaluator @es[eval^circuit]:
@centered[(with-paper-rewriters (render-metafunction eval^esterel #:only-contract? #t))]
It takes a 
a set of output signals and a program, and gives back a pair
containing a map with the status of each of those signals
and a Boolean which tells us if the program is constructive
or not. The evaluator itself is has two clauses, the first clause
handling constructive programs, and the second clause handling
non-constructive programs:
@centered[(with-paper-rewriters (render-metafunction eval^esterel))]
If a program is @es[≡] to another program which is done (@es[done]),
and that program has an environment which is @italic{complete} with respect to that program,
them, the program is constructive. The @es[complete-with-respect-to] relation hold if
every signal is either set to @es[1], or is set to @es[⊥] and that signal is not in the
result of @es/unchecked[(->S Can-θ)]:
@extract-definition["complete-wrt"]
This completeness winds up meaning that every signal in the environment has a definite value.
From there the value of the signals is extracted using the metafunction @es[restrict],
which gives back a map like @es[θr_2], but with every signal that can be set to @es[0] set to @es[0],
and with the domain restricted to @es[O]:
@extract-definition["restrict"]

The second clause of @es[eval^esterel] recognizes programs
which are non-constructive. This is accomplished with a
special judgment, @es[(blocked-pure θr A E p)], which can be
read as ``In the program context consisting of the state
@es[θr], the control variable @es[A] and the evaluation
context @es[E] the program @es[p] is blocked on some signal
or shared variable''. In this case the program is
non-constructive, and its signal statuses are given by the
same @es[restrict] metafunction. The resulting signal statuses
may, however, contain @es[⊥] in this case.

@subsection{The blocked judgment}

The @es[(blocked-pure θr A E p)] judgment traverses the the
program and checks that at the leaf of each evaluation
context there is either an @es[if] which is blocked on an
signal or an @es[emit] which is awaiting an @es[GO].

The relation is in @figure-ref["calc:eval:blocked:pure"]. The first
case, @rule["if"], checks that, for a conditional, the status
of its signal is @es[unknown], and that that signal is not in the result
of @es/unchecked[(->S Can-θ)] for the whole program. These conditions mean that
the @rule["is-absent"] and @rule["is-present"] rules cannot fire. The second rule @rule["emit-wait"]
says that the program is blocked on an @es[emit] if the control
variable is telling us to @es[WAIT]. Note that both of these
clauses assume that @es[S] is in @es[θr]. We will return to this in
@secref["calc:eval:stuck"].

The remainder of the judgment recurs through the term following the
grammar of evaluation contexts, copying each layer of the context
into the evaluation context on the left of the judgment, so that
the overall program can be reconstructed in the base cases.

The only interesting part here is the handling of @es[par]
which requires three separate clauses. Together these clauses
ensure that at least one branch of the @es[par] is blocked,
and that the other branch is either blocked, or is done
evaluating.

@figure["calc:eval:blocked:pure" "The blocked judgment on pure terms" 
         pure-blocked-pict]

@subsection[#:tag "calc:eval:stuck"]{Open programs}

There are two major cases that make @es[eval^esterel] is a
partial function. One of these involves loops, and we will
return to this in @secref["sec:calc:loop:eval"]. The other
is the case of open programs. If a program has a free
variable is may reach a state where it is not @es[blocked]
or @es[done], but it cannot progress. For example, the
program @es[(ρ · GO (emit S))] can never be equal to a term
which is @es[blocked], because the @es[blocked] judgment
will see that the control variable is not @es[WAIT], and
will therefore determine that @es[emit]s can be run. On the
other hand @es[(emit S)] is not in the grammar of @es[done],
because @es[emit]s are terms which can execute. Therefore
this particular program is stuck. Therefore
@es[eval^esterel] is not defined on such terms.


@section{Correct Binding & Schizophrenia}

 A natural question about the calculus for
someone familiar with the lambda calculus might be ``is
there an @rule["α"] rule?''. Instead of working up to α-equivalence, as is common in the
lambda calculus world, I take a different tact inspired by
Esterel, circuits, and schizophrenia and work up
to what I have called correct binding. The judgment for a program
with correct binding is given in @figure-ref["CBfig"].

@figure["CBfig" "The correct binding judgment" CB-pict]

This judgment tells us that a program which has correct
binding cannot accidentally capture a variable it should not
when it takes a reduction step. To understand this look at
the rule for @es[seq] in @es[CB]. It states that the bound
variables of @es[p] must not overlap with the free variables
of @es[q]. This means that if an environment is lifted out
of @es[p], it cannot capture any variables in @es[q].

This approach explains all the rules of @es[CB] in fact.
For any term, if that term could be part of an evaluation context
or could reduce to a term which could be part of an evaluation context,
then the term that would be in the hole of that context must have
distinct bound variables from any possible adjacent free variables.

Correct binding is preserve by reduction:
@proof-splice["cbpreserved"]
The full proof is given in
@proof-ref["cbpreserved"]. This follows by case analysis
over the rules of @es[⇀]. I should also note that any
program can any be renamed into a program with correct binding
by making all variable names unique. Therefore I work up to
correct binding, that is, I assume that any program used in
the calculus or in my proofs has correct binding.

Using correct binding instead of α-equivalence also explains
the lack of a @rule["gc"] rule, as appears in the state
calculus@~cite[felleisen-hieb]. As the calculus does not
rename variables, but instead constantly replaces instances
of variables in the environment with the new instances,
there is a possible size to every environment. This matches
well with actual Esterel implementations which, absent host
language allocation, execute in a bounded amount of memory.
In addition Correct Binding will be used to explain
how the calculus avoids schizophrenic variables, which is explained
in @secref["sec:calc:loop:cb"].

@include-section["calculus/examples.scrbl"]