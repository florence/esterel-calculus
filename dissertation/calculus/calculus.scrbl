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


TODO introduction

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

Stopped terms (@es[stopped]) can no longer evaluate and will do
nothing further in future instants. Paused terms (@es[paused]) are
terms which will not reduce further this instant, but will evaluate further in
future instants. Done terms (@es[done]) are stopped or paused.

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

Next up is @es[suspend]:@(linebreak)
@[render-specific-rules '(suspend)]@(linebreak)
Which just states that the suspension of a @es[stopped] term is equivalent to just that
term. Because this @es[⇀] only works within one instant, and @es[suspend]
has different behaviors on initial versus future instants, this is the only rule
that touches @es[suspend]. The rest of @es[suspend]'s behavior will be handled by the inter-instant
translation function @es[next-instant].



The final administrative rules handle loops. However to handle loops
we must add a new form to Kernel Esterel:
@centered[lang/loop]
This new form, @es[loop^stop] represents a loop which has been unrolled once.
To understand its usage, the loop rules are:@(linebreak)
@[render-specific-rules '(loop loop^stop-exit)]@(linebreak)
The first rule, @rule["loop"] expands a
@es[loop] into a @es[loop^stop]. This @es[(loop^stop p q)]
is essentially equivalent to @es[(seq p (loop p))]---that
is, it represent one unrolling of a loop---however, unlike
@es[seq], the second part is inaccessible: if @es[p] reduces
to @es[nothing], the loop cannot restart, instead the
program gets stuck. This is to handle instantaneous loops,
which are an error in Esterel. The second loop rule,
@rule["loop^stop-exit"], is analagous to @rule["seq-exit"],
aborting the loop if it @es[exit]s.

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
written to during execution of the program.

I will note accessing only one of these sets will a
superscript: @es/unchecked[(->S Can)] for the @S set,
@es/unchecked[(->K Can)] for the @K set, and
@es/unchecked[(->sh Can)] for the @sh set.

Note that @es[Can] takes in an map @es[θ] not a
restricted map @es[θr]. This is because @es[Can] will record
@es[0]s into this map, and it cannot arrive at a
contraction. This because it only records a signal @es[S] as @es[0] in the map
if @es[S] cannot be emitted, therefore it cannot enter the contradictory corner
of @figure-ref["back:lattice"].

While I will explain this version of @es[Can] here, a much
more detailed explaination can be found in chapters 4 and 5
of @cite/title[compiling-esterel].

the first three clauses of @es[Can] handle the return codes
for irreducible terms: @es[nothing] gets @es[0], etc. The @S
and @sh sets are empty for these, as they can neither emit signals
nor write to shared variables.

The next clause, for @es[emit], puts @es[S] in the @S set, and @es[0] in the @K set,
as @es[(emit S)] can reduce to  only @es[nothing], and emit only @es[S].

The next three clauses handles @es[if]. When @es[θ] knows that @es[S] is @es[present],
then @es[Can] will only inspect the @es[p] branch, as the @es[q] branch cannot be reached.
The reverse is true when @es[θ] maps @es[S] to @es[absent]. Otherwise, both branches are analyzed
and, as both branches can happen, their result sets are unioned.

The next clause handles @es[suspend], which just gives the
result of analyzing the body of the @es[suspend]. This is
because @es[suspend] does nothing on the first instant, and
our calculus will transform it into a @es[if] on future instants, therefore
no special reasoning is needed.

The next two clauses handle @es[seq]. If @es[0] is not in
the possible return codes of the first part of the @es[seq],
we know that it cannot reduce to @es[nothing], therefore the
@es[q] can never be reached. Therefore in this case @es[Can]
only analyzes @es[p]. If @es[0] is in the possible return
codes of @es[p], @es[Can] analyzes both parts, and unions
the results. However @es[0] is removed from the return codes
of @es[p], as if @es[p] reduces to nothing then the return
code will given by only @es[q].

The next two clauses handle loops, which just behave as their bodies.
In the case of @es[loop^stop] the right hand side, which is the loops origional body,
is not analyzed as it an never be reached.

Next is @es[par]. The @S and @sh sets are just the union
of the sets from the recursive calls. The return codes are
give by the set of pairwise @es[max] of each possible return
code of the subterm. This mimics exactly what the
@rule["par-nothing"], @rule["par-1exit"], and
@es["par-2exit"] rules do.

The next clause handles @es[trap]. Again the @S and @sh sets
are the same as the sets for the subterm. The return codes
are given by the metafunction @es[↓], which does for return
codes what @es[harp] does for terms.

The next two clauses handle @es[signal] forms. If the signal
@es[S] cannot be emitted by the body @es[p], then the term
is re-analyzed with @es[S] set to @es[0], as this refined
information may give a more accurate result of what the term
can do. Otherwise the recursive call is used as is. In both
cases @es[S] is removed from the result set, as it's name
may not be unique and thus emissions from within this
@es[signal] form need to be hidden to avoid conflicts with
other signals of the same name.

The clause for @es[ρ] delegates to the @es[Can-θ] function,
which will be explained later. Like the @es[signal] case, it
removes all of its bound variables from its result.

The last few clauses handled state and host language
expressions. The analysis of the shared from is like that of
the @es[signal] form, except that there is no special case
for when the shared variable cannot be written to. Because
Esterel does not make control flow decisions based on the
writability of shared variable, there is not need for the
extra step. Writing to a shared variable behaves akin to
emitting a signal: the return code is @es[0] and the variable
is added to the @sh set.

The last three forms handle sequential variables. No special
analysis is done for these forms as Esterel does not think
them into its concurrency mechanism.


@figure["Can-rho"
        "Can rho"
        Canθ-pict]

The @es[Can-θ] function handles the analysis of @es[ρ]
forms. It essentially behaves as if the form was made of
nested @es[signal] forms: for each signal, if the signal is
@es[unknown] and not in the @S set of the recursive call
then the form is re-analyzed with that signal set to
@es[absent]. Otherwise the signal's value remains unchanged.
The primary difference between this and the signal rule is
that the bound variables are not removed from the resulting
@S set---this is handled by @es[Can].

We can understand why this is by looking at the rule which
uses @es[Can-θ]:@(linebreak)
@[render-specific-rules '(is-absent)]@(linebreak) This rule
says that we may take the else branch of an @es[if], when
the signal is bound in an environment in a relative
evaluation context to the conditional, an the signal cannot
be emitted by the program. If the signals in @es[θr] were
removed from the result of @es[Can-θ] this rule would always
fire.

@subsection{Host language rules}

TODO extend θ to handle sh and x

@[render-specific-rules '(shared set-old set-new)]@(linebreak)



@[render-specific-rules '(var set-var)]@(linebreak)
@[render-specific-rules '(if-true if-false)]@(linebreak)

@section{The full calculus}

@section[#:tag "calc:eql"]{The evaluator}

The evaluator defined by the calculus is a partial function which
evaluates one instant of execution.
Its signature is similar to that of the circuit evaluator @es[esterel^circuit]:
@centered[(with-paper-rewriters (render-metafunction eval^esterel #:only-contract? #t))]
It takes a 
a set of output signals and a program, and gives back a pair
containing a map with the status of each of those signals
and a Boolean which tells us if the program is constructive
or not. The evaluator itself is has two clauses:
@centered[(with-paper-rewriters (render-metafunction eval^esterel))]

The first clause handling constructive programs, and the second clause handling
non-constructive programs. If a program is @es[≡] to another program which is done (@es[done]),
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

@subsection{The values of shared variables}

@subsection{The blocked judgment}

The @es[(blocked-pure θr A E p)] judgment traverses the the
program and checks that at the leaf of each evaluation
context there is either a @es[if] which is blocked on a
signal, a host language expression which is blocked on a
shared variable, or an @es[emit] or @es[<=] which cannot
execute because of the current control variable.

This is clearest to see in the cases which handle Pure Esterel
programs, seen in @figure-ref["calc:eval:blocked:pure"]. The first
case, @rule["if"], checks that, for a conditional, the status
of its signal is @es[unknown], and that that signal is not in the result
of @es/unchecked[(->S Can-θ)] for the whole program. These conditions mean that
the @rule["is-absent"] cannot fire. The second rule @rule["emit-wait"]
says that the program is blocked on an @es[emit] if the control
variable is telling us to @es[WAIT]. Note that both of these
clauses assume that @es[S] is in @es[θr]. We will return to this in
@secref["calc:eval:stuck"].

The remainder of the judgment recurs through the term following the
grammar of evaluation contexts, copying each layer of the context
into the evaluation context on the left of the judgment, so that
the overall program can be reconstructed in the base cases.

The only interesting part here is the handling of @es[par]
which requires three separate clause. Together these clauses
ensure that at least one branch of the @es[par] is blocked,
and that the other branch is either blocked, or is done
evaluating.

@figure["calc:eval:blocked:pure" "The blocked judgment on pure terms" 
         pure-blocked-pict]

The handling of forms that refer to the host language, seen
in @figure-ref["calc:eval:blocked:host"]. They are all base
cases, an are either blocked because a write to a shared
variable may not be performed due to the control variable
(@rule["set-shared-wait"]), or because a host language
expression is blocked. The blocked judgment for a host
language expression (@figure-ref["calc:eval:blocked:e"])
says that the expression may not be evaluated if at least
one of the shared variables that the expression references
might still be written to by the full program.

@figure["calc:eval:blocked:host" "The blocked judgment on terms using the host language" 
         blocked-pict]
@figure["calc:eval:blocked:e" "The blocked judgment host language expressions" 
         blocked-e-pict]

@subsection[#:tag "calc:eval:stuck"]{Open programs and instantaneous loops}
TODO Loops

@subsection{Future Instants}

While both the calculus and the evaluator only handle single
instants, we can still describe multiple instants. This is
done via the inter-instant transition metafunction
@es[next-instant]. This relies on the notion of a complete
term:
@centered[[with-paper-rewriters (render-language esterel-eval #:nts '(complete*))]]
which is a term which is either constructive or @es[done].
Such a term is either a program or a fragment of a program
which has finished evaluating for the current instant. The
@es[next-instant] metafunction turns such a term into a term
which will begin execution at the start of the next instant.
The function is defined in @figure-ref["calc:eval:next"].

@figure["calc:eval:next" "The inter-instant transition function" @extract-definition["next-instant"]]

This function walks down the structure of the program
updating it so that it will unpause, if possible. The first
clause uses the metafunction @es[reset-θ], which takes an
environment and sets the status of every signal to
@es[unknown], and the status of every shared variable to
@es[old]. The second clause replaces a @es[pause] with a
@es[nothing], causing execution to resume from that point.

All but two of the remaining clauses simply recur down the
structure of evaluation contexts. The exceptions are
@es[loop^stop] and @es[suspend]. @es[loop^stop] is replaced
by the traditional unfolding of a loop, because in the next
instant the body of the loop that was executing is allowed
to terming, restarting the loop.

The @es[suspend] transformation is more complex. We want a
term which entered a @es[suspend] to pause in that suspend
if the given signal is @es[present] in the next instant.
Therefore we transform an @es[suspend] to do exactly that:
if the signal is @es[present] then @es[pause], otherwise do
nothing and resume executing the loop body.

@section{Correct Binding & Schizophrenia}



