#lang scribble/base
@(require "misc-figures.rkt"
          "rule-figures.rkt"
          "redex-rewrite.rkt"
          scriblib/figure
          racket/set
          (except-in esterel-calculus/redex/model/shared
                     quasiquote))

@title[#:tag "sec:reduction"]{Reduction Rules}

@figure["fig:supp" "Supplemental Structures"]{@supp-lang}
@figure["fig:reduction" "Reduction Rules"]{@reduction-relation-pict}

The rules given in @figure-ref["fig:reduction"]
govern how computation takes place within a single instant.

The first rule, @rule["signal"], reduces a @es[signal]
expression to a @es[ρ] expression by introducing a singleton
@es[θ] that binds the signal to @es[unknown].

Once a signal has an entry in a relevant @es[θ], the
@rule["emit"] rule records that a signal is present (using
the composition operator @es[<-] from
@figure-ref["fig:supp"]) and eliminates the @es[emit]
expression. The side-condition ensures that the
environment @es[θ] does not already indicate that the signal
is absent.

In order for an @es[emit] to fire, it must be in the body of
a @es[ρ] in only a specific set of positions, as captured by
the @es[E] contexts, shown in
@figure-ref["fig:supp"]. They include the first
sub-expression of a @es[seq] expression,
the first sub-expression of a @es[(loop^stop p q)] expression,
either branch of a
@es[par], the body of a @es[suspend] or a @es[trap]. Notably
this rule does not allow an expression like
@es[(ρ θ (seq p (emit S)))] to reduce its @es[emit]
expression because the @es[p] could be @es[pause],
delaying the @es[(emit S)] to the next instant. More
generally, the expressions captured by @es[E]
are guaranteed to happen in the current instant.

As we saw in @secref["sec:can-intro"], @es[Can] determines if a signal cannot be emitted. The
rule @rule["absence"] uses @es[Can-θ] (a variation of @es[Can]
that is explained in @secref["sec:can"]) to determine that
a signal cannot be emitted and records that information
in a @es[θ] expression, if that information
is not yet recorded.

Once the status of a signal is recorded as either present
or absent, the @rule["is-present"] and @rule["is-absent"] rules
can reduce @es[present] expressions.

The rules @rule["shared"], @rule["set-old"],
@rule["set-new"], and @rule["readyness"] handle shared
variables in a manner similar to how the previous set of
rules handle signals. The @rule["shared"] rule
introduces a new environment that binds the shared variable
using the @es[e] in the @es[shared] expression to
determine the default value of the variable using
the host language's evaluation function.
The rules @rule["set-old"] and @rule["set-new"] modify a
shared variable depending on whether it has been modified
in the current instant or not.
If the status of a shared variable in the environment
is @es[old], it is being modified for the first time
in the current instant and
the rule @rule["set-old"] replaces the old value
in the environment with the new value.
If the status of a shared variable is @es[new], it has already been modified
in the current instant and the rule
@rule["set-new"] adds
the current value and the new value in the
@es[<=] expression and stores the result in the environment.
Finally, the @rule["readyness"] rule
makes a variable change from writable to readable.
This occurs if @es[Can-θ]'s
result does not contain the shared variable
@es[s], which means it will not be modified in this
instant and thus we can update the environment to mark the
variable as @es[ready]. Furthermore, the side-conditions on
the @rule["shared"], @rule["set-new"], and
@rule["set-old"] rules (as well as the corresponding rules
for sequential variables) ensure that these rules can
fire only if, for every shared variable used in the host language expression,
that variable safe to be read, e.g. is marked as @es[ready] in @es[θ].

The rules @rule["var"], @rule["set-var"],
@rule["if-true"], and @rule["if-false"] cover sequential
variables. Unlike the rules for signals or shared variables,
these rules do not refer to @es[Can]. These variables are
not allowed to be free in two different arms of any @es[par]
expression, so they can be freely read and written.

The final rule that handles @es[ρ] expressions is @rule["merge"].
It combines two environments, lifting an inner environment out
to an outer one and composing them into a single environment.

There are two rules for sequential composition. If the first
sub-expression is @es[nothing], then we replace the entire expression with the second
branch. If the first sub-expression is an @es[exit]
expression, however, then the entire sequence exits,
discarding the second part of the @es[seq] expression.

The next rule handles @es[trap]. Once the body of a @es[trap] has finished evaluating, it will
either be an @es[exit] expression or @es[nothing], and the
@es[harp] (@figure-ref["fig:supp"]) function handles them.

The @es[par] rules are a little more interesting. The
first three refer to
to the definitions of @es[stopped] and @es[done] in
@figure-ref["fig:supp"] and handle
the situations when both branches are finished for
the instant. If one side has reduced to nothing,
the @rule["par-nothing"] rule reduces to the other
one. If one side has @es[exit]ed and the other is @es[paused],
the @rule["par-1exit"] rule preempts the other branch of the
par by bubbling the @es[exit] up. If both sides have
@es[exit]ed the @rule["par-2exit"] rule reduces the
expression to whichever @es[exit] will reach the farthest up
@es[trap]. The @rule["par-swap"] rule switches the branches,
allowing the @rule["par-nothing"] and @rule["par-1exit"]
rule to match regardless of which branch is
@es[exit] or @es[nothing].

The @rule["suspend"] rule reduces to its body when its body
has either @es[exit]ed or reduced to @es[nothing].

This leaves us with one last pair of rules: @rule["loop"] and @rule["loop^stop-exit"].
Intuitively, we would like an expression like @es[(loop p)]
to reduce simply to just @es[(seq p (loop p))], duplicating
the body @es[p] into a @es[seq] expression which becomes the
current iteration of the loop.

Such a rule could give rise to infinite loops within a
single instant, however, which is forbidden in Esterel. We
capture this constraint in our calculus with the
@es[loop^stop] expression form. It is introduced
only by the reduction rule for @es[loop], and is meant to
capture a single unrolling of the loop; the first sub-expression
is the part of the loop that runs in the current instant
and the second sub-expression is the body of the loop, saved
to be used in the next instant. There is no
rule that eliminates a @es[loop^stop] when the first
sub-expression is @es[nothing] (unlike @es[seq], which has
the @rule["seq-done"] rule). As such, programs get stuck
when they contain instantaneous loops.

One thing to note about these rules: with the exception of
@rule["par-swap"], they are strongly normalizing. The proof
is given as @tt{noetherian} in Agda code in the
supplementary material.
