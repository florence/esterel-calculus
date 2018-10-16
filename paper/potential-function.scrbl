#lang scribble/base
@(require "misc-figures.rkt"
          "redex-rewrite.rkt"
          "cite.rkt"
          "util.rkt"
          scriblib/figure
          racket/set
          redex/reduction-semantics
          esterel-calculus/redex/model/potential-function
          esterel-calculus/redex/model/lset
          rackunit
          (except-in esterel-calculus/redex/model/shared
                     quasiquote))

@title[#:tag "sec:can"]{The Can Function}

@figure["fig:can" (list (es Can) " Function")]{@Can-pict}

@figure["fig:can-theta"
        @elem{The @es[Can] Function for @es[ρ] Expressions
         (cases are checked in order)}]{
 @Canθ-pict
}

This section describes the function @es[Can], a
conservative analysis of the state of an Esterel
program that determines its behavior.
Our definition is inspired by @citet[esterel02]'s
definition, generalized to support @es[ρ] expressions and
modified to handle a reduction semantics rather than one
based on annotating the program with program counters.


This function computes a conservative approximation
to the behavior of some given Esterel expression with
respect to some knowledge about signals and shared variables
that is encapsulated in an environment, @es[θ]. In
particular, it computes a set of signals (@es[S]), a set of
exit codes (@es[κ]), and a
set of shared variables (@es[s]). Any @es[S] that is not in the result
is guaranteed not to be emitted in the current instant
(although if some @es[S] is in the result, it may or may not
be emitted in the current instant). Ditto for any shared
variable in the result: if an @es[s] is not the result, then
it is guaranteed that @es[s] is not going to be updated
again in the current instant. If the @es[s] is in the
result, then it may or may not be updated. The exit codes
capture whether or not the given expression pauses, reduces
to @es[nothing], or exits.
If the expression may reduce to @es[nothing], then the code
@es[nothin] will be in the result.
If the expression may pause, then the code @es[paus] will
be in the result.
If the expression may exit with the code @es[n],
then the code @es[n] will be in the result.
Thus, if any of those specific
codes are @emph{not} in the result, then we know the
expression does not have the corresponding behavior.

The notation we use for the records in the definition of
@es[Can] is similar to many record notations, but we use the
precise one in @citet[tapl]'s book @italic[tapl-title]. We
write @es[Can]'s result as a record with three fields, where
curly braces construct records, e.g., the @es[emit] case of
@es[Can] returns a record with a singleton set of signals
(containing @es[S]), a singleton set of exit codes
(containing @es[nothin]) and the empty set of shared
variables. Selecting a field from a record uses dot
notation. For example, @es[(->S (Can p θ))] selects the “S”
field from a call to @es[Can].

The three results from @es[Can] interact with each other in
order to determine the overall result.
Consider the two @es[seq] cases. In the first one, the
side-condition says that @es[nothin] is not in the @es[K] field
for the first sub-expression of the @es[seq], @es[p].
Accordingly, we know that @es[p] does not reduce to
@es[nothing], thus it must either exit or pause. Since it
exits or pauses, we know that none of the behavior of @es[q]
is relevant as it will not be evaluated in this instant and so
the result of @es[Can] for the entire @es[seq] expression is just
its result for the @es[p] expression. This means that
@(term-let
  ([θ (term ·)])
  @esblock[(->S (Can (seq pause (emit S)) θ))
           #:equal?
           (L0set)])
is the empty set, since the @es[emit] must happen in
the next instant.

In the second @es[seq] case, we know that @es[nothin] was a
possible result code, and thus @es[p] might reduce to
@es[nothing] so we have to combine the result of the @es[p]
and @es[q] recursive calls. Mostly this amounts to simply
unioning them, but note that the @es[K] case removes @es[nothin]
from the codes in the result of @es[p] before performing the
union. This removal accounts for the fact that, even if @es[p]
reduces to @es[nothing], @es[q] must also reduce to @es[nothing]
for the @es[seq] expression to reduce to @es[nothing].
For example,
@(term-let
  ([θ (term ·)])
  @esblock[(->K (Can (seq nothing pause) θ))
           #:equal?
           (L1set paus)])
correctly contains only the exit code @es[paus].

The @es[loop^stop] expression form, in contrast, always ignores
the second sub-expression, because we know that the second sub-expression can
affect only future instants.

Various other cases in the definition of @es[Can] reflect
the semantics of the different constructs in similar ways.
The cases handling @es[present] consult the given @es[θ] to
see if the status of the signal is known and look only at
the corresponding branch of the @es[present] expression if
so. The rule for @es[par] takes into account the same
behavior that the four @es[par] rules in the reduction relation do when computing the codes for
the entire expression out of the codes of the
subexpressions. The @es[trap] case uses the metafunction
@es[↓] to adjust the exit codes in a manner that mimics how
@es[trap] expressions reduce. Since the @es[shared] form
introduces a new signal, its case in @es[Can] removes that
signal from the results, as the signal is lexically scoped.
In each of these cases, @es[Can] ignores the @es[e] expressions,
as it does not reason about the behavior of the host language.

This leaves the @es[signal] and @es[ρ] cases. 
Consider first the cases that handle @es[signal] expressions. The second
@es[signal] case is the more straightforward one.
It says that the result for the entire @es[signal] form is the same
as the result for the body of a @es[signal] form when it is
analyzed with no knowledge about the signal. But there would be a problem
with the @es[Can] function if that were the only case.

To motivate the first @es[signal] case in @es[Can], 
consider this call:
@esblock[(->S (Can (signal S2 (present S2
                                       (emit S1)
                                       nothing)) ·))
         #:equal?
         (L0set)]
If we took the second @es[signal] case in @es[Can],
then this would return a set containing @es[S1]. It actually
returns the empty set, however, because of that first
case. In particular, that case first calls @es[Can] with
@es[S2] set to @es[unknown] and checks to see if @es[S2]
is not present in the “S” portion of the result. It is not
(because there are no @es[(emit S2)] expressions), so
@es[Can] then sets @es[S2] to @es[absent] and reprocesses
its body. This time, because @es[S2] is known to
be @es[absent], @es[Can] considers only the last sub-expression
of the @es[present], thereby ignoring
the @es[(emit S1)] and returning the empty set of signals.

In isolation, analyzing the body twice seems like
overkill, especially because it triggers exponential behavior
in the number of nested @es[signal] forms.@note{This
 exponential behavior affected our testing of the
 semantics against each other; see
 @secref["sec:testing"] and @secref["sec:stdred"] for more.} But consider
this call to @es[Can]:
@(provide can-exp-example-d)
@(define/esblock
   can-exp-example-t
   can-exp-example-d
   (->S (Can (signal S1
                     (seq (present S1 pause nothing)
                          (signal S2 (present S2
                                              (emit S1)
                                              nothing)))) ·)))
@(check-equal? can-exp-example-t (term (L0set)))

@can-exp-example-d

This example input is a bit complex, but first notice that
the inner @es[signal] expression is the same as the previous
example (and there are no other @es[(emit S1)] expressions),
so we know that @es[S1] is not going to be emitted.
If @es[Can] did not have that first @es[signal] case, then
it could not learn that @es[S1] cannot be emitted and thus we
would not be able to use the @rule["absence"] rule on
this expression.

Finally, for the @es[ρ] case, the @es[Can] function
dispatches to @es[Can-θ]. The @es[Can-θ] function looks
complex, but it is essentially the same as the two
@es[signal] cases. It is broken out into its own function
because @es[ρ] binds multiple signals at once; so @es[Can-θ]
recurs though the structure of the environment, considering
each of the signals that are bound. The first case of @es[Can-θ]
corresponds to the first @es[signal] case in @es[Can]; the
second case in @es[Can-θ] corresponds to the second
@es[signal] case, and the last case in @es[Can-θ]
corresponds to the situation where there are no more signals
bound in @es[θ] (and the remainder of the @es[θ_1] can be
dropped as it contains only information about @es[s] and
@es[x] variables, which @es[Can] does not need, as it does
not reason about host expressions).
