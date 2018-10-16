#lang scribble/base
@(require "misc-figures.rkt"
          "redex-rewrite.rkt"
          "cite.rkt"
          "util.rkt"
          scriblib/figure
          racket/set)

@title[#:tag "sec:gentle"]{A sense of Esterel}

@figure["fig:lang" "Esterel Syntax"]{@lang}

This section provides some background on Esterel both to
introduce the language to those not familiar with it and to
orient Esterel experts with the particular notation we have
chosen for Kernel Esterel. @Figure-ref["fig:lang"] shows the
syntax we use for our Esterel calculus.

Evaluation of an Esterel program is unlike conventional
programming languages in that it proceeds in a series of
@italic{instants}, each of which is intended to happen in,
essentially, no time. Once an instant has completed, the
Esterel program waits for the state of the outside world to
change, which triggers another instant of computation. The
external state changes of the world are reflected in Esterel
via @italic{signals}. Each signal can either be present
(set), absent (not set), or in an indeterminate state, where
we do not know yet if it will be present or absent. Once a
signal's value becomes known (in a specific instant), it
cannot change. Accordingly, the outside world may set a
signal to present or it may not, indicating that its value
is as yet undetermined (as the program itself may set
it).@note{For those familiar with Esterel: free
 signals in programs in our calculus correspond to
 input-output signals in Esterel.} Once an
instant completes, the Esterel program will have
emitted some set of signals, which the outside world
can observe and react to (by setting different input
signals), in order to provoke different behavior in the next
instant when the Esterel program runs.

Esterel is typically used as an embedded language, where
the outside world is some other programming language, @italic{e.g.},
C for reactive, real-time systems@~\cite[compiling-esterel],
Bigloo@~\cite[bigloo] and JavaScript for GUIs@~\cite[hiphop],
or Racket@~\cite[plt-tr1] for medical prescriptions@~\cite[pop-pl].
The external language generally controls when instants take place and
sets up the signal environment for each instant.

@section{Conditioning on signals: @es[present]}

@right-figure[#:lines 8 #:caption "A First Example" #:tag "ex:first"]{
@esblock[(signal SL
           (seq (emit SL)
                (present SL
                         (emit SO1)
                         (emit SO2))))
         #:run-instants
         (list '((sig SO1 unknown)
                 (sig SO2 unknown)))
         (ρ θ nothing)
         (list (set 'SL 'SO1))]}

Esterel programs can also have local signals that they
use to communicate internally. Let us consider a few example
programs that use internal signals to get a sense of
how Esterel programs evaluate. @Figure-ref["ex:first"]
shows a first example.

This program has no input signals and two output
signals, @es[SO1] and @es[SO2]; we prefix all signal
names with an @tt{S}. The @es[signal] form
is a binding form that introduces a local signal (here named @es[SL])
available in its body. Signals that are free in the entire
program are the ones that support communication
with the host language, external to Esterel.


@right-figure[#:lines 7 #:caption @elem{This time with @es[par]} #:tag "ex:second"]{
@esblock[(signal SL
           (par (emit SL)
                (present SL
                         (emit SO1)
                         (emit SO2))))
         #:run-instants
         (list '((sig SO1 unknown)
                 (sig SO2 unknown)))
         (ρ θ nothing)
         (list (set 'SL 'SO1))]}

The @es[seq] form is simply sequential composition, so the
first thing this program does in the body of the @es[signal]
form is @es[emit] @es[SL], which means that the signal @es[SL]
is now known to be present for this entire instant. Next, the program
evaluates a signal conditional, written using the
@es[present] keyword in Esterel. When a signal is known
to be present, a @es[present] form is equivalent to its
first sub-expression, in this case @es[(emit SO1)]. So this
program @es[emit]s @es[SO1] and then terminates, ending the
instant with @es[SO1] set and @es[SO2] not set.

Esterel also supports a deterministic form of parallelism
and indeed if we replace the sequential composition
in @figure-ref["ex:first"] with parallel composition, as shown in
@figure-ref["ex:second"], the program is
guaranteed to behave identically. Specifically,
the @es[present] form in the second arm of the @es[par]
(conceptually) blocks until the signal @es[SL] is emitted or we
learn it cannot be emitted (in this instant). So
the first arm of the @es[par] is the only part of the
program that can progress, and once it performs the
@es[(emit SL)], that unblocks @es[present] form, enabling
@es[(emit SO1)] to happen.

@right-figure[#:lines 6
 #:caption @elem{A signal never emitted}
 #:tag "ex:third"]{
@esblock[(signal SL
           (present SL
                    (emit SO1)
                    (emit SO2)))
         #:run-instants
         (list '((sig SO1 unknown)
                 (sig SO2 unknown)))
         (ρ θ nothing)
         (list (set 'SO2))]}

In order for a @es[present] expression to become unblocked
and evaluate the second sub-expression, the Esterel program
must know that there is no way that the given signal
can be emitted (in this instant). One way this can happen
is that there are no occurrences of @es[(emit SL)].
So, if we remove the @es[(emit SL)] from our running example,
as shown in @figure-ref["ex:third"],
then the program will @es[emit] the signal @es[SO2], as
the @es[present] form reduces to its second branch
since there is no way to emit @es[SL].

@right-figure[#:lines 6
 #:caption @elem{Cyclic signal dependencies}
 #:tag "ex:fourth"
 #:wide? #t]{
@esblock[(signal SL1
           (signal SL2
             (par (present SL1 (emit SL2) nothing)
                  (present SL2 (emit SL1) nothing))))
         #:run-instants
         (list '())
         #f
         (list)]}

The way that @es[present] works helps guarantee Esterel's
form of deterministic concurrency. Until a particular signal's
value becomes known, the program simply refuses to
make a choice about which branch to run.
This style of conditional raises many interesting questions
about how apparent cyclic references interact with each other, however.
For example, what should the program in @figure-ref["ex:fourth"] do? (@es[nothing]
is the Esterel equivalent of @tt{unit} or @tt{void} in other languages.)
How such programs behave is well-studied
in the Esterel community and touches on the notions of logical correctness
and constructiveness, which we return to in @secref["gettin stuck"].

@section{Running for multiple instants: @es[pause]}

@right-figure[#:lines 8
 #:caption @elem{Multiple instants}
 #:tag "ex:fifth"]{
@esblock[(signal SL
           (par (seq pause
                     (emit SL))
                (present SL
                         (emit SO1)
                         (emit SO2))))
         #:run-instants
         (list '((sig SO1 unknown)
                 (sig SO2 unknown))
               '((sig SO1 unknown)
                 (sig SO2 unknown)))
         (ρ θ nothing)
         (list (set 'SO2) (set 'SL))]}

So far, all of the example programs have terminated in a
single instant but, in general, an Esterel program might run
to some intermediate state and then @es[pause]. When all of
the parallel branches of some program have paused or
terminated, then the instant terminates. During the next
instant, however, evaluation picks up right where it left
off, with whatever remains of the program.

As an example, consider the program in @figure-ref["ex:fifth"].
As it starts, the second arm of the @es[par] blocks,
as with the example in @figure-ref["ex:second"].
The first arm of the @es[par] first evaluates
@es[pause], which means that that arm of the @es[par] has
terminated for the instant and thus the @es[(emit SL)]
is not going to happen in this instant. Accordingly the
@es[present] can take the else branch, safe in the knowledge that
no @es[(emit SL)] can happen this instant.

In the next instant, the only thing that
remains is the @es[(emit SL)], so only @es[SL] is emitted.

@section[#:tag "sec:can-intro"]{Determining That a Signal Cannot be Emitted: @es[Can]}

@right-figure[#:lines 17
 #:caption @elem{Can}
 #:tag "ex:sixth"
 #:wide? #t]{
@esblock[(signal SL1
           (signal SL2
             (signal SL3
               (par (present SL1
                             (present SL2
                                      (emit SO1)
                                      (emit SL3))
                             (present SL2
                                      (emit SO2)
                                      (emit SL3)))
                    (seq
                     (emit SL2)
                     (seq
                      (present SL3 pause nothing)
                      (emit SL1)))))))
         #:run-instants
         (list '((sig SO1 unknown)
                 (sig SO2 unknown)))
         (ρ θ nothing)
         (list (set 'SL2 'SL1 'SO1))]}

Determining whether or not a signal can be emitted is not
simply a matter of eliminating untaken branches in
@es[present] expressions and then checking the remaining
@es[emit] expressions. Sometimes, a @es[present] expression
may be blocked on some as-yet indeterminate signal, but portions
of its branches are known to not be able to run, which enables
us to declare that some signal will not be emitted.

For example, consider the program in
@figure-ref["ex:sixth"]. The @es[par] expression's first
sub-expression is a @es[present] expression and its second
sub-expression is a @es[seq] expression. The @es[present]
expression is
blocked on @es[SL1]. Of course,
the last expression in the @es[seq] expression emits @es[SL1] but
beware: it is preceded by another @es[present] expression that may
or may not pause. If it does pause, then the @es[(emit SL1)]
happens in a future instant (so we take the ``else'' branch
of the @es[present] on @es[SL1]). If it does not pause, then
the @es[(emit SL1)] happens in the current instant (and so
we take the ``then'' branch of the @es[present] on
@es[SL1]).

This complex interplay of signals and branches of @es[par]
expressions is completely fine in Esterel. Let us work
through how Esterel evaluates this program.

The first @es[emit] that happens is @es[(emit SL2)].
Once that happens, we know how the inner @es[present]
expressions will go, even though they cannot yet fire because
we do not yet know about @es[SL1].
In particular, we know that neither one takes their second
sub-expression and thus none of the @es[(emit SL3)] expressions
will be evaluated. Accordingly we now know that the
@es[(present SL3 pause nothing)] in the other side of
the @es[par] expression reduces to @es[nothing] and we
can evaluate @es[(emit SL1)] which unblocks the
@es[present] on @es[SL1], which triggers the @es[emit]
on the output signal @es[SO1].

The most important step in this sequence was when Esterel
decided that @es[SL3] cannot be emitted. The decision
procedure for determining when a signal cannot be emitted is
called @es[Can]. It follows the same reasoning we have here,
but accounts for other details of the core language of
Esterel. For example, it reasons about the first
sub-expression of @es[seq] expressions in order to determine
if they might pause, in order to reason about @es[emit]
expressions that follow.

The full definition is given in @figure-ref["fig:can"] and
is explained in @secref["sec:can"].

@section[#:tag "gettin stuck"]{Getting stuck: Logical Correctness and Constructivity}

@(define stuck-note
   @note{Conventionally, the
 @es[suspend] form is a third way that prevents @es[Can] from
 determining a signal's value. In our setting, however,
 @es[suspend] is rewritten to a use of @es[present] as part of the
 transition between instants.})


@right-figure[#:lines 5
 #:caption @elem{No possible value for @es[S1]}
 #:tag "ex:stuck1"
 #:wide? #f]{
@esblock[(signal S1
           (present S1 nothing (emit S1)))]}

The style of instantaneous decision making in Esterel
facilitated via the @es[Can] function leads to
programs that have no meaning, even though 
a traditional programming language would given them meaning. Such
programs are called @italic{logically incorrect}.


@right-figure[#:lines 5
 #:caption @elem{Too many values for @es[S1]}
 #:tag "ex:stuck2"
 #:wide? #f]{
@esblock[(signal S1
           (present S1 (emit S1) nothing))]}
Logical correctness can be thought of as a consequence of
the instantaneous nature of decision making in Esterel: if
decisions about the value of a signal are communicated
instantly and that value cannot change, then the program should behave as if that value
was determined at the start of the instant. Therefore, there
should only be one possible value for each signal. Some
programs, however, have zero or multiple possible
assignments. Consider the program in @figure-ref["ex:stuck1"].
No matter the definition of @es[Can], @es[S1] cannot be set to either present or
absent. If @es[S1] were present, the program would take the
first branch of the condition, and the program would
terminate without having emitted @es[S1]. If @es[S1] were
set to absent, the program would chose the second branch and
emitting the signal. Both of these executions lead to a
contradiction, therefore there are no valid assignments of
signals in this program. This program is logically incorrect.

The opposite is true for the program in @figure-ref["ex:stuck2"].
Here, if @es[S1] is chosen to be present, the conditional
will take the first branch and @es[S1] will be emitted,
justifying the choice of signal value. However, if the
signal is chosen to be absent, the signal will not be
emitted and the choice of absence is also justified. Thus
there are two possible assignments to the signals in this
program, and this program too is rejected as logically incorrect.

@(define connote
@note{The use of the name ``constructive'' arises from
 connections to constructive logic@~cite[constructive-boolean-circuits].})

@right-figure[#:lines 10
 #:caption @elem{Constructiveness examples}
 #:tag "ex:stuck3"
 #:wide? #f]{
 @esblock[(signal S1
            (present S1 (emit S1) (emit S1)))
          (signal S1
            (seq (present S1
                          nothing
                          nothing)
                 (emit S1)))]}

A related notion, @emph{constructiveness}, arises from the order of execution
imposed by @es[seq] and
@es[present]. All
decisions in the first part of a @es[seq] must be made
before decisions in the second part and the value of a signal
being conditioned on by @es[present] must be determined before
decisions within either branch of the @es[present] can be
made. Decisions that may affect sibling branches in a @es[par]
expression, however, may happen in any order.

To ensure these ordering constraints, Esterel imposes an order on
information propagation: decisions about the value of a
signal can only be used by the portion of the program that is
after (in the sense of the ordering imposed by @es[seq] and
@es[present]) it is emitted. Thus, programs that are logically
correct may still be rejected because there is no
order in which to run the program that will arrive at the
single, valid assignment. Such programs are called
non-constructive.@|connote| Accordingly, not all logically
correct programs are constructive, but the converse is true: all
constructive programs are logically correct.
Put another way, making a guess
about the value of a signal and backtracking if the guess
turns out to be wrong is a match for logical correctness,
but would admit programs that are non-constructive.

@right-figure[#:lines 7
 #:caption @elem{Getting stuck}
 #:tag "ex:stuck4"
 #:wide? #t]{
@esblock[(signal SL1
           (signal SL2
             (par (present SL1 (emit SL2) nothing)
                  (seq (present SL2 pause nothing)
                       (emit SL1)))))
         #:run-instants
         (list '())
         #f
         (list)]}

Succinctly, a program is constructive if it is logically
correct, and the values of signals can be determined without
any speculation: a signal is present only after it has
been emitted, and a signal is absent only after @es[Can]
determines it cannot be emitted without speculating about the
value of other signals.

Example non-constructive programs are shown in
@figure-ref["ex:stuck3"]. The first program has only one possible assignment for @es[S1], as
it is emitted by both branches of the conditional. Because
@es[present] requires that the value of @es[S1] be
known before executing a sub-expression, however, there
is no valid order in which to execute the code, and the
program is rejected as non-constructive.
A similar phenomena can be seen in the second program in
@figure-ref["ex:stuck3"], but with @es[seq].

The two ordering constraints can interact in complex ways.
In the example in @figure-ref["ex:stuck4"], the
@es[(emit SL1)] is in a @es[seq] that may or may not
@es[pause], which prevents us from determining if @es[SL2]
is emitted.

Non-constructive programs are handled two different ways by
Esterel implementations. Some approximate constructiveness 
with a conservative static analysis and reject programs
they cannot prove constructive on all inputs. This is the
default behavior of @|Esterel\ v5|@~cite[esterel-v5]. Others treat
non-constructivity as as runtime error, raising an error if,
during an instant, the program cannot determine a value for
all signals. This is the behavior of  HipHop.js@~cite[hiphop], and Esterel
v5 when used with the @tt{-I} flag.

In the circuit semantics for Esterel, a non-constructive programs is
one that, when compiled to a circuit, will cause the circuit
to misbehave, never settling because of cyclic dependencies
between inputs and outputs of some of the gates. That is, a
program is constructive if and only if its circuit
stabilizes within some fixed delay@~cite[esterel02 constructive-boolean-circuits].

Non-constructive programs usually get stuck in our calculus,
but they do not always. The issues here are subtle and
revisited in @secref["sec:constructiveness"].

@section{Loops, @es[suspend], non-local exits, variables, and the host language}

Our calculus also covers the rest of Kernel Esterel. The
@es[(trap p)] and @es[(exit n)] forms allow non-local
control. Roughly speaking, @es[(exit n)] will abort
execution up the the @es[n+1]@superscript{th} enclosing
@es[(trap p)], reducing it to @es[nothing]. These can be
used for exception handling, but also for non-exceptional
control flow. For example, it may be simpler to express some
repeating task on the assumption it never terminates and
then, in parallel to it, use @es[exit] to abort it (with a
@es[trap] that is outside both). Kernel Esterel's trap is a
simplified form of Esterel's trap where traps are named and
escaping uses the names.

The @es[loop] form is an infinite loop, running its body,
@es[p], over and over, but with a constraint that the loop's
body can be started at most once in any instant. This means
that the body of a loop must either pause or exit at least once in every
iteration, thereby ensuring that instants always terminate.
One subtle ramification of this point is that two
separate iterations of a loop may run within a single instant,
but only in the situation where we finish an iteration that
was started in a previous instant and then start a new one
in the current instant (which must then pause or exit). We return
to this point in @secref["sec:cb"].

Loops that fail this condition are called @italic{
 instantaneous} and programs with such loops are not
constructive. In our calculus, we handle this by reducing a
loop in such a way that the program gets stuck if the loop
were to be instantaneous.

The @es[suspend] form has a subtle semantics. If we are starting a
@es[suspend] for the first time, it simply runs the body. But, if we
are picking up from a previous instant where we @es[pause]d in the body
of a @es[suspend], then we test the signal. If it is present,
the entire @es[suspend] is paused until the next instant. If it is not present,
evaluation continues within the @es[suspend], picking up at
the @es[pause].

The @es[suspend] form is used to implement many useful,
high-level behaviors. One straight-forward use is to
implement a form of multiplexing, where some portion of the
input signals are used directly by several different
sub-pieces of the computation at once, and another portion
of the input determines which of those computation is the
desired output. For example, an ALU might, in parallel, both
add and multiply its inputs and store the output in the same
place. The @es[suspend] form can be used to control whether
the addition or multiplication computation happens.

Another use of @es[suspend] is in task management. As a
workflow is progressing there may be a task that runs at
some interval, but where the interval may change over time.
This repeating task is important, but there may be an
occasional situation where some much more important task
takes precedence. So, we wish to pause the subcomputation
corresponding to the repeating task with the intention of
resuming it with its current state, but at a later moment
in time. This pattern is captured easily with @es[suspend].

@(define |Esterel v5| @nonbreaking{Esterel v5})

And finally, Esterel has two forms of variables: shared
variables (lowercase @es[s]) and sequential variables
(@es[x]). Both of these variables refer to values and expressions in a host language,
into which Esterel is embedded. For example, in @|Esterel\ v5|@~cite[esterel-v5] the host
language is a subset of C, whereas in HipHop.js@~cite[hiphop] the host language is Javascript.

Shared variables may be looked at or modified at by multiple
branches of a @es[par] expression, but the program's
execution cannot be influenced by the value of the variable
until it can no longer be written in the current instant (in
a manner reminiscent of, but simpler than,
@citet[lvars]'s LVars). Tracking if a shared variable is
writable uses the same mechanism as tracking whether or not
a signal has been emitted, and shared variables are subject
to the logical correctness and constructivness constraints.

Multiple writes are allowed, but only via an associative and
commutative combining operation, ensuring the order of
writes is not observable. In our calculus we restrict shared
variables to always be natural numbers and use @es[+] as the
only combining operation.

Sequential variables may be used only sequentially (any
given variable may not appear free in both branches of
any specific @es[par] expression). This frees them from the constraints
imposed on shared variables, allowing them to act as typical mutable variables
without sacrificing deterministic concurrency. In our calculus they are
bound to natural numbers and support a
conventional conditional expression, @es[if], that tests
if the value is @es[0] or not.

For a fuller explanation of these features and how they
behave, start with @citet[compiling-esterel]'s book
@italic{Compiling Esterel}, especially the first two chapers.
The semantic rules in @figure-ref["fig:reduction"] also provide
more details on how these constructs work.
