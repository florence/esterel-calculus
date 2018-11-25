#lang scribble/base
@(require "misc-figures.rkt"
          "redex-rewrite.rkt"
          "cite.rkt"
          "util.rkt"
          scriblib/figure
          racket/set)

@title[#:tag "sec:gentle"]{A Sense of Esterel}

@figure["fig:lang" "Esterel Syntax"]{@lang}

This section provides some background on Esterel both to
introduce the language to those not familiar with it and to
orient Esterel experts with the particular notation we have
chosen for Kernel Esterel. @Figure-ref["fig:lang"] shows the
syntax we use for our Esterel calculus.

Evaluation of an Esterel program is unlike conventional
programming languages in that it proceeds in a series of
@italic{instants}. Each instant happens in,
essentially, no time and appears atomic from the outside. An instant is triggered by a change in the state of the outside world.
The
external state changes of the world are communicated to Esterel
via @italic{signals}. Within each instant, each signal can either be present
(set), absent (not set), or in an indeterminate state, where
it is not yet known if it will be present or absent. Once a
signal's value becomes known in a specific instant, it
cannot change. Accordingly, the outside world may, in between instants, set a
signal to present or it may not, indicating that its value
is as yet undetermined (as the program itself may set
it).@note{For those familiar with Esterel: free
 signals in programs in our calculus correspond to
 input-output signals in Esterel.} Once the instant begins these signal values cannot be modified by outside
world, preventing interference with the computation. Once an
instant completes, the Esterel program will have
decided the value of all of its signals. The outside world
can then observe these values, and respond by setting different
signals for the next
instant. The value of signals does not carry over
between instants. 

Esterel is typically used as an embedded language, where
the outside world is some other programming language, @italic{e.g.},
C for reactive, real-time systems@~\cite[compiling-esterel],
Bigloo@~\cite[bigloo] and JavaScript for GUIs@~\cite[hiphop],
or Racket@~\cite[plt-tr1] for medical prescriptions@~\cite[pop-pl].
The external language controls when instants take place and
sets up the signal environment for each instant. From the perspective of the host language,
the atomicity of instants gives Esterel a notion of
discrete, logical time. Each instant represents
one tick of the clock, and the host language controls the ``clock speed''
by explicitly starting instants.

@section{Conditioning on Signals: @es[present]}

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

@(define sig-note @note{We prefix all signal names with an @tt{S}.})

This program has two external
signals, @es[SO1] and @es[SO2],@sig-note through which it will communicate its output. The @es[signal] form
is a binding form that introduces a local signal (here named @es[SL])
available in its body. Signals that are free in the entire
program are the ones that support communication
with the host language, external to Esterel. At the beginning of the instant the values
of @es[SL], @es[SO1], and @es[SO2] are not known.


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

The @es[seq] form is sequential composition, so
this program first
@es[emit]s @es[SL], which means the signal @es[SL]
is known to be present for this entire instant. Next, the program
evaluates a signal conditional, written using the
@es[present] keyword in Esterel. When a signal is known
to be present, a @es[present] form is equivalent to its
first sub-expression, in this case @es[(emit SO1)]. So this
program @es[emit]s @es[SO1] and then terminates, ending the
instant with @es[SO1] present and with @es[SO2] absent.

Esterel also supports a deterministic form of parallelism
and indeed if we replace the sequential composition
in @figure-ref["ex:first"] with parallel composition, as shown in
@figure-ref["ex:second"], the program is
guaranteed to behave identically. Specifically,
the @es[present] form in the second arm of the @es[par]
(conceptually) blocks until the signal @es[SL] is emitted or we
learn it cannot be emitted in this instant. So
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
must determine that given signal
cannot be emitted in this instant. One way this can happen
is that there are no occurrences of @es[(emit SL)].
So, if we remove the @es[(emit SL)] from our running example,
as shown in @figure-ref["ex:third"],
then the program will @es[emit] the signal @es[SO2].

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

@section{Running for Multiple Instants: @es[pause]}

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

The @es[pause] expression brings the host language's notion
of logical time into Esterel. From the Esterel programmer's
perspective, every instruction in the language is @italic{
 instantaneous}---taking zero logical time---with the
exception of @es[pause], which takes one unit of
time. This effectively stops a thread of execution when it reaches
@es[pause], until the host language starts the next time
step. At the start of the next instant, one unit of time
has passed, so the @es[pause]s will have had enough ``time''
to complete and the program will resume from that point.

As an example, consider the program in @figure-ref["ex:fifth"].
As it starts, the second arm of the @es[par] blocks,
as with the example in @figure-ref["ex:second"].
The first arm of the @es[par] first evaluates
@es[pause], which means that that arm of the @es[par] has
terminated for the instant, and cannot reach the @es[(emit SL)]
until the next instant. Accordingly the
@es[present] takes the else branch, safe in the knowledge that
no @es[(emit SL)] can happen this instant.
In the next instant, the program resumes from each @es[pause] it hit the previous instant. Therefore
only @es[SL] is emitted in the second instant.

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
@es[present] expressions that have executed and then checking the remaining
@es[emit] expressions. Sometimes, a @es[present]
may be blocked on some as-yet indeterminate signal, but portions
of its branches are already known to be unreachable because other signal values are known, enabling
us to declare that some signal is absent.

For example, consider the program in
@figure-ref["ex:sixth"]. The @es[par]'s first
sub-expression is a @es[present] and its second
is a @es[seq]. The @es[present]
expression is
blocked on @es[SL1]. Of course,
the last expression in the @es[seq] expression emits @es[SL1] but
beware: it is preceded by another @es[present] expression that may
or may not pause. If it does pause, then the @es[(emit SL1)]
happens in a future instant (so we take the ``else'' branch
of the @es[present] on @es[SL1]). If it does not pause, then
the @es[(emit SL1)] happens in the current instant (and so
we take the ``then'' branch of the @es[present] on
@es[SL1]). Let's work through how Esterel evaluates this
complex interplay of signals and branches of @es[par] expressions.

First @es[SL2] is emitted.
Once it is, it is clear which branch the inner @es[present]
expressions will take, even though they cannot yet run because
we do not yet know about @es[SL1].
In particular, neither one can take their ``else''
branch and thus none of the @es[(emit SL3)] expressions
can be evaluated. Accordingly we can now reduce the
@es[(present SL3 pause nothing)]
to @es[nothing]. From there we
can evaluate @es[(emit SL1)], which unblocks the
@es[present] on @es[SL1], which @es[emit]s
the output signal @es[SO1].

The most important step in this sequence was when Esterel
decided that @es[SL3] cannot be emitted. The decision
procedure for determining when a signal cannot be emitted in the current instant is
called @es[Can]. It follows the same reasoning we have here,
but accounts for other details of the core language of
Esterel. For example, if the first sub-expression of
a @es[seq] cannot terminate in a given instant, @es[Can] will
rule out any emissions in the second sub-expression.

The full definition is given in @figure-ref["fig:can" "fig:can-theta"], and
is explained in @secref["sec:can"].

@section[#:tag "gettin stuck"]{Getting Stuck: Logical Correctness and Constructivity}

@(define stuck-note
   @note{Conventionally, the
 @es[suspend] form is a third way that prevents @es[Can] from
 determining a signal's value. In our setting, however,
 @es[suspend] is rewritten to a use of @es[present] as part of the
 transition between instants.})


@right-figure[#:lines 4
 #:caption @elem{No possible value for @es[S1]}
 #:tag "ex:stuck1"
 #:wide? #f]{
@esblock[(signal S1
           (present S1 nothing (emit S1)))]}

The style of instantaneous decision making in Esterel,
facilitated via @es[Can], leads to
programs with no meaning, even though 
a traditional programming language would given them meaning. Such
programs are called @italic{logically incorrect}.


Logical correctness can be thought of as a consequence of
the instantaneous nature of decision making in Esterel: if non-@es[pause] expressions take no logical time,
then decisions about the value of a signal are communicated
instantly and that value cannot change. Therefore, the program should behave as if that value
was determined at the start of the instant. Therefore, there
should be exactly one value for each signal. Some
programs, however, have zero or multiple possible
assignments. Consider the program in @figure-ref["ex:stuck1"].
No matter the definition of @es[Can], @es[S1] cannot be set to either present or
absent. If @es[S1] were present, the program would take the
first branch of the condition, and the program would
terminate without having emitted @es[S1]. If @es[S1] were
set to absent, the program would chose the second branch and
emitting the signal. Both executions lead to a
contradiction, therefore there are no valid assignments of
signals in this program. This program is logically incorrect.

The opposite is true of the signals in the program in @figure-ref["ex:stuck2"].
Here, if @es[S1] is chosen to be present, the conditional
will take the first branch and @es[S1] will be emitted,
justifying the choice of signal value. However, if the
signal is chosen to be absent, the signal will not be
emitted and the choice of absence is also justified. Thus
there are two possible assignments to the signals in this
program, and this program is also logically incorrect.

@(define connote
@note{The use of the name ``constructive'' arises from
 connections to constructive logic@~cite[constructive-boolean-circuits].})


@right-figure[#:lines 4
 #:caption @elem{Too many values for @es[S1]}
 #:tag "ex:stuck2"
 #:wide? #f]{
@esblock[(signal S1
           (present S1 (emit S1) nothing))]}

A related notion, @emph{constructiveness}, arises from an order of execution
imposed by @es[seq] and
@es[present]. All
decisions in the first part of a @es[seq] must be made
before decisions in the second part and the value of a signal
being conditioned on by @es[present] must be determined before
decisions within either of its branches can be
made. Decisions that may affect sibling branches in a @es[par],
however, may happen in any order.

To ensure these ordering constraints, Esterel imposes an order on
information propagation: decisions about the presence of a
signal can only be used by the portion of the program that is
after (in the sense of the ordering imposed by @es[seq] and
@es[present]) it is emitted. Thus, programs that are logically
correct may still be rejected because there is no
order in which to run the program that will arrive at the
single, valid assignment. Such programs are called
non-constructive.@|connote| Not all logically
correct programs are constructive, but the converse is true: all
constructive programs are logically correct.
Put another way, making a guess
about the value of a signal and backtracking if the guess
turns out to be wrong would admit logically correct,
but non-constructive, programs.

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

Succinctly, a program is constructive if it is logically
correct, and the values of signals can be determined without
any speculation: a signal is present only after it has
been emitted, and a signal is absent only after @es[Can]
determines it cannot be emitted.

Example non-constructive programs are shown in
@figure-ref["ex:stuck3"]. The first program has only one possible assignment for @es[S1], as
it is emitted by both branches of the conditional. Because
@es[present] requires that the value of @es[S1] be
known before executing a sub-expression, however, there
is no valid order in which to execute the code, and the
program is rejected as non-constructive.
A similar phenomena can be seen in the second program in
@figure-ref["ex:stuck3"], but with @es[seq].

The two ordering constraints can interact.
In the example in @figure-ref["ex:stuck4"], the
@es[(emit SL1)] is in a @es[seq] that may or may not
@es[pause], which prevents us from determining if @es[SL2]
is emitted.

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

Non-constructive programs are handled two different ways by
Esterel implementations. Some approximate constructiveness 
with a conservative static analysis and reject programs
they cannot prove constructive on all inputs. This is the
default behavior of @|Esterel\ v5|@~cite[esterel-v5]. Others treat
non-constructivity as as runtime error, raising an error if,
during an instant, the program cannot determine a value for
all signals. This is the behavior of  Hiphop.js@~cite[hiphop], and Esterel
v5 when used with the @tt{-I} flag.

In the circuit semantics for Esterel, a non-constructive programs is
one that, when compiled to a circuit, will cause the circuit
to misbehave, never settling because of instantaneous cyclic dependencies
between inputs and outputs of some of the gates. That is, a
program is constructive if and only if its circuit
stabilizes within some fixed delay@~cite[esterel02 constructive-boolean-circuits].

Non-constructive programs usually get stuck in our calculus,
but they do not always. The issues here are subtle and
revisited in @secref["sec:constructiveness"].

@section{Loops, @es[suspend], Non-local Exits, Variables, and the Host Language}

Our calculus also covers the rest of Kernel Esterel. The
@es[(trap p)] and @es[(exit n)] forms allow non-local
control. Roughly speaking, @es[(exit n)] will abort
execution up the the @es[n+1]@superscript{th} enclosing
@es[(trap p)], reducing it to @es[nothing]. These can be
used for exception handling, but also for non-exceptional
control flow. For example, it may be simpler to express some
repeating task on the assumption it never terminates and
then, in parallel, use @es[exit] to abort the task when necessary.
Kernel Esterel's trap is a
simplified form of Esterel's trap where traps are named and
exits refer to those names.

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
an interval that varies over time.
This repeating task is important, but there may be an
occasional situation where some more important task
takes precedence. @es[suspend] can be used to pause the subcomputation
corresponding to the repeating task,
and resume it later without losing its current state.

@(define |Esterel v5| @nonbreaking{Esterel v5})

And finally, Esterel has two forms of variables: sequential
variables (@es[x]) and shared variables (lowercase
 @es[s]). Both of these variables refer to values and expressions in a host language,
into which Esterel is embedded. For example, in @|Esterel\ v5|@~cite[esterel-v5] the host
language is a subset of C, whereas in Hiphop.js@~cite[hiphop] the host language is JavaScript.

Sequential variables are conventional mutable variables. To ensure deterministic concurrency, they may be used only sequentially (any
given variable may not appear free in both branches of
any specific @es[par] expression).

Shared variables, on the other hand, may be modified or looked at in multiple
branches of a @es[par] expression. However, restrictions apply
to ensure that the order of modifications
is not observable. In particular, the program's
execution cannot be influenced by the value of the variable
until after all modifications have been performed (in
a manner reminiscent of, but simpler than,
@citet[lvars]'s LVars).

Shared variables start each instant
with their old values, carried over from the previous instant.
Multiple writes to a shared variable within an instant are collected 
with an associative and commutative operation,
which throws away the value from the previous instant.
After all possible writes are collected,
the shared variable's value is available.
Tracking if a shared variable is
writable uses the same mechanism as tracking whether or not
a signal is set, and shared variables are subject
to the same logical correctness and constructiveness constraints as signals.

For simplicity, our calculus restricts shared and sequential
variables to be natural numbers. Shared variables use @es[+] as the
only combining operation. Sequential variables also support a
conventional conditional expression, @es[if], that tests
if the value is @es[0] or not.

For a fuller explanation of these features and how they
behave, start with @citet[compiling-esterel]'s book
@italic{Compiling Esterel}, especially the first two chapers.
The semantic rules in @figure-ref["fig:reduction"] also provide
more details on how these constructs work.
