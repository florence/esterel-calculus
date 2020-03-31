#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          "../lib/misc-figures.rkt"
          esterel-calculus/redex/model/deps
          esterel-calculus/dissertation/lib/pict
          scriblib/figure
          pict/code
          pict
          ppict
          syntax/parse/define
          (for-syntax racket/base))

@(define-simple-macro (code+graph {~alt
 {~optional {~seq #:ignore-start? qq}}
 {~once e}} ...)
   (with-bar (es e) (flow/pict 'e #:ignore-start? (~? qq #t))))

@(define (with-bar p1 p2)
   (hc-append
    p1
    (vline 30 (max (pict-height p1) (pict-height p2)))
    p2))

@title[#:style paper-title-style #:tag "background-esterel"]{Esterel}

This dissertation will not focus on the Full Esterel
language. There are other, better primers on that such as
@cite/title[compiling-esterel]. Instead I will focus on
Kernel Esterel@~cite[esterel02]. Kernel Esterel is a small
subset of Esterel in which, for the most part, Full Esterel
is trivially macro expressible. It's grammar
is: @centered[lang/state] The Kernel I am using is adapted
from the Kernel used in Section 2.2 of
@cite/title[compiling-esterel]. The translation from Full
Esterel to this Kernel is given in appendix B of that book.

@section["Pure Esterel"]

The first three lines of the grammar give the subset of
Esterel called Pure Esterel. Pure Esterel defines a
``core'' to the language which we can use to introduce
and examine the important concepts in the language. Pure
here refers just this fragment of Esterel only contain
Esterel terms, without reference to a host language, not
to a fragment of Esterel without state.

@bold{Instants} Esterel divides computation in instants.
Each instant begins in response to some external stimuli,
and each instant is atomic with respect to the outside world: its inputs
may not change, nor may its outputs or internal state be
observed until the instant is completed.

In addition code within each instant can be thought of as
running in zero time. That is to say: to maintain
deterministic concurrency Esterel does not allow for the
program to observe the order in which expressions are run.
Without such a total ordering being visible, there isn't
really an internal sense of "time" to an instant in Esterel.

The lack of an internal sense of time combined with the fact that the program doesn't run at
all outside of instants means that the full execution of an
instant is the only notion time in Esterel. Each instant
represents one tick forward on a global, discrete
clock.@note{ It should be noted that each instant may not
 match up to physical time. The outside environment can
 impose arbitrary delays between instants as each instant is
 only run on the outside world's request.} In fact, this
external-only view time is what gives ``instants'' their
name. We think of every computation in Esterel taking zero
time, and so the entire instant completes in zero time.

@bold{Signals} Signals, declared with @es[(signal S p)],
give local broadcast communication channels which carry one
bit of information: if the signal is present or absent. A signal
may only have one value in a single instant. 

The conditional form @es[(present S p q)] conditions on if a signal is present or
absent, running @es[p] or @es[q] respectively.

The form @es[(emit S)] sets a signal to present. There is no
way to explicitly set a single absent. This asymmetry ties
into Esterel's deterministic concurrency and the fact that
signals can only obtain one value in an instant. A signal is
present if and only if it has is emitted in the current
instant. A signal is absent if and only if it is not
emitted and @italic{cannot} be emitted in the current
instant. The exact meaning of cannot is discussed in
@secref[ "back:esterel:cannot"].

@bold{Composition} Esterel terms can either be composed
concurrently---@es[(par p q)]---or
sequentially---@es[(seq p q)]. @es[seq] behaves, more or
less, like the sequential composition from familiar
languages. @es[par] is akin to a fork/join construct: it
determines the state of both of its branches and only
finishes execution if they both have.

@bold{Pausing} The @es[pause] form tells the program to stop the
instant at that point, and resume from that point in the next
instant. If both branches of a @es[par] pause, the next
instant resumes at both, concurrently. Another way to see
this is that @es[pause] is the only expression in Esterel
which takes time, and it always takes exactly one unit of
time.

@bold{Non-local control flow} There are two forms of
non-local control in Esterel. The first is a form of named,
upward jumps, in the form of @es[(trap p)] and
@es[(exit n)]. The @es[(exit n)] jumps to the @es[n]th
outermost trap (counting from zero). This form cooperates
with @es[(par p q)] such that if both branchs of the
@es[par] @es[exit], the outer most trap is jumped to. For
example @es[(par (exit 0) (exit 3))] will jump to the 4th
outer most @es[trap]. If one branch @es[exit]s, and the
other either @es[pause]s or completes, the whole @es[par]
@es[exit]s, preempting the non-@es[exit]ing branch once it
has paused. For example both
@es[(par (seq (emit S) pause) (exit 3))] and
@es[(par (seq (emit S) (exit 0)) (exit 3))] emit the signal
@es[S] and jump to the fourth outermost trap. I refer to
traps as ``named'' upward jumps because the numbers in
@es[exit] are really just de Brujin indices for names that appear in
Full Esterel. This representation is more convenient to
work with in a semantics.

The other kind of non-local control is @es[(suspend p S)].
In the first instant a suspend is reached, the suspend
behaves like @es[p]. However in all future instants where
the instant would resume in @es[p], it only resumes when
@es[S] is absent. If @es[S] is present, then the whole form
pauses, continues in the next instant (following the same rules).

@bold{Loops} The final construct in Pure Esterel is
@es[(loop p)]. It continually repeats @es[p] in an infinite
loop. However, because signals can only take on one value
per instant in Esterel, any loop which both begins and ends
in a single instant will loop forever, causing the instant
to never terminate. Therefore Esterel requires that all
loops either @es[pause] or @es[exit] each
instant. This ensures that each instant, in fact, terminates.

@subsection[#:tag "back:esterel:schizo" "Schizophrenia"]

Reincarnated and Schizophrenic variables are a problem
related to improper handling of variables and loops in
Esterel semantics, particularly when compiling to circuits.
Chapter 12 of @cite/title[esterel02] goes into this in
detail. Here I will only give a cursory overview of this
issue.

@as-index{Reincarnationj} occurs when loop which contains
the declaration of a variable or signal completes execution
and restarts in the same instant. This results in two instances of
the same variable, and the variable is said to be reincarnated.

@as-index{Schizophrenia} occurs when a reincarnated variable
takes on a different value during the two instances of the
loop body. This can seem at odds with the statement that ``A
signal may only have one value in a single instant'', and is
why these two instances must be though of as separate
variables to have a correct semantics. For instance, circuit
compilers must duplicate part of all of a loop body to
ensure that there are, in fact, two distinct variables.

@section["The host language and Esterel"]

The last line of the grammar at the start of @secref["background-esterel"] extends Pure Esterel with forms
which can track values, in addition to Boolean signals.

However Esterel does not have any notion of value: Instead
it borrows the outside world's notion of value. That is,
Esterel is meant to be embedded in another programming
language. That language controls when instants in
Esterel run, and communicates with Esterel using
signal presence and is own values. In turn values in Esterel
are computed using the host language's expressions, which may refer to variables bound by Esterel.
Values can be stored in either host language or shared variables.

@bold{Host Language Variables} Host language variables are like traditional programming
variables. They are declared and initialized by the
@es[(var x := e p)] form, and written to with the
@es[(:= x e)] form. Kernel Esterel also includes another conditional
form @es[(if x p q)], which conditions on the host languages
notion of truth. To maintain deterministic concurrency
these variables must be used in a way where
concurrent updates are not observable: for example
by never using them in multiple branches of an @es[par].
How exactly (and if) this is guaranteed depends on the Esterel
implementation.

@bold{Shared Variables} Shared variables give concurrent access
to state that may be shared between branches of a @es[par], such
that Esterel guarantees deterministic concurrency. Shared variables are
declared with @es[(shared s := e p)] and mutated with
@es[(<= s e)]. To ensure determinism shared variables have
two restrictions. The first is that they must be paired with
an associative, commutative, combination function which will
be used to combine multiple writes to the variable in a
given instant, to ensure the order of writes is not visible. The
second is that a host language expression referring to a
shared variable cannot be evaluated unless no further writes
to that shared variable can occur in a given instant. This
ensures that only one value for that variable is observed by
the program in a given instant. Tracking if a shared
variable cannot be written anymore in the current instant
uses the same mechanism as determining absence for a signal.@note{In fact,
 in Full Esterel shared variables and signals are
 combined into a single concept: the value carrying signal,
 which pairs the absence/presence of a signal with a value
 that is computed the same way as with a shared variable. In
 Kernel Esterel value carrying signals are represented as a
 signal paired with a shared variable.}

In the calculus I present here, I will assume a host language
which always use the combination function @es[+], and that
the host language only contains numerical literals, and @es[+]
and @es[-].

@section[#:tag "back:esterel:cannot" "Constructive programs"]

What is the mechanism used to determine if a signal can be
set to absent? Specifically, what kind of reasoning can we
perform when showing that a signal cannot be emitted?

To show that a signal is emitted or that it cannot be
emitted we must build a chain of cause and effect which
either shows that  program Must reach an emit (setting the
program to present) or shows the program Cannot reach an
emit (setting the signal to absent).

For a first example, consider the program:

@centered[(code
           (signal S1
             (par
              (present S1
                       pause
                       nothing)
              (emit S))))]

In this example, we can say that the signal @es[S1] is emitted, because we can establish the following
chain of cause and effect:

@centered[(deps
           (signal S1
             (par
              (present S1
                       pause
                       nothing)
              (emit S1))))]

We can read this graph as "emitting the signal S on the last line
might cause the conditional to take its true branch". We get
this interpretation by starting at the entry points of the
causality graph and walking forward. In this case the only
entry point to the graph is the @es[(emit S1)]. It points to
the conditional that branches on @es[S1], which we can
interpret as "this emit running or not running can cause
this conditional to take its left or right branch". Because
the @es[(emit S1)] is at the entry point to the graph we can
also conclude that the emit must run. Therefore it must
cause the conditional to take its then branch. This
reasoning, where we say "the @es[(emit S1)] must happen,
therefor the conditional must take this branch" can also be
interpreted as "the @es[emit] must run before the
@es[present]", because we are saying that it must cause the
present take some action. This prescribing of order to an
instant, which is supposed to be timeless, may seem odd.
This is because the order we get out of a causality graph is a
partial order: there isn't really an internal sense of total
time, but rather there are just several possible chains of
cause and effect that lead us to a single result.
Anything that does not violate the partial ordering goes:
including true parallelism.@note{To quote Gérard Berry:
 ``Everything happens at the same time, just in the right
 order.''}

Now consider this adjustment to the prior program, and its
causality graph:

@centered[(deps
           (signal S1
             (present S1
                      pause
                      nothing)))]

When we walk this causality graph from its entry points as
before, we immediately run into the conditional without
hitting any @es[(emit S1)]s. In addition if we keep
walking forward, neither branch
can emit @es[S1] either. From this we can safely conclude
that nothing can cause @es[S1] to be emitted be emitted, therefore
it cannot be emitted, therefore it is absent.

Notice that the asymmetry in the syntax---that we have a form
for setting a signal to present but not for setting to a signal
absent---leads to an asymmetry in our reasoning. To reason
about the presence of a signal we consider the causality graph up to the
conditional and what it must do. To reason about absence of a signal we
look at the entire graph and reason about what it cannot do.
However the reasoning about what it cannot do is, itself,
restricted by causality. Consider the program in
@figure-ref["first graph"], which is the same as the
previous one but with the pause replaced by an emit. To make
the graph easier to read it has been pulled out into a
separate image. The darker edges@note{Blue if printed in color.} describe the parts of
the causality graph that come from the control of the
program. The lighter edges@note{Pink if printed in color.} come from the data flow. Conditions are
represented as nodes labeled @tt{
 (? S)}, and their branches are labeled @tt{T} and @tt{F}, for the then and else branches respectively.
Other control flow edges are labeled
with @tt{n} if they pass control on in this instant, @tt{p}
if they pass control on in the next instant (e.g. a
@es[pause]), or a number if they exit with that code.


@figure["first graph"
        "A program with a separate causality graph"
        (code+graph
         (signal S1
           (present S1
                    (emit S1)
                    nothing)))]

As before, we
cannot set @es[S1] to present, as there is no emit that must
be reached before the conditional. However we cannot
set @es[S1] to absent either, as the emit in the then branch might still be reached!
One might assume that  we could analyze
the conditional as if @es[S1] were absent  looking at only the else
branch, as we know it cannot be present. However this would amount justifying @es[S1] being absent
based on the assumption that it was absent. Such self
justification doesn't leave a clear chain of causes which
result in showing the signal is absent: one of the
reasoning steps is just a guess. Esterel considers programs like this one,
where some signals cannot be set to either absent or present, to be illegal. Such a programs are either rejected statically or raise a runtime
error, depending on the Esterel implementation. Programs like this are called non-constructive.@note{
 This comes from the analogous lack of self-justified reasoning
 in a constructive logic.}

Another way of seeing this is observing that causality graph
for that program has a cycle in it: in a timeless world the
emit in the then branch could cause the conditional to make
a particular choice, which could cause the emit to be
reached. Such a cycle in causality does not make sense (and
does not give us even a partial ordering on events).

However causality cycles are not always nonsense.
In some cases a cycle does not result in a
non-constructive program because prior steps in our
reasoning may allow the cycle to be broken. Consider the program in @figure-ref["good cycle"].

@figure["good cycle"
        "A constructive program with a causality cycle"
        (code+graph
         (signal S1
           (signal S2
             (present S1
                      (present S2
                               (emit S1)
                               nothing)
                      nothing))))]

This program has a causality cycle, because the condition
@es[S1] might cause @es[S1] to be emitted. However, we can
also see that no emit for @es[S2] is reachable in the
causality graph, which means we can set it to absent. But
now that we have justified setting @es[S2] to absent, we can
justify ignoring any code in that conditionals then branch.
This causes the @es[(emit S1)] is unreachable, so we can cut
any edges in the causality graph leading to or from it. Now
we have a causality graph with no cycles that never
reaches an @es[(emit S1)], so we can set @es[S1] to absent.

Causality graphs also interact with
@es[pause]. Because @es[pause] ends an instant (and causes
the next instant to pick up from the pause), and the single
value restriction for signals only pertains to a single instant,
@es[pause]s essentially cut the causality graph, splitting it in two:
one for the instants before the pause is reached, and one for the ones
after. For example consider the program and graph in @figure-ref["pause1"].
This program will emit @es[S1], then pause. In the next instant
it will emit @es[S2]. This is represented in the graph by introducing
a new node @es[start], which has a choice: if it is starting this program
fresh it will go down the path which emits @es[S1], and @es[pause]s, terminating
that instant. If it is an instant where it's resuming for the @es[pause], it will take
the right hand branch and emit @es[S2].

@figure["pause1"
        @list{A simple graph split by a @es[pause].}
        (code+graph
         #:ignore-start? #f
         (signal S1
           (signal S2
             (seq (emit S1)
                  (seq pause
                       (emit S2))))))]


We can us this to see how pause can break what might
otherwise be causality cycles. Look at the differences in
the programs and graphs in @figure-ref["unpause2"] and
@figure-ref["pause2"]. In the first example when we walk the
graph from start to finish we find that we need the value
for @es[S1] first, but after that condition we might emit
@es[S1] so we cannot set it to absent. This cycle renders
the program non-constructive. But in the second example,
where the last @es[nothing] is replaced by a @es[pause] we have
a different graph with no cycles! Because the emit cannot
happen in the same instant as the condition (represented by
the choice of where @es[start] goes) this program is
constructive, and its graph is acyclic.

@figure["unpause2"
        @list{A cycle}
        (code+graph
         #:ignore-start? #f
         (signal S2
           (seq (present S1 nothing nothing)
                (seq nothing
                     (emit S1)))))]

@figure["pause2"
        @list{A cycle cut by a @es[pause].}
        (code+graph
         #:ignore-start? #f
         (signal S2
           (seq (present S1 nothing nothing)
                (seq pause
                     (emit S1)))))]

@subsection["Must/Cannot and Present/Absent"]

The description of constructivity in terms of program graphs
and what Must and Cannot happen can actual give a complete
semantics for Pure Esterel. This is described by the
Constructive Behavioral Semantics @~cite[esterel02], which
defines Esterel inters of two functions: @es[Can] and
@es[Must]. We can think of what these functions do in terms
of the chart in @figure-ref["back:lattice"]. The upper left
corner of this diagram, labeled @es[1], corresponds to a
portion of the program being executed, and to a signal being
present. The bottom right, labeled @es[0], corresponds to a
portion of the program not being executed and to a signal
being absent. The upper right corner, labeled @es[⊥]
corresponds to a portion of the program being in an unknown
state. The lower left is never realized.


@figure["back:lattice"
        "Must/Can Lattice"
        (let ()
  (define width 150)
  (define height 150)
  (define (debase x)
    (inset x 0 (* -.2 (- (pict-height x) (pict-descent x)))))
  (define (scl x)
    (debase
     (scale-to-fit
      x
      (* .4 width)
      (* .4 height))))
  (define v-line (vline 0 height))
  (define h-line (hline width 0))
  
  (define chart
    (ppict-do
     (blank width height)
     #:go (coord 0 .5)
     v-line
     #:go (coord .5 .5)
     v-line
     #:go (coord 1 .5)
     v-line
     #:go (coord .5 0)
     h-line
     #:go (coord .5 .5)
     h-line
     #:go (coord .5 1)
     h-line
     #:go (grid 2 2 1 1)
     (tag-pict (scl @es[1]) 'one)
     #:go (grid 2 2 1 2)
     (strike-for (* .5 width) (* .5 height))
     #:go (grid 2 2 1 2)
     (strike-for (* .5 width) (* .5 height) 3 'other)
     #:go (grid 2 2 2 1)
     (tag-pict (scl @es[⊥]) 'bot)
     #:go (grid 2 2 2 2)
     (tag-pict (scl @es[0]) 'zero)))
  (define w/labels
    (panorama
     (hc-append
      10
      (vc-append
       (cc-superimpose
        (blank 0 (/ height 2))
        (text "Can"))
       (cc-superimpose
        (blank 0 (/ height 2))
        (text "Cannot")))
      (refocus
       (vc-append
        10
        (hbl-append
         (cc-superimpose
          (blank (/ width 2) 0)
          (text "Must"))
         (cc-superimpose
          (blank (/ width 2) 0)
          (text "May Not")))
        chart)
       chart))))
  (app
   w/labels
   (arrow/tag
    10
    #:line-width 3 'bot lc-find 'one rc-find)
   (arrow/tag
    10
    #:line-width 3 'bot cb-find 'zero ct-find)
   ))]

Every edge in the program graph begins in the corner of the
chart labeled @es[⊥], representing that it could be
executed, but might not be. As we execute the program, any
control edge can be moved to the @es[1] corner (It both Must
and Can happen), if @italic{all} of it's incoming edges are
@es[1]. Conversly, a control edge can be set to @es[0] if
@italic{any} of it's incoming edges are @es[0]. Note that
this means that the edges leading from @es[start]
automatically have @es[1]'s as they have no incoming edges.
Conversely a Data edge can be set to @es[1] if @italic{any}
of it's incoming edges are @es[1], but can only be set to
@es[0] if @italic{all} of it's incoming edges are @es[0].
This corresponds to control edges being linked by an
extension of @es[and] with @es[⊥], and data edges being
linked to by a similar extension of @es[or]. This is
discussed in more detail in @secref["background-circuits"]
and @secref["just:sound:compiler"] as this leads directly to
the circuit semantics of Esterel.

The Must and Cannot corner in the diagram is not reachable,
as it is a logical contradiction. No consistent and sound
semantics should be able to put programs in this corner.
This will motivate some of the design decisions of the
Calculus.

It should also be noted that this description leads to a
kind of asymmetry between the Must and Cannot corners. The
Must corner can be reached only if there is a chain of
@es[1]'s leading form the top of the program, as the only
control node that has zero incoming edges is @es[start]. The
Cannot corner however can be reached without a connection to
the top of the program, as any signal with no @es[emit] can
automatically get a @es[0]. This leads to an odd fact: Must
is non-local, but Cannot is local. Any program can be put
into a context where is wont be executed, therefor Must
requires knowledge about where the top of the program is.
However if something Cannot happen, then no context can make
it happen. This asymmetry will show up several times in the design
of the Calculus.