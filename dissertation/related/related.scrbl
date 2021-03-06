#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt")

@title[#:tag "related" #:style paper-title-style]{Related Work}

This section gives existing work related to the Constructive
Calculus. Most of this work is other Esterel semantics. In
addition there are some related works on the development of
calculi in general.

@section{Other Esterel semantics}

To show why a new semantics for Esterel contributes to the
existing work on Esterel, this section covers some existing
semantics, how they related to properties the calculus
captures, and how they capture the notion of
constructiveness. Many of the semantics in this section are
given the label ``Constructive''. This is because earlier
semantics for Esterel captured a slightly different language
which accepted more programs. Those semantics are called
``logical'', such as the original semantics, given in
@citet[esterel84]. While some more recent work such as
@citet[tardieu-deterministic] use a logical semantics, they
mostly have out of favor, and no modern Esterel
implementation uses them. As Logical Esterel is a slightly
different language than Constructive Esterel, I will not
discuss logical semantics futher here, but rather focus on the
constructive semantics, of which the Constructive Calculus
is one.


@subsection["Constructive Behavioral and State Behavioral Semantics"]

This section actually covers two semantics, the Constructive
Behavioral Semantics (CBS), and the State Behavioral
Semantics (SBS), as they are the same in all but one
respect. Both are given in @citet[esterel02].

These semantics largely consist of two metafunctions: @es[Must]
and @es[Can]. @es[Must] determines what code must be reached by
execution, and therefore what signals must be emitted. @es[Can]
determines what code might be reached, walking the causality graph and pruning branches that
cannot be reached, and is used to set signals to absent.
Constructive programs are ones in which all signals in the
program either @es[Must] or Cannot be emitted, and non-Constructive programs have
signals which fall into neither set.

CBS tracks the state of pauses via an administrative
reduction, reducing the program to one which will resume
from the appropriate points. SBS does the same, but instead
of rewriting the program it
decorates @es[pause] statements to see which ones were reached,
and uses these decorations to figure out where to resume. In
essence, these reductions propagate the information
from @es[Must] and @es[Can].

These semantics both give a syntactic evaluator for Esterel:
that is they give a function that gives the final result of
several instants of execution. They are not equational
theories.
These semantics, as given in @citet[esterel02], only handle Pure Esterel.

@subsection["Constructive Operational Semantics"]

The Constructive Operational Semantics (COS), in some sense,
provides a bridge between the SBS and an actual
implementation of Esterel. It replaces the @es[Must] metafunction
with a reduction relation (which also doubles as the
administrative reduction relation from the SBS). The core
idea here is that the reduction relation represents running
the program, and if something runs then it must happen.

In the COS, non-constructive programs are ones which
get stuck during execution, e.g. programs that cannot reduce
further and are not in a fully executed state. In
general, this is because the reduction cannot make progress without
executing some conditional, but the value of the signal
being conditioned on is unknown and cannot be set to absent.
This approach inspired how the Constructive Calculus handles constructiveness.

Like the CBS and CSS, the COS gives defines a syntactic
evaluator for Esterel, and is
not an equational theory. The COS is defined on all of Kernel Esterel.

@subsection["Circuit Semantics"]

The circuit semantics gives meaning to Esterel programs by
transforming them into circuits. This works by
transforming the control flow part of Esterel programs into
a dataflow problem where the data is encoded as power
flowing down a wire. This is then combined with the original
dataflow (e.g. signals) to give a full circuit. In
essence, the circuit semantics treats the causality
graph as a dataflow problem in the domain of circuits. A
@es[pause]s is encoded as a register which passes on whether or
not control reached a given point onto a future instant.

There are multiple circuit semantics.
@citet[optimizations-for-esterel-programs-thesis] splits the
program into two circuits, the Surface, which handles the
first instant a term is reached, and the Depth which handles
future instants. Whether or not the Surface or Depth circuit
is reached is controlled by the state of the registers
within those terms.

The circuit semantics I prove the calculus
equivalent to comes from @citet[esterel02], which is
based on the original circuit compiler from  @citet[esterel-circuit-cannon].
This compiler is discussed in depth in @secref["just:sound:compiler"].

In both semantics, the constructivity of Esterel
programs is transformed into the constructivity of
circuits@~cite[shiple-constructive-circuit]: an Esterel program
is constructive on some inputs if and only if all wires in its circuit
always settle to a single value in a bounded amount of
time. Just as with causality graphs, circuits are
non-constructive if some cycle in the circuit
demands a value be settled on for some wire, and the value for that wire value
depends on the state of the cycle.

The circuit semantics allow for local reasoning about
equality between programs.
It also provides an evaluator, through circuit
simulation. In addition circuit semantics
can be used to prove equivalences between programs,
as we have a computable equality relation between circuits.
However its reasoning is non-syntactic: the
transformations done to a circuit may not result in a new
circuit that can be transformed back into an Esterel
program, and even when they can be, the reasoning used to
explain why the circuit can be transformed in that way might
not map cleanly back to Esterel. Therefor,
it is not an equational theory. The circuit semantics
in @citet[esterel02] is defined on only pure Esterel. The circuit semantics in
@citet[optimizations-for-esterel-programs-thesis] is extended to handle
a host language.

@subsection["The Axiomatic Semantics"]

@citet[tini-axiomatic] gives two semantics. The first
is a labeled transition system that gives an evaluator for Esterel programs,
and the second is a series of logical axioms
which give an equality relation for Esterel programs, which they call
the Axiomatic Semantics. Of all the semantics presented so
far, these axioms are the closest to the goal that I have,
as it is an equational theory. However it
is built from fundamentally different techniques,@note{For instance, their
 notion of equality is based on bisimulation, whereas mine is based on
 contextual equivalence.} and it is not adequate to define an evaluator for Esterel.
This is because it cannot reason about @es[emit]s, as it lacks the control
variable my calculus adds. However it is much stronger in other
respects: in fact it is complete modulo bisimilarity on constructive programs. Adding
the axioms of the Axiomatic Semantics to the Construtive Calculus would result in a much more
powerful reasoning framework. The Axiomatic Semantics only handles Pure Esterel.


@subsection["The Color Semantics"]

@citet[color-semantics] gives a a microstep semantics
which I call here the Color Semantics.@note{This is called the ``Microstep semantics'' by
@citet[color-semantics]. I use a different name here to avoid confusion with
other microstep semantics like the COS.}
It replaces both Must and Can
with colors that propagate throughout the program, mimicking how @es[1] and @es[0]
propagate through circuits. The control variables of the constructive
calculus are based off this.
The Color semantics is computationally adequate, and is not
an equational theory. The Color Semantics handles only  Pure Esterel.

@subsection["Quartz"]

Quartz@~cite[quartz] is a variant of Esterel embedded into
the interactive theorem prover HOL@~cite[HOL]. Quartz is
defined by a transformation to a set of control flow
predicates and guarded commands. The full semantics is given
by the conjunction of the logical formula these define. This
allows properties of Quartz programs to be verified by both
model checking and theorem proving using HOL. The generation
of the guarded commands used for defining dataflow requires
knowledge of the precondition for that command, which
requires knowledge about the context. Like the circuit semantics,
this means it is not an equational theory, but it still can
prove equivalences between program using the underlying
model it maps programs to. It is adequate, and in fact can be used
for verified code generation.
Quartz handles host language data, and
also extends Kernel Esterel with forms such as
delayed emission and non-deterministic choice.

@section{Circuits}

The handling of cyclic circuits is derived from the seminal
work of @citet[malik-circuit]. It uses the extensions for registers
given by @citet[shiple-constructive-circuit], which have been proven correct by
@citet[constructive-boolean-circuits]. The notion of constructivity used here
is what @citet[shiple-constructive-circuit] call strong constructivity, as Malik's
original definition of constructivity only demanded that interface wires be non-@es[⊥],
and allowed internal wires to take on any value.

@section{Calculi}

The Constructive Calculus for Esterel draws heavily from the State
Calculus@~cite[felleisen-hieb]---specifically in the usage
of local maps and evaluation contexts@~cite[felleisen-friedman]
to track the state locally.

This calculus is the second draft, the first introduced in @citet[florence-2019].
That calculus, however, was not constructive, as it allowed for local
rewrites which could bypass signals who's value was not yet known. The
local control variables @es[A] was introduced to solve this issue.
