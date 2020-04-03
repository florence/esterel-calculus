#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt")

@title[#:tag "related" #:style paper-title-style]{Related Work}

@section{Esterel}

The canconical citation for Esterel is @citet[esterel92].

@section{Other Esterel semantics}

To show why a new semantics for Esterel contributes to the
existing work on Esterel, this section covers some existing
semantics, how they related to properties the calculus
captures, and how they capture the notion of
constructiveness.@note{Many of the semantics in this
 section are given the epithet ``Constructive''. This is
 because earlier semantics for Esterel captured a slightly
 different language which accepted more programs. Those
 semantics are called ``logical'', but have fallen out of
 favor, and no modern Esterel implementation uses them.}

@section["Constructive Behavioral and State Behavioral Semantics"]

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
several instants of execution. They do not provide
for local reasoning about equality between program fragments,
however.
These semantics, as given in @citet[esterel02], only handle Pure Esterel.

@section["Constructive Operational Semantics"]

The Constructive Operational Semantics, in some sense,
provides a bridge between the SBS and an actual
implementation of Esterel. It replaces the @es[Must] metafunction
with a reduction relation (which also doubles as the
administrative reduction relation from the SBS). The core
idea here is that the reduction relation represents running
the program, and if something runs then it must happen.

In this semantics, non-constructive programs are ones which
get stuck during execution, e.g. programs that cannot reduce
further and are not in a fully executed state. In
general, this is because the reduction cannot make progress without
executing some conditional, but the value of the signal
being conditioned on is unknown and cannot be set to absent.
This approach in fact inspired how the Calculus handles Esterel.

Like the CBS and CSS, the COS gives defines a syntactic
evaluator for Esterel and does not afford for local reasoning about
equality between programs. The COS is defined on all of Kernel Esterel.

@section["Circuit Semantics"]

The circuit semantics gives meaning to Esterel programs by
transforming them into circuits. This works by
transforming the control flow part of Esterel programs into
a dataflow problem where the data is encoded as power
flowing down a wire. This is then combined with the original
dataflow (e.g. signals) to give a full circuit. In
essence, the circuit semantics treats the causality
graph as a dataflow problem in the domain of circuits.
@es[pause]s are encoded as registers which pass whether or
not control reached a given point onto a future instant.

There are multiple circuit semantics.
@citet[optimizations-for-esterel-programs-thesis] splits the
program into two circuits, the Surface, which handles the
first instant a term is reached, and the Depth which handles
future instants. Whether or not the Surface or Depth circuit
is reached is controlled by the state of the registers
within those terms.

The circuit semantics I prove the calculus
equivalent to comes form @citet[esterel02]. It transforms
the single control wire used in
@citet[optimizations-for-esterel-programs-thesis] into four
control wires: GO, which carries a 1 when the surface would be
reached; RES, which carries a 1 when the Depth would be
reached (e.g. resumed); SUSP which carries a 1 when an outer
@es[suspend] from would suspend execution of this term
instead of resuming it; and KILL, which carries a 1 when a control jump (e.g. @es[exit]) would
cause the term to abort instead of being resumed.

In both semantics, the constructivity of Esterel
programs is transformed into the constructivity of
circuits@~cite[shiple-constructive-circuit]: an Esterel program
is constructive on some inputs if an only if all wires in its circuit
always settle to a single value in a bounded amount of
time. Just as with causality graphs, circuits are
non-constructive if some cycle in the circuit winds up
demanding a value be settled on for some wire, who's value
depends on the state of that cycle.

The circuit semantics allow for local reasoning about
equality between programs, as circuits are well understood.
It also provides an evaluator, through circuit
simulation. However its reasoning is non-syntactic: the
transformations done to a circuit may not result in a new
circuit that can be transformed back into an Esterel
program, and even if it could be, the reasoning used to
explain why the circuit can be transformed in that way might
not map cleanly back to Esterel. The circuit semantics
in @citet[esterel02] is defined on only pure Esterel. The circuit semantics in
@citet[optimizations-for-esterel-programs-thesis] is extended to handle
a host language.

@section["The Axiomatic Semantics"]

@citet[tini-axiomatic] gives two semantics. The first
is a labeled transition system that gives an evaluator for Esterel programs,
and the second is a series of logical axioms
which give an equality relation for Esterel programs, which they call
the Axiomatic Semantics. Of all the semantics presented so
far, these axioms are the closest to the goal that I have. As a set of
axioms over programs it is local and syntactic. However it
is built from fundamentally different techniques,@note{Their
 notion of equality is based on bisimulation, whereas mine is based on
 Contextual Equivalence.} and it is not adequate to define an evaluator for Esterel.
This is because it cannot reason about @es[emit]s, as it lacks the control
variable my calculus adds. However it is much stronger in other
respects: in fact it is complete modulo bisimilarity. Adding
the axioms of this semantics to the calculus would result in a much more
powerful reasoning framework. This semantics only handles Pure Esterel.


@section["The Color Semantics"]

What I am calling the color semantics is an as-yet unpublished by Lionel Rieg.
It is a microstep semantics which replaces both Must and Can
with colors that propagate throughout the program. This
propagation is designed to be close to how @es[1] and @es[0]
propagate through circuits. The control variable of this
calculus are based off of the Colors of the Color calculus.
The Color semantics is syntactic and adequate. However it does
not allow for local transformations. This semantics only handles Pure Esterel.

@section["Quartz"]

Quartz@~cite[quartz] is a variant of Esterel embedded into
the interactive theorem prover HOL@~cite[HOL]. Quartz is
defined by a transformation to a set of control flow
predicates and guarded commands. The full semantics is given
by the conjunction of the logical formula these define. This
allows properties of Quartz programs to be verified by both
model checking and theorem proving using HOL. The generation
of the guarded commands used for defining dataflow requires
knowledge of the precondition for that command, which
requires knowledge about the context. This limits the amount
of local reasoning in the semantics. It is also not a
syntactic semantics. It is adequate, and in fact can be used
for verified code generation.
This semantics handles host language data, and
also extends Kernel Esterel with forms such as
delayed emission and non-deterministic choice.

@section{Circuits}

malik & shipple
mendler
