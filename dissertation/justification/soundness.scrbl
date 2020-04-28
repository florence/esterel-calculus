#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          (only-in
           "../lib/circuit-diagrams.rkt"
           emit-pict nothing
           compile-def
           esterel-interface)
          "../lib/proof-extras.rkt"
          (only-in "../proofs/proofs.scrbl")
          (only-in "../notations.scrbl")
          (only-in scribble/manual racket)
          scriblib/figure
          racket/match)


@title[#:style paper-title-style  #:tag "just:sound"]{Justifying Soundness}

@proof-splice["soundness"]

The proof is given in the appendix as
@proof-ref["soundness"]. To pick the statement apart, it
says that if two terms are @es[≡], and those terms have
correct binding, then, when we restrict ourselves to looking at a
single instant, the compilation of those circuits is
@es[≃^circuit].

This proof proceeds by induction over the structure of the
equality relation @es[≡]. Thus, the majority of the work in
the proof goes into showing that it holds for each rule of
@es[⇀]. Each rule in @es[⇀] is proved sound, in
general, by induction on @es[p-pure].
The base cases have concrete circuits, so in general
the base cases are proven by the circuit solver.

@section[#:tag "just:sound:lemma"]{Important lemmas}

This section will discuss the proof sketches of the most interesting or
informative lemmas needed to prove soundness of the various
rules of @es[⇀]. Many of the lemmas are trivial or uninformative, and so will not be discussed here.
The interested reader can find them in appendices A.2 and A.3.

A first informative proof to look at is the proof that @rule["trap"] is sound:
@proof-splice["trap"]

The full proof may be found at @proof-ref["trap"]. The first
thing to note is that this proof does not require the
premise that we are in the first instant, or correct binding. Many of the
equations do not touch @es[pause] or binding forms, and therefore are not
sensitive to instants or binding. This proofs proceeds by cases on
the structure of @es[stopped]. The case where
are @es[(= stopped nothing)] can just invoke the solver:@note{@racket[harp] is the implementation of @es[harp].}
@check[(assert-same
        (compile-esterel (term (trap nothing)))
        (compile-esterel (term (harp nothing))))]
We can also see that these two are the same if we draw out the circuits on paper: they give us the same graph!
The last case is @es[(= stopped (exit n))].
In this case we do cases on @es[harp].
In the first of these cases we have @es[(= stopped (exit 0))], we have a concrete circuit, and so can use the solver again.
In the last case we have @es[(= stopped (exit n))], where @es[(> n 0)]. Again if we draw
this out we find that we get the exact same graph.

The next proof of interest is the proof that @rule["emit"] is sound.
This proof is more complex because it must deal with both evaluation contexts
and environments.
@proof-splice["emit"]

The full proof is given in @proof-ref["emit"]. This proof
proceeds by induction over @es[E-pure]. The base case is
rather trivial: when @es[(= E-pure hole)] the two circuits
look identical, as the @es[1] from the @es[GO] wire is
directly connected to the @es[S] wire. The inductive case is
more interesting: the proof uses the idea that evaluation
contexts obey the property that
in @es[(compile (in-hole E-pure p-pure))], the @es[GO] and
signal wires from the top of the term are passed, unchanged,
to the subcircuit for @es[(compile p-pure)]. This is stated formally with these two
lemmas:
@proof-splice["S-maintains-across-E"]
@proof-splice["GO-maintains-across-E"]

The full proofs of which are given in
@proof-ref["S-maintains-across-E"] and
@proof-ref["GO-maintains-across-E"]. Both lemmas follow
directly by induction on @es[E-pure] and the definition of
@es[compile]. These two lemmas together give that the
inputs of the subcircuit are unchanged by the context. The remainder of the
inductive case for @proof-ref["emit"] follows from the notion that the @es[So] wires are always
or'ed with each other, therefore a @es[1] in any subterm
leads to the overall signal wire being @es[1].

The last proof I will describe here is the proof for @rule["is-absent"]:
@proof-splice["is-absent"]

The full proof is given in @proof-ref["is-absent"]. This
proof is one of key proofs which requires the premise that
we are in the first instant. This is because this proof
relies on @es[Can], which assumes that it is in the first
instant. Other variations of @es[Can], such as those from
the State Behavioral Semantics@~cite[esterel02] or the
Constructive Operation
Semantics@~cite[optimizations-for-esterel-programs-thesis]
drop this assumption by reflecting register state back in
the syntax of the program.

This proof is essentially a chaining of several other lemmas. As
with @proof-ref["emit"], @proof-ref["S-maintains-across-E"] and @proof-ref["GO-maintains-across-E"]
are used to shed the evaluation contexts in the rule. From there the proof mostly follows from the following
lemma:
@proof-splice["Can-S-is-sound"]

To understand this proof statement, I must explain a little bit of notation. The phrase
@es[(binds (compile p-pure) θ)] exists to tie the syntactic world of Esterel to the circuit world.
It, in essence, states that the knowledge contained in the map @es[θ] also holds when reasoning about the circuit.
Formally, it is defined as:

@extract-definition["binds"]

With this in hand we can interpret
@proof-ref["Can-S-is-sound"]: If we restrict our view to the
first instant, and the environment given to @es[Can] is
valid with respect to the circuit, then @es[Can] accurately
predicts when signal wires will be set to @es[0] (or rather,
the complement of @es[Can] accurately predicts this).

The proof of @proof-ref["Can-S-is-sound"] proceeds by
induction over the structure of @es[p-pure], following the
cases laid out by @es[Can]. The majority of this lemma
consists of tracing how the definition of can walks the
program, and compares that to the structure of the generate
circuit. In most cases the result follows fairly directly.
In the end there are two interesting cases: @es[signal] and
@es[seq]. The @es[signal] case in interesting only when the
bound signal is not in the result of @es[Can]. In this case
we must use our inductive hypothesis to show that the output
of the bound signal is @es[0], and use that to invoke our
inductive hypothesis to show that the goal signal is also
@es[0]. The @es[seq] case of @es[Can] relies on the return
codes. Thus we use an auxiliary lemma to reason about
those codes:
@proof-splice["Can-K-is-sound"]
This lemma is similar to @proof-ref["Can-S-is-sound"], except that it
tells us which return code wires must be @es[0]. The proof
of which is essentially the same as @proof-ref["Can-S-is-sound"].

These two lemmas also have counterparts for @es[Can-θ]:
@proof-splice["Can-rho-S-is-sound"]
@proof-splice["Can-rho-K-is-sound"]
However as @es[Can-θ] is essentially just repeated applications of the @es[signal]
case of @es[Can], these proofs are relatively uninteresting.

@section[#:tag "just:sound:changes" "Change the compiler for Soundness"]

The compiler used here differs from the compiler in @citet[esterel02].
Specifically the changes are the @es[KILL]
wire including the return codes, and the definition of the @es[LEM] and @es[REM] wires.
The old compiler broadcasts the @es[KILL] wires directly to the subcircuit.
Both of these definitions result in unsoundness under local rewrites
to the syntax of the program that should hold. Both of these changes were used in the Esterel v7 compiler, however
they have not yet been published anywhere.@note{The changes and
 come from personal communication with @|gerard|.}

The change to the @es[REM] and @es[LEM] wires can be
explained by noticing that we expect
@centered[@es[(≃^esterel (trap (par (exit 0) pause)) nothing)]]
as this circuit will always abort, and immediately catch the
@es[exit]. Therefore we want
@centered[@es[(≃^circuit (compile (trap (par (exit 0) pause))) (compile nothing))]]
to hold. However in this equivalence did not hold in the
@citet[esterel02] compiler, specifically in the case where
@es[(= GO ⊥)]. In that case both @es[LEM] and @es[REM] are
@es[⊥], causing @es[K2] to be @es[⊥]. However in the circuit
for @es[nothing], @es[K2] is defined to be @es[0]. The
Esterel v7 compiler handles this case correctly.

The change to the @es[KILL] wire can be seen by a similar
example. We expect
@centered[@es[(≃^esterel (par (exit 2) pause) (exit 2))]] for a similar
reason as before. As before, this means we want
@centered[@es[(≃^circuit (compile (par (exit 2) pause)) (compile (exit 2)))]]
to hold. With the @citet[esterel02] compiler, however, we are free
to let @es[KILL] be @es[0], even when @es[GO] is @es[1]. This means that in the second
instant the @es[pause] is selected. However there is no @es[pause] in @es[(exit 2)],
therefore its @es[SEL] wire must be @es[0]. The new compiler handles this correctly by
killing the other branch of the @es[par] even if the outer @es[KILL] wire is @es[0].

Note that these two issues both rely on both subcircuits
being simultaneously active at some point to trigger the change in
behavior. As @es[par] is the only case where two
subcircuits can be active simultaneously, this is the only
case that requires this special care.

It should be noted that equality violations above do not
constitute a bug in actual Esterel compiler implementations. In
actual compilers, if @es[GO] is @es[⊥], then the program
raise an error and the different in wire states cannot be
observed. In addition if an exit code is raised, then the
@es[KILL] wire will be set, as full programs must be closed
and therefore an external @es[trap] will catch the code and
set the @es[KILL] wire. Therefore, behaviorally at least,
the changes used here should not effect an actual Esterel
implementation.
