#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          "../lib/rule-figures.rkt"
          "../lib/cite.rkt"
          "../lib/circuit-diagrams.rkt"
          scriblib/figure
          pict)

@title[#:tag "final" #:style paper-title-style]{Future Work}

The constructive calculus presented here is the first calculus
for Esterel which captures both Constructivity and
which is Adequate. However, research is never complete---the
proofs do not cover the entire language, the handling of
@es[emit] makes the calculus somewhat weak, and there are
stronger compilation guarantees one might wish to have proven. This
section is meant to give a small starting point for any
ambitious researcher who wants to tackle these
problems.

@section[#:tag "future"]{Extending proofs to multiple instants, and guarding compilation}

Future work may wish to extend the proofs for the
Consistency, Soundness, and Adequacy of the Constructive
Calculus to multiple instants. This should be possible with
a tweak to the compilation of terms.

This tweak enforces an assumption that the compilation
function makes: that @es[GO] and @es[SEL] are mutually
exclusive. The circuits generated by @es[compile]
do not behave properly if this condition is not met: in essence
it is undefined behavior. This undefined behavior ruins many equalities that
should hold, as having both @es[GO] and @es[SEL] true simultaneously
can expose details of the internals of a term that are not observable in
Esterel, but are observable in the circuit.
Consider the equation:
@[centered
  (hc-append 15
             @es[(signal S1
                   (seq
                    (present S1 (emit S2) nothing)
                    (seq pause
                         (emit S1))))]
             @es[≃^esterel]
             @es[(signal S1
                   (seq pause (emit S1)))])]
These two programs should be @es[≃^esterel], as the signal
@es[S1] can never be emitted in the same instant
in which it is conditioned on. However consider their circuit
compilations: in the first program there will be a wire
@es[(= S2 (and GO S1))]. However in the compilation of the second term there will
be no @es[S2] wire, therefore it will be taken to be @es[0].
If, in the second cycle, @es[GO] is @es[1], (making it
@es[1] at the same time as @es[SEL]) the wire @es[S2] will
get a @es[1], as both @es[GO] and @es[S1] will be @es[1]. But
this differs from the second program! This means that the
two circuits are not @es[≃^circuit], which violates
soundness.

No Esterel context would ever produce a violation like this,
as this only occurs when the outer circuit context violates the
protocol that @es[GO] and @es[SEL] are mutually exclusive.
Therefore we can fix this by wrapping any compilation in a guard
which, if this condition is violated, forces the circuit to have consistent
behavior. Such a wrapper is given in @figure-ref["guard"]. This guard
suppresses @es[GO] if the protocol is violated,
preventing the circuit from behavior from changing.
@figure["guard"
        "Guarding the top of a circuit to avoid protocol violations"
       (hc-append
        @es[(guard circuit)]
        @es[=]
        guard-pict)]
From here we can modify the statement of soundness to:
@proof[#:label "soundness2"
       #:title "Soundness over multiple instants"
       #:type 'conjecture
       #:statement @list{For all @es[p-pure] and @es[q-pure],
        if @es[(CB p-pure)] and
        @es[(≡ p-pure q-pure)],
        then
        @es[(≃^circuit (guard (compile p-pure)) (guard (compile q-pure)))]}]
Which removes the requirement that the @es[SEL] be @es[0], but adds in the @es[guard].
One should also prove that
@proof[#:label "guard-correct"
       #:title "guard is correct"
       #:type 'conjecture
       #:statement @list{For all @es[p-pure],
        if @es[(≃ (and (of (compile p-pure) GO) (of (compile p-pure) SEL)) 0)]
        then
        @es[(≃^circuit (compile p-pure) (guard (compile p-pure)))]}]
Which shows that the guard never changes the program behavior if
the protocol is never violated.

I believe that this is the only guard necessary. This belief
comes from the proofs I have done so far: Other than proofs involving @es[Can],
the mutual exclusion of @es[GO] and @es[SEL] is the strongest precondition
needed.@note{As we always take @es[SEL] to be @es[0], this condition
is given by the existing preconditions on soundness and adequacy.}

The @es[RES] and @es[SUSP] wires do not need a similar guard procedure, because of
@proof-ref["activation-condition"]. While their is a similar protocol for them
(e.g. @es[GO] and @es[RES] are mutually exclusive), this protocol only matters
while @es[SEL] is @es[1], as @es[RES] and @es[SUSP] only have an effect
on program resumption. Therefore the guard procedure above is enough to protect
against errant uses of these wires by a (non-Esterel) outer context.

I suspect that the @es[KILL] wire should not need a guard either. This is because of
the changes to the compilation of @es[par] from @secref["just:sound:compiler"]. These changes
remove the reliance on the protocol that return codes above @es[1] trigger the @es[KILL] wire,
and therefore no protocol, and no guard, should be needed.

Adequacy must also be extended in a similar manner. However
the new statement of Adequacy must be extended to involve
the inter-instant translation function @es[next-instant].

@section[#:tag "future:remove"]{Removing θ from ρ}

I suspect that there is a variant of my calculus which is
both stronger (in the sense that it can prove more things
equal) and does not require the @es[θr] portion of the
environment. The idea behind is this that a @es[θr] can
always be removed by running the existing @rule["emit"] and
@rule["signal"] rules backwards, so why add it in the first
place? Specifically, I believe that the @rule["emit"] and
@rule["is-present"] rules can be replaced with:

@[render-specific-rules2 '(emit is-present)]

In this new system the @rule["is-present"] rule says that we
may take the then branch of an @es[if] when the environment
is @es[GO] and there is an @es[emit] for that signal in a
relative evaluation context. The correctness of this rule
can be validated by the current calculus (modulo the
different environment shape), because the @es[emit] could be run,
putting @es[(mtθ+S S present)] in the environment, and then
the rule old @rule["is-present"] rule could take over.

The @rule["emit"] rule is where the extra power comes in. It
lets us reshuffle @es[emit]s arbitrarily within evaluation
contexts. This would let us, for example, lift an @es[emit]
out of a @es[seq]. We could
prove equations like @es[(≡ (par (emit S) q) (seq (emit S) q))],
and @proof-ref["unprovable-lifting"] which was discussed in
@secref["example"]. The new @rule["emit"] rule cannot be proven by the
current calculus, because in enables reasoning about
@es[emit]s when there is no @es[GO], and
when the binding form is not in an evaluation context with respect to the @es[emit].

This new rule would require changing the formalization of
@proof-ref["strongly-cannibalizing"], as the new
@rule['emit] rule could always execute, using
@es[(= E hole)]. However this does not seem like it would
make a similar proof impossible, using a different
formulation of the @es[⟶^s] and @es[⟶^r] relations. Or
perhaps this could be solved by enforcing that the evaluation context
never be empty. Both paths would be worth exploring.

The definition of @es[Can] would also need to change in this variant of the calculus.
The @es[Can] function would likely still need an @es[θ] argument, therefore @es[Can]
will need to add @es[1]s to @es[θ] somehow. This could likely be done by replicating
the relative evaluation context reasoning from the @rule["is-present"] rule, but it
is not clear how this would work.

@section{Fully Abstract Compilation}

A future semanticist may wish to prove that the Esterel compiler (augmented
with @es[guard]) is fully abstract. I believe that the Constructive Calculus
gives the tools to do this.
Specifically, the theorem to prove would be:
@proof[#:label "fully abstract"
       #:title "Fully Abstract Compilation"
       #:type 'conjecture
       #:statement @list{For all @es[p-pure] and @es[q-pure],
        @es[(≃^esterel p-pure q-pure)]
        if and only if
        @es[(≃^circuit (guard (compile p-pure)) (guard (compile p-pure)))]}]
The reasons that such a proof may be within reach follows from the following chain of reasoning.
First, the definition of @es[≃^circuit] used here is defined by analyzing
all of the possible inputs to the circuits.
Second, the inputs to the circuits can be simulated using Esterel contexts. For example,
if we have one input signal @es[SI], we can simulate all inputs on it using the contexts
@es[(signal SI hole)], @es[(signal SI (par (emit SI) hole))],
and @es[(signal SI (par (present SI (emit SI) nothing) hole))], which correspond to
@es[0], @es[1], and @es[⊥] respectively. Third, we know that
the evaluator given by the Constructive Calculus is equivalent to the circuit evaluator
by @proof-ref["comp-ad"]. Therefore if the contexts which simulate the inputs
to the circuit are sufficient to decide @es[≃^esterel],
it must be that the notions of contextual equivalence between Esterel and Circuits
is the same. I believe that these contexts, plus some which change @es[A], are enough to decide @es[≃^esterel].
Formally, let these be defined as:@(linebreak)
@[definition
   #:notation @es[(input-contexts L-S)]]{
                                                                                         
 @[vl-append
   @es[(= (input-contexts (L0set)) (L2set (ρ · GO hole) (ρ · WAIT hole)))]
   (panorama
    [hbl-append
     @es[(input-contexts(LU (L1set S) L-S))]
     [def-t " "]
     @es[=]
     (let ([x [def-t " { "]])
       (refocus
        [vl-append
         [hbl-append x @es[(signal S C)] [def-t " | "] @es[(L∈ C (input-contexts L-S))] [def-t "}"]]
         [def-t " ∪ "]
         [hbl-append [def-t " { "] @es[(signal S (par (emit S) C))] [def-t " | "] @es[(L∈ C (input-contexts L-S))] [def-t "}"]]
         [def-t " ∪ "]
         [hbl-append [def-t " { "] @es[(signal S (par (present S (emit S) nothing) C))] [def-t " | "] @es[(L∈ C (input-contexts L-S))] [def-t "}"]]]
        x))])
      
   ]
}
If one could prove:
@proof[#:label "signals-decide-equality"
       #:title "Signals decide contextual equivalence"
       #:type 'conjecture
       #:statement @list{For all @es[p-pure] and @es[q-pure],
        @es[(≃^esterel p-pure q-pure)]
        if and only if
        for all @es[(L∈ C (input-contexts (LU (FV p-pure) (FV q-pure))))],
        @es[(≡ (in-hole C p-pure) (in-hole C q-pure))]}]
then the argument laid out here should be enough to complete a proof of fully abstract compilation.
I do not know how this proof would proceed, however my intuition is that if
there exists some context which shows that two terms are not @es[≃^esterel], then one could inductively walk
that context, and build a context which is in the @es[input-contexts] and which also shows
that the two terms are not equivalent. Or perhaps the proof of Böhm's Theorem for the @es[λ]-calculus
could provide inspiration.

