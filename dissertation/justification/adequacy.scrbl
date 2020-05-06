#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          "../lib/proof-extras.rkt"
          (only-in "../proofs/proofs.scrbl")
          (only-in "../notations.scrbl")
          (only-in scribble/manual racket)
          scriblib/figure
          racket/match
          "../lib/jf-figures.rkt")

@title[#:style paper-title-style #:tag "just:adequacy"]{Justifying Adequacy}

Adequacy is the statement that a calculus can define an evaluator for
it's language. In this case, we want Computational Adequacy, which is the statement
that the calculus's evaluator is equivalent to the ground truth evaluator:
@proof-splice["comp-ad"]

The full proof can be found at @proof-ref["comp-ad"]. The first premise of this theorem
requires that the program be @es[closed], as the evaluator is only really meant to work on full programs.
However @es[closed] here is slightly different from the usual definition, because it restricts
programs to those which will also generate closed circuits which will execute their first instant.
Formally, a program is @es[closed] if it is a @es[ρ] term with the control variable @es[GO],
and it has no free variables:

@extract-definition["closed"]

By setting @es[A] to @es[GO] we force the @es[GO] wire in
the compilation to be @es[1], which causes the circuit to
execute its first instant. The next premise is the usual
statement that we are only observing the first instant of
execution. The conclusion of the proof states that the
output signals and constructivity from the two evaluators
are the same.

@;TODO index ⟶^r

To complete the proof we use
a set of canonical forms for terms in the
calculus. Any closed term is equal to
such a canonical term, and that these canonical forms are the exact cases
that @es[eval^esterel] looks at. These canonical forms are
equivalent modulo @rule["par-swap"], meaning that, while a
canonical form, they may still step via @rule["par-swap"],
but may not take any other steps. To prove this @es[⟶] is
broken up into two parts: @[as-index @es[⟶^s]], which contains only the
compatible closure of @rule["par-swap"], and @[as-index @es[⟶^r]], which
is the compatible closure of every other rule.@note{The @tt{S} stands for ``swap'', and the @tt{R} stands
 for ``remainder''.} With that we can
state theorem about these canonical forms like so:
@proof-splice["step-is-v"]

The full proof is in @proof-ref["step-is-v"]. To unpack this:
The proof states that canonical forms are forms which both
cannot step by @es[⟶^r] and if they step by @es[⟶^s], then
the resulting form also cannot step by @es[⟶^r].
We only
need to check for one step of @es[⟶^s], because if multiple @es[⟶^s] could uncover
a reduction in @es[⟶^r], then there would exist some term which would be one step @es[⟶^s] away
from a @es[⟶^r] reduction which would violate the lemma. The negative existential in this
would make it tricky to prove. However, we are in luck: everything used in this statement
is decidable. Therefore this is proved by proving it's contrapositive:
@proof-splice["nv-must-step"]

The full proof can be found at @proof-ref["nv-must-step"].
This proof states that if a term is not one of our canonical
forms, then it must be able to either take a step in
@es[⟶^r], or step by @es[⟶^s] then by @es[⟶^r]. The proof
of this follows by induction of @es[p-pure], with some case analysis
on @es[blocked-pure] and @es[done] along the way.

Beyond this, it is the case that @es[⟶^r] is a strongly
canonicalizing relation. Therefore it must be the case that we
can reach a canonical form using a finite number of @es[⟶^r]
and @es[⟶^s] steps:
@proof-splice["strongly-cannibalizing"]

The full proof is given in
@proof-ref["strongly-cannibalizing"]. The function
@es[count] acts as an estimate on the number of steps that a
term can take. Because it is strictly decreasing and gives
back a non-negative number, we must eventually reach a case
where no more @es[⟶^r] steps can be taken. Whats more its
easy to show that @es[⟶^s] does not change the count,
therefore there always exists a finite reduction path to
one of these canonical forms.
Therefore all closed terms are @es[≡^esterel] to some
canonical term.

Now that we have show that there exist canonical forms, and
that every closed pure Esterel term is @es[≡^esterel]
to one of these forms, we know that @es[eval^esterel] is
defined on all closed pure terms. The next step in proving adequacy is to show
that these two canonical forms give back the same signal
set as their circuit compilation. Fortunately this follows fairly directly from
soundness, as we know that our canonical forms are @es[≡] to
the original term, and that @es[≡] is sound with respect
to the circuit compilation.

The final step is to show that the two types of canonical
forms map exactly to constructive and non-constructive
circuits respectively. The simpler of these is:
@proof-splice["e-v-is-c-v"]

Which is proved fully in @proof-ref["done-is-constructive"].
Note that the premise
@es[(complete-with-respect-to θr done)] always holds, by the
proof @es[canₛ-done] from the Agda code base which states
that the result of @es/unchecked[(->S Can)] on any @es[done] is empty.
The premises about the control wires are given by the
definition of @es[compile], and by the fact that unassigned
input wires are set to @es[0] by @es[eval^circuit]. This proof
follows by induction on the structure of @es[done].

The other side, the statement that @es[blocked-pure] corresponds to non-constructive
circuits is given by:@nopagebreak
@proof-splice["blocked-is-nc"]

The proof of which can be found at
@proof-ref["blocked-is-nc"]. The proof of this lemma is
complex. It relies on a subject-reduction lemma which shows
that, as the circuit reduction relation @es[⟶^c] steps
through the term, the wires which are in
@es/unchecked[(->S Can)] cannot change from @es[⊥]. The core
of this lemma is another subject-reduction lemma which shows that,
assuming @es[GO] is @es[⊥], @es[Can] is perfectly adequate
to describe evaluation:
@proof-splice["adequacy-of-can"]

The full proof is in @proof-ref["adequacy-of-can"]. To
unpack: If we are given some term @es[r-pure], and two
circuit states @es[cs_1] and @es[cs_2] such that both
circuit states are states of the compilation of @es[r-pure],
and @es[cs_1] steps to @es[cs_2], and we know about the
signals of @es[(compile r-pure)] via @es[θ], and we know
that the @es[GO] wire of @es[cs_1] is currently bottom, then
the invariant @es[all-bot] is preserved. The invariant
@es[all-bot] (@figure-ref["nc1"]) is formed of three
judgments. The first of these, @es[all-bot-S], says that any signal
wire is currently @es[⊥] if it is both
@es/unchecked[(->S Can)] and is @es[⊥] in @es[θ]. The
second, @es[all-bot-κ] says the same, but for
@es/unchecked[(->K Can)], return codes, and their wires.

@figure["nc1"
        @list{The smaller judgments for @es[all-bot]}
        (list
        @extract-definition["nc"]
        @extract-definition["nc-κ"]
        @extract-definition["nc-S"])]

The last of the judgments, @es[all-bot-rec]
(@figure-ref["nc2"]) looks complex, but all it says is that
the @es[all-bot] judgment holds for subterms, subcircuits, and
environments that match how @es[Can] recurs over the term.
Together all of these properties mean that ``@es[Can]
accurately predicts when wires are @es[⊥]''. Therefore the
overall proof states that ``@es[Can] accurately predicts when
wires are @es[⊥] when @es[GO] is @es[⊥]''@note{ This is why
 I call this proof ``adequacy''. When combined with the
 soundness of @es[Can], it tells us when @es[Can] gives a
 complete evaluator.} The last step in completing this proof is to
argue that initial states are always @es[all-bot], but this
follows fairly directly since wires are internal and output wires are initialized to
@es[⊥] in the initial state. Note that in this judgment the
metafunction @es[sub] extracts the substate of the circuit
corresponding to the given subterm.

@figure["nc2"
        @list{The recursive judgment part of @es[all-bot]}
        @all-bot-rec-pict]

At it's core the proof of @proof-ref["adequacy-of-can"]
holds because all return code and signal wires are and'ed
with the @es[GO] wire, therefore they can never be set to
@es[1] unless the @es[GO] wire is @es[1], and they can only
be set to @es[0] when they are not in @es/unchecked[(->S Can)]. From
this we can argue that @proof-ref["blocked-is-nc"] holds,
essentially, because the @es[GO] wires the leaves of the
@es[blocked-pure] must be blocked on a signal wire, and
therefore they depend on a @es[GO] which itself depends on
one of these signal, and therefore that @es[GO] wire must
always remain bottom.
