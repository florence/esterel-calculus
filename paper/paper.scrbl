#lang scribble/acmart @acmsmall @review @anonymous
@(require
          "cite.rkt"
          "util.rkt"
          "agda-fact.rkt")


@title[#:style paper-title-style]{A Calculus for Esterel}
@subtitle{@subtitle-font-adjust{“If can, can. If no can, no can.”  —Hawaiian pidgin proverb}}
@author{Spencer P. Florence}
@author{Shu-Hung You}
@author{Jesse A. Tov}
@author{Robert Bruce Findler}
 
@abstract{
          
 The language Esterel has found success in many safety
 critical applications, such as fly-by-wire systems and
 nuclear power plant control software. Existing semantics of
 these languages generally fall into two categories:
 translation to Boolean circuits, or operational semantics
 that give a procedure for running a whole program.

 In contrast, equational theories enable reasoning about
 program behavior via equational rewrites at the source
 level. Such theories form the basis for proofs of
 transformations inside compilers or for program refactorings,
 and defining program evaluation syntactically.

 This paper presents the first such equational theory for Esterel.
 It also illustrates the calculus’s usefulness with a series of
 example equivalences and discuss how it enabled us to find bugs
 in Esterel implementations.
}

@include-section["intro.scrbl"]
@include-section["sense-of-esterel.scrbl"]
@include-section["reduction-rules.scrbl"]
@include-section["potential-function.scrbl"]
@include-section["invariants.scrbl"]
@include-section["eval.scrbl"]
@include-section["constructiveness.scrbl"]
@include-section["examples.scrbl"]
@include-section["testing.scrbl"]
@include-section["standard-reduction.scrbl"]
@include-section["related.scrbl"]

@; this comes out in the wrong place in the PDF, or maybe nowhere
@;{@acks{
 Thanks to Dan Feltey, Christos Dimoulas, and Vincent St-Amour for their
 feedback on drafts of this paper. Thanks to Colin Vidal,
 Gérard Berry, and Manuel Serrano for their help with HipHop,
 Esterel v5 and, more generally, understanding Esterel's
 semantics.
}}

@;{

Introduces rules.
Physican intuition behind the rules:

lift corresponds to a single propagating down a wire, or being saved to a register
absence and presence rules correspond to the circuit settling.

STD reduction.

Inter-instants.


intuition for explaining CB: CB's job is to avoid variable capture on lifts. That’s
why it’s slightly different between `present S p q` and `p || q`: one of
these is an evaluation context, the other is not, so they have different constraints.

So to summarize CB enforces/describes three things:

1. Capture avoiding lifts.
2. Sequential variables actually being sequential.
3. Doing the “right” thing for schizophrenic variables. (Via 1)

@section{The Next Instant}

@section{why this semantics is correct}
@subsection{theorems}
@subsection{Correspondence to existing Esterel semantics and implementation}

@section{Transformations the Calculus can and cannot preform}

We would like to prove (rho theta C[p]) == C[(rho theta p)] if Dom(theta) distinct from
FV(C). Can't do. We would want this for inter-instant stuff. Doesn't work at in general, some
specific terms where it would work. (i.e. if the signal has a value already moving it may be bad)



TODO random testing and such to see if it does or doesn't work,
 and it what cases it does or doesn't work.


Can prove:

Signal S in emit S; Present S then <p> else <q>
≡
Signal S in emit S; <p>

and

Signal S in Present S then <p> else <q>
≡
Signal S in <q>
if S ∉ Can⟦Present S then <p> else <q>,{S ↦ unknown}⟧
}

@(generate-bibliography)

@(unless (getenv "SKIPAGDA") (check-the-examples))
