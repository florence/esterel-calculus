#lang scribble/base

@[require
 "lib/cite.rkt"
 "lib/redex-rewrite.rkt"
 scriblib/footnote]

@title[#:tag "intro"]{An Introduction}

The language Esterel has found success in many
safety-critical applications. It has been used in the
creation and verification of the maintenance and test
computer, landing gear control computer, and virtual display
systems of civilian and military aircraft at Dassault
Aviation@~cite[esterel-avionics] and the specification of
part of digital signal processors at Texas
Instruments@~cite[twelve-years-later].

Its success can partially be attributed to how it is
radically different from other languages. It gives the
programmer the ability to use non-local communication
mechanisms to coordinate powerful non-local control (like
suspension or preemption of whole groups of threads) while
maintaining deterministic concurrency. This non-local nature
of evaluation leads to unexpected situations. For example
the choice of which branch a conditional takes may
immediately affect the choice another conditional makes in a
different part of the program, without any explicit
communication between those parts of the program. The
selection of the other branch may render the entire program
invalid. This powerful and unique evaluation model makes
giving a formal semantics to Esterel a subtle and tricky
business, and has lead to a plethora of different semantics
suited to different purposes.

Some of these semantics are adequate to give an
evaluator for programs, giving meaning to full programs by
running them---Such as the Constructive Operational
Semantics (COS)@~cite[optimizations-for-esterel-programs-thesis],
and the State Behavioral Semantics (SBS)@~cite[esterel02]. Others give us local reasoning, allowing for
modular reasoning about fragments of full programs (i.e.
constant propagation or modular compilation)---such as
the Circuit Semantics@~cite[esterel02] or the Axiomatic Semantics (AS)@~cite[tini-axiomatic].
Still others give syntactic reasoning, which reason about programs
directly using their syntax, without going through an
external domain---Such as the COS, SBS, and AS. This allows for more direct communication
with programmers in the domain they already understand. This
is useful, for example, when giving good crash reports,
explaining program refactorings, or for optimization
coaching@~cite[optimization-coaching], which helps explain
to programmers why some optimization were not applied and
how to fix it. All of the existing semantics are (and must
be) sound, in that they all describe the exact same
language, as opposed to subtly different variations on that
language.

Each of Esterel's many semantics do some of these jobs very
well. However there are no semantics for Esterel which are
simultaneously, local, syntactic, sound, and adequate enough
to give an evaluator for the language. This is the
contribution of this dissertation is the construction of
syntactic, local, consistent, sound, and adequate semantics
for Esterel.

I have proven this syntactic, local semantics---this
calculus---is consistent, sound, and adequate for Loop Free,
Pure Esterel programs with respect to the circuit semantics
for Esterel@~cite[esterel02]. In addition I will give
evidence and arguments for the soundness of the rest of the
calculus, as well as future directions for making the
calculus more powerful and useful.

@;@section[#:tag "intro:syntactic"]{Syntactic}

@bold{Syntactic.} The benefits of a syntactic semantics is primarily human:
They allow reasoning about a programming language to be
expressed directly in terms of that language, rather than in
terms of some external domain, at least in principle.
Often developing a semantics which uses @italic{only} the
syntax of a language is impractical, or even impossible.
See, for instance, the @es[σ] and @es[ρ] forms of the
@citet[felleisen-hieb] state calculus which do not appear
directly in any language, or the evaluation
contexts@~cite[felleisen-friedman] often used to describe
non-local control operators (e.g. exceptions, continuations)
which while described in terms of existing syntax cannot be
written directly by a programmer. However, while these
frameworks require extending the syntax of the language,
they still map very closely to the syntax of the surface
language, and the extensions they use are minor and either
can be mapped directly to the surface language syntax or
require only minor annotations to the surface syntax.
Therefore, even in the case of minor syntactic extensions, a
syntactic semantics still allows for explanations of program
transformations using the notation users of that language
are familiar with, rather than some external domain.

In order to make my calculus sound and adequate I have added
two new forms to the syntax of Kernel Esterel: a variant of
@citet[felleisen-hieb]'s @es[ρ], and a loop variant
@es[loop^stop]. This is discussed in more detail in
@secref["sec:calculus"].

@;@section[#:tag "intro:local"]{Local}

@bold{Local.} The benefits of a local semantics are useful
for both human and machine reasoning. Reasoning about full
programs is difficult, impractical, and in often impossible
in the case of libraries. Modular reasoning is essential for
working with large programs, thus we want a local semantics.

Locality in my calculus is handled by allowing the equations
of the calculus to be using under any program context. In
practice this means that most equations apply anywhere in a
program, while some work as long as entire scope of a signal
is visible. Detains my be found in @secref["calc:eql"] and
@secref["just:local"].

@;@section[#:tag "intro:consistent"]{Consistent}

@bold{Consistent.} Consistency is one of the most essential
of these facets. A consistent semantics is one that does not
allow contradictions to be derived: for example, by not
allowing two programs to be proven equal if they evaluate to
different values.

The Consistency of the calculus given by proof, as a
corollary of Adequacy. Details may be found in
@secref["just:consistent"].

@;@section[#:tag "intro:sound"]{Sound}

@bold{Sound.} Soundness is necessary for an semantics which describes an
already established language. A sound semantics is one which
agrees with an existing, ground truth semantics. In other
words, a semantics which is not sound describes a @italic{
 different} language that the one it is supposed to describe.
Thus soundness, like consistency is essential for any
semantics.

The soundness of the calculus is also given by proof.
Specifically it is proven with respect to the circuit
semantics@~cite[esterel02], for pure, loop free, programs
withing a single instant. Evidence for the Soundness for
multi-instant, loop containing programs is given by informal
arguments and random testing. This is discussed
more in @secref["just:setup"]and  @secref["just:sound"].

@;@section[#:tag "intro:adequate"]{Adequate}
@[define semantics-note
  @note{There are many ways to define what @italic{
    semantics} means. Literally, a semantics is that which gives
   meaning to a language, but that just shifts the question
   over to defining ``meaning''. Therefore, I am intentionally
   using a very broad definition.}]

@bold{Adequate.} Adequacy describes the power of a semantics. If we take the
word @italic{semantics} to mean ``something which allows for
formal reasoning about a language''@semantics-note, then we can have semantics
which allow for manipulations or transformations of a
language, but cannot actually run a complete program. Such
semantics are not @italic{adequate} for describing an
evaluator for a language. This is not ideal, as it means
there is some aspect of the language the semantics does not
describe. Therefore, to make sure a semantics has broad coverage
of the aspects of a language, an adequate semantics is desirable.

Adequacy is also given by proof. Like soundness, it is
proven for pure, loop free, programs for one instant.
Evidence for the Adequacy of loop containing programs with
host language expressions across multiple instants is also
given by informal argument and random testing. This is discussed
more in @secref["just:setup"]and  @secref["just:adequacy"].

@;@section{Overview}

@section{Overview}

The dissertation is divided into 5 more Chapters, and three
Appendices. @Secref["background"] covers summarizes the
background a reader will need to understand this document,
as well as pointers to the background reading I assume the
reader has. @Secref["sec:calculus"] the describes the
calculus I have designed. @Secref["just"] gives the evidence
that my calculus meets the properties above. @Secref["related"]
gives existing work related to my calculus. @Secref["final"]
gives some final thoughts and future directions.

Appendix A lists definitions for all of the notation
I use here. Appendix B gives the proofs of the my
theorems. Appendix C gives an overview of the
implementation of a circuit solver I implemented for my proofs.