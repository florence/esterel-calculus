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

Its success can partially be attributed to how its computational model is
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
running them---such as the Constructive Operational
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
be)  consistent and sound, in that they all describe the exact same
language, as opposed to subtly different variations on that
language.

Each of Esterel's many semantics do some of these jobs very
well. However there are no semantics for Esterel which are
simultaneously, local, syntactic, consistent, sound, and adequate enough
to give an evaluator for the language. This is the
contribution of this dissertation: a
syntactic, local, consistent, sound, and adequate semantics
for Esterel.

I have shown that this syntactic, local semantics---this
calculus---is consistent, sound, and adequate. I show this
using three pieces of evidence: proofs, testing, and prior
work. This evidence, this tripod the calculus stands upon,
is necessary because not all parts of the calculus stand
equally upon all three legs. The proofs apply only to loop
free, pure Esterel programs, and are proven with respect
to the circuit semantics
for Esterel@~cite[esterel02]. The full calculus, on the
other hand, is tested against several different Esterel
semantics and implementations. Many parts of the calculus are
also borrowed from the prior semantics, helping increase
confidence in their correctness.

@bold{Syntactic.} The benefits of a syntactic semantics is primarily human:
They allow reasoning about a programming language to be
expressed directly in terms of that language, rather than in
terms of some external domain.
Often developing a semantics which uses @italic{only} the
syntax of a language is impractical, or even impossible.
See, for instance, the @es[σ] and @es[ρ] forms of the
@citet[felleisen-hieb] state calculus which do not appear
directly in any language, or evaluation
contexts@~cite[felleisen-friedman] often used to describe
non-local control operators (e.g. exceptions, continuations)
which while described in terms of existing syntax cannot be
written directly by a programmer. However, while these
frameworks require extending the syntax of the language,
they still map closely to the syntax of the surface
language, and the extensions they use are minor and either
can be mapped directly to the surface language syntax or
require only minor annotations to the surface syntax.
Therefore, even in the case of minor syntactic extensions, a
syntactic semantics still allows for explanations of program
transformations using the notation users of that language
are familiar with, rather than some external domain. In the end,
this means that calculi are syntactic @italic{by construction}.

In order to make my calculus sound and adequate I have added
two new forms to the syntax of Kernel Esterel: a variant of
@citet[felleisen-hieb]'s @es[ρ], and a loop variant
@es[loop^stop]. They are discussed in more detail in
@secref["sec:free-and-pure"] and @secref["sec:the-rest"] respectively.

@bold{Local.} A local semantics is useful
for both human and machine reasoning. Reasoning about full
programs is difficult, impractical, and in often impossible
in the case of libraries. Modular reasoning is essential for
working with large programs, thus we want a local semantics.

Calculi are local @italic{by construction.}
A calculus allows it's equations
of the calculus to be using under any program context. In
practice this means that most equations apply anywhere in a
program, while some work as long as entire scope of a signal
is visible. Detains my be found in @secref["calc:eql"].

@;@section[#:tag "intro:consistent"]{Consistent}

@bold{Consistent.} Consistency is one of the most essential
of these facets. A consistent semantics is one that does not
allow contradictions to be derived: for example, by not
allowing two programs to be proven equal if they evaluate to
different values.

The Consistency of the calculus given by proof and by testing. Details may be found in
@secref["just:consistent"] and @secref["just:sound:testing"].

@bold{Sound.} Soundness is necessary for a semantics which describes an
already established language. A sound semantics is one which
agrees with an existing, ground truth semantics. In other
words, a semantics which is not sound describes a @italic{
 different} language that the one it is supposed to describe.
Thus soundness, like consistency is essential for any
semantics.

The soundness of the calculus is also given by proof and testing.
Specifically it is proven with respect to the circuit
semantics@~cite[esterel02], for pure, loop free, programs
within a single instant. Evidence for the Soundness for
multi-instant, loop containing programs is given by random testing. This is discussed
more in @secref["just:sound"]  and @secref["just:sound:testing"].

@;@section[#:tag "intro:adequate"]{Adequate}
@[define semantics-note
  @note{There are many ways to define what @italic{
    semantics} means. Literally, a semantics is that which gives
   meaning to a language, but that just shifts the question
   over to defining ``meaning''. Therefore, I am intentionally
   using a very broad definition.}]

@bold{Adequate.} Adequacy describes the power of a semantics. If we take the
word @italic{semantics} to mean ``something which allows for
formal reasoning about a language'',@semantics-note then we can have semantics
which allow for manipulations or transformations of a
language, but cannot actually run a complete program. Such
semantics are not @italic{adequate} for describing an
evaluator for a language. This is not ideal, as it means
there is some aspect of the language the semantics does not
describe. Therefore, to make sure a semantics has broad coverage
of the aspects of a language, an adequate semantics is desirable.

Adequacy is also given by proof and testing. Like soundness, it is
proven for pure, loop free, programs for one instant.
Evidence for the Adequacy of loop containing programs with
host language expressions across multiple instants is also
given by random testing. This is discussed
more in @secref["just:adequacy"] and @secref["just:sound:testing"].

@section{Overview}

The dissertation is divided into six more chapters, and four
appendices. @Secref["background"] summarizes the
background a reader will need to understand this document,
as well as pointers to the background reading I assume the
reader has an understanding of. @Secref["sec:free-and-pure"] then describes the
calculus I have designed on pure, loop free Esterel programs.
Then @secref["sec:proofs"] gives
the proofs for Consistency, Soundness, and Adequacy on this
part of the calculus. Next @secref["sec:the-rest"]
gives the remainder of the calculus and describes the remainder of
the evidence that the calculus is correct. 
@Secref["related"]
gives existing work related to my calculus. Finally, @secref["final"]
gives some final thoughts and future directions.

Appendix A lists definitions for all of the notation
I use here. Appendix B gives the proofs of the
theorems. Appendix C gives an overview of the
implementation of a circuit solver I implemented for my proofs.
Appendix D gives examples of using the calculus to prove equalities.