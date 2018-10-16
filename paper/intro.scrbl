#lang scribble/base
@(require "cite.rkt"
          "redex-rewrite.rkt")



@title{Introduction}

The language Esterel has found success in many safety-critical
applications. It
has been used in the creation and verification of the maintenance
and test computer, landing gear control computer, and
virtual display systems of civilian and
military aircraft at Dassault
Aviation@~cite[esterel-avionics]; the
control software of the N4 nuclear power plants; the
Airbus A320 fly-by-wire system; and the specification of part of Texas Instrument's digital signal
processors@~cite[twelve-years-later].

This success with real time and embedded systems in domains
that need strong guarantees can be partially attributed to
its computational model. Esterel treats
computation as a series of deterministic reactions to
external stimuli. All parts of a reaction complete
in a single, discrete time step, called an @italic{instant}.
Furthermore, in this synchronous reactive
paradigm@~cite[synchronous-approach twelve-years-later],
each instant is isolated from interference by
the outside environment once the reaction begins. In
addition, instants exhibit deterministic concurrency; 
each reaction may contain concurrent
threads without execution order effecting the
result of the computation.

This combination of synchronous reactions with
deterministic concurrency makes formulating the semantics a challenging problem.
Existing semantics tend to take two
forms. The first, and most widely used, are
semantics that give meaning to programs through a
translation to circuits. These semantics are excellent for
compilation and optimization. However they are
not ideal for programmers, who would rather reason in terms
of the source-level program not its compiled form.

The second form are operational semantics that eschew term
rewriting in favor of decorating terms with various flavors
of code pointers and state annotations to track execution.
These semantics are easier for programmers to reason with
but give meaning only to whole programs. They do not
lend themselves to compositional reasoning about
program fragments, which programmers need.

To obtain the best of both of these approaches, we build on
@citet[plotkin] and @citet[felleisen-hieb]’s work on
equational theories of programming languages. These theories
model languages with a set of axioms that specify when
source-level terms are equivalent. As a result, they provide
a single framework for both reasoning about how a program
will run (e.g. reduce to an answer) using only the source
text of the program, and for justifying program
transformations in host of applications: compiler
transformations, refactorings, program derivations, etc.

This paper reports on the first equational theory of
Kernel Esterel@~cite[esterel02]. Developing such a theory is tricky because of the
highly non-local nature of evaluation in Esterel. To
maintain determinism and synchrony, evaluation in one thread of execution
may affect code arbitrarily far away away in the program,
even if that evaluation does not directly modify shared state.
For instance, the selection of a
particular branch of execution in one thread may immediately
unblock a different thread of execution. The selection of
the other branch may render the entire program invalid.
These non-local execution and correctness issues are at the
heart of Esterel's notions of @italic{Logical Correctness} and
@italic{Constructiveness}, and have informed the choice of
techniques used for previous semantics. The circuit
semantics match both notions well because they are
intimately tied to whether or not a given cyclic circuit
settles. The operational semantics handle these properties
by performing full program passes on each evaluation step to
both propagate execution information to the entire program,
and determine which locations in the program are safe to
evaluate. A calculus, however, cannot use either of those
techniques. To this end our calculus borrows from
@citet[felleisen-hieb]'s equational theory of state and
@citet[optimizations-for-esterel-programs-thesis]'s Constructive
Operational Semantics to give the first calculus for Esterel.

The remainder of this paper consists of seven sections.
@Secref["sec:gentle"] provides an introduction to Esterel
and to the specific syntax we use for Kernel Esterel.
@Secref["sec:calculus"] explains the semantics and our
central results, which have all been checked in Agda. With
the semantics defined, the paper moves on to discuss
implications of specific aspects of our semantics.
@Secref["sec:constructiveness"] discusses constructiveness
and how it interacts with our semantics.
@Secref["sec:examples"] gives some example equivalences that
our calculus supports and discusses others that it does not.
Our semantics is executable and @secref["sec:testing"]
discusses how we test that our semantics is faithful to
preexisting semantics and implementations. In short, we
designed and implemented an executable version of our
semantics and used it to find bugs in Esterel
implementations. We also automatically typeset the figures
in the paper from the semantics and use it to test all of
the examples in the paper. @Secref["sec:stdred"] discusses a
standard reduction that we designed to aid in testing but
have not proven, and we conclude with a discussion of
related work in @secref["sec:related"].
