#lang scribble/base

@[require "lib/cite.rkt"]

@title{An Introduction}

The language Esterel has found success in many
safety-critical applications. It has been used in the
creation and verification of the maintenance and test
computer, landing gear control computer, and virtual display
systems of civilian and military aircraft at Dassault
Aviation@~cite[esterel-avionics] and the specification of
part of Texas Instrument's digital signal
processors@~cite[twelve-years-later].

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

Some of these semantics are expressive enough to give an
evaluator for programs, giving meaning to full programs by
running them. Others give us local reasoning, allowing for
modular reasoning about fragments of full programs (i.e.
constant propagation or modular compilation). Still others
give syntactic reasoning, which reason about programs
directly using their syntax, without going through an
external domain. This allows for more direct communication
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
simultaneously, local, syntactic, sound, and expressive
enough to give an evaluator for the language. This is the
contribution of the dissertation: @centered{There exists a
 local, syntactic, sound, and expressive semantics for
 Esterel.}

I have proven this calculus is sound for Loop Free, Pure
Esterel programs with respect to the circuit semantics for
Esterel@~cite[esterel02]. In addition I will give evidence
and arguments for the soundness of the rest of the calculus,
as well as future directions for making the calculus more
powerful and useful.