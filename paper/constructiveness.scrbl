#lang scribble/base

@(require scriblib/figure
          "redex-rewrite.rkt"
          "cite.rkt"
          "util.rkt"
          "constructiveness-examples.rkt")

@title[#:tag "sec:constructiveness"]{On Constructiveness}

@right-figure[#:lines 10
 #:caption @elem{A Non-constructive Program}
 #:tag "ex:constructive1"
 #:wide? #t]{
@init-term/block
}

The properties of logical correctness and
constructiveness are key for any correct semantics
of Esterel. For examples of these properties we refer the reader to @secref["gettin stuck"].
We follow the definition of constructiveness given by the constructive operational semantics (COS) as
referenced by @citet[esterel02] and described by
@citet[optimizations-for-esterel-programs-thesis].
Constructiveness is defined by the COS evaluator: non-constructive programs
reduce to stuck terms (that are not
@es[complete]).


In our semantics, for many expressions, this is also the
case. But, it is not the case for all of them because
reductions that occur in arbitrary program contexts sometimes
give @es[Can] more information than it “should” have (more
precisely, more information that it would get by running the
program directly). This extra information means that
reductions in our calculus can transform a non-constructive
program into a constructive one that can still reduce.

For an example, consider the expression in @figure-ref["ex:constructive1"].
If we restrict our attention to the outside part of the
term (the way that the COS semantics does), it reduces only
by replacing the outer @es[signal] form with a @es[ρ] expression.
At that point, the expression might appear to be
stuck because @es[Can] is unable to prove that
@es[S1] is not emitted (and thus the @rule["absence"]
rule does not apply) and the @es[present] expression
does not reduce (because @es[S1] is @es[unknown]).

@right-figure[#:lines 8
 #:caption @elem{An expression equivalent to the expression in @figure-ref["ex:constructive1"]}
 #:tag "ex:constructive2"]{
@extra-info-visible/block
}

There are reductions that can occur, however, at the inner
@es[signal] expression, revealing
information to @es[Can], and enabling it to determine that
@es[S1] is @es[absent].

Specifically, the calculus can reduce in this context:
@the-context/block
and thus it can turn the signal form into a @es[ρ] and
perform the @es[emit], resulting in the expression
in @figure-ref["ex:constructive2"].
Being able to reduce in that context is effectively “peeking” ahead
into the future non-constructively.

Once those reductions happen, @es[Can] is able
to determine that @es[S1] cannot be emitted and now
the @rule["absence"] rule can fire, eventually reducing the
original expression to
@|final-term/block|.

In sum, our calculus equates some non-constructive programs to
constructive programs with the same logical behavior. Although
we are not satisfied with this aspect of our calculus and believe
that it deserves further study, such a
relaxation of constructiveness is not
unprecedented@~cite[tardieu-deterministic].
