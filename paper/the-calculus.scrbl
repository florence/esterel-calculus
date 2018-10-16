#lang scribble/base
@(require scriblib/figure
          "util.rkt"
          "overview-figure.rkt"
          "redex-rewrite.rkt"
          "cite.rkt")
@title[#:tag "sec:calculus"]{The Esterel Calculus}

@figure["fig:overview" @list{An overview of the main definitions}]{
@;@right-figure[#:lines 18 #:caption "An overview of the main definitions" #:tag "fig:overview"]{
 @overview-figure
}

We define a reduction relation on program expressions that
corresponds to a single-step of computation. This relation
captures a notion of simplification, where each
computational step brings us closer to a final answer. Thus,
the reduction induces an evaluator for the language.
Furthermore, the reflexive, symmetric, and transitive
closure of the relation together with its closure over
arbitrary contexts gives rise to an equivalence relation
between programs terms, which is our calculus.

The remainder of this section explores the definitions that
comprise the calculus, specifically the definitions shown in
@figure-ref["fig:overview"]. @Secref["sec:reduction"] shows
the basic notion of reduction that our calculus supports and
@secref["sec:can"] describes our our @es[Can] function. The
judgment form @es[CB] captures how signals are to be used
in Esterel programs, and is described in @secref["sec:cb"].
Finally @secref["sec:eval"] gives the @es[Eval] and the
@es[next-instant] functions and the central result of this
work, namely that @es[Eval] is a function.

Before diving into the rules, however, we need a to extend
the @es[p] non-terminal to track information about the term
as it reduces. @Figure-ref["fig:supp"] shows the two
extensions. First, the @es[(loop^stop p q)] expression form
is similar to a @es[(seq p (loop q))] and is used by the
loop reduction rule (discussed in @secref["sec:reduction"]).

The other extension is the @es[(ρ θ p)] expression form, the
heart of our calculus. It pairs an environment (@es[θ]) with
an Esterel expression. The environment records what we have
learned about the signals and variables in this instant for
the contained subexpression, and various rules either add
information to the @es[θ] or exploit information recorded as
the program reduces. We keep the environments local to
specific expressions in order to facilitate local reasoning.

@include-section["reduction-rules.scrbl"]
@include-section["potential-function.scrbl"]
@include-section["invariants.scrbl"]
@include-section["eval.scrbl"]
