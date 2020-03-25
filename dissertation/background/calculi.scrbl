#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt")

@title[#:style paper-title-style #:tag "background-calculi"]{Language Calculi}

This section introduces the brand of semantics I have designed
to get the properties listed in my thesis. To start: what is
a semantics? A semantics is a function maps programs to
their meaning. For example: evaluators are
functions mapping programs to the result of running them; and denotational semantics
 give meaning by mapping programs to elements of some external
domain, like the circuit semantics for Esterel. The
semantics I plan to build will give meaning to terms by
mapping them to a set of terms to which they are equivalent.
Specifically I will do this by giving a set of axioms that
define an equivalence relation, which will implicitly define
this mapping from terms to sets of terms. This is the sense
in which the semantics I build will be syntactic: it gives
meaning to programs in terms of only other programs.

This equivalence relation will let us reason about programs
like we reasoned about arithmetic in grade school: if we can
show two terms are equal, then we can safely replace of
those terms for another in some larger program without
changing its meaning. I will refer to this as a calculus
(taking the name from Church's lambda calculus).

To prepare the reader this section will walk through soem exa



what is a semantics?

@section{Syntactic}
Notions of reduction

@section{Local}
Program Contexts.

@section{Sound}
external model

@section{Adequate}
eval via reduction relation.

@section{State}
maps
Evaluation Contexts

@section{Contextual equivalence}
