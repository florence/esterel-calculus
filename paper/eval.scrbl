#lang scribble/base

@(require "calculus-figures.rkt"
          "redex-rewrite.rkt"
          "cite.rkt"
          "util.rkt"
          "agda-fact.rkt"
          scriblib/figure
          racket/set)

@title[#:tag "sec:eval"]{Evaluating Programs}

@figure["fig:eval" "Eval"]{@eval-pict}

@figure["fig:next-instant" "Next Instant"]{@next-instant-pict}


Now that we have established the correct binding
invariant and defined the primitive notions of
reduction, we can turn to the definition of the
evaluator. It is shown on the top-left of
@figure-ref["fig:eval"]. It accepts a program
and an initial environment (that captures what
the host language sets the input signals to),
and it returns the signals that were emitted
at the end of the instant. It is defined by
finding a complete expression that is @es[≡e]
to the input and extracting the @es[present]
signals from it.

The @es[≡e] relation is the symmetric, transitive,
reflexive closure of the @es[→] relation, which is
the compatible closure of the @es[⇀] reduction relation.

The central result of this paper is that @es[Eval]
is a function:

@theorem[#:label "thm:evalconsistent" #:break? #t]{
@(equiv
  (list (var-prem 𝕊_1)
        (var-prem 𝕊_2)
        (var-prem θ)
        (var-prem p))
  (list (newline-prem)
        (fact-prem (CB (ρ θ p)))
        (newline-prem)
        (fact-prem (Eval () () () p θ 𝕊_1))
        (newline-prem)
        (fact-prem (Eval () () () p θ 𝕊_2))
        (newline-prem))
  (same 𝕊_1 𝕊_2)
  "\\ ls₁ ls₂ -> eval≡ₑ-consistent")
}
The proof is given as @tt{eval≡@|sub-e|-consistent} in the
Agda code in the supplementary material.

This theorem is a corollary of the consistency of @es[≡e],
which states that if two expressions are @es[≡e], then
there is an expression that both reduce to, under the
transitive reflexive closure of the compatible closure of
the reduction relation:

@theorem[#:label "thm:equivconsistent" #:break? #t]{
@(equiv
  (list (var-prem p)
        (var-prem q))
  (list (fact-prem (CB p))
        (fact-prem (≡e () () () p q))
        (newline-prem))
  (∃ r Term (∧ (→* () () p r) (→* () () q r)))
  "\\ p q CBp p≡ₑq -> ≡ₑ-consistent CBp p≡ₑq")
}
The proof is given as @tt{≡@|sub-e|-consistent}, and it
follows from the confluence of reduction.

@; TODO: consider discussing the monotonicity of @es[Can],
@; as that seems like the most important Esterel-specific lemma.

Our semantics supports multiple instants via a
transformation that prepares a complete expression for
the next instant, @es[next-instant], shown in
@figure-ref["fig:next-instant"]. It makes four modifications
to the expression. First, it resets all signals to
@es[unknown]. Second, it replaces the @es[pause] expressions
where the program stopped with @es[nothing]. Third, it replaces
each @es[loop^stop] expression with a @es[loop] and @es[seq]. Finally, it adds a
@es[present] expression to @es[suspend] expressions that
have paused. The @es[present] serves to conditionally pause the body of
the @es[suspend] in the next instant. The result is an expression
suitable for use with @es[Eval] in the next instant.
