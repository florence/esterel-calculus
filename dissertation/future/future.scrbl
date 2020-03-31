#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          "../lib/rule-figures.rkt"
          "../lib/cite.rkt")

@title[#:tag "final" #:style paper-title-style]{Final Thoughts}
@section[#:tag "future"]{Future Work}
@subsection{Extending proofs to multiple instants, and guarding compilation}

must use guard to ensure GO => NOT SEL

Then show inter-instant sound somehow

@subsection[#:tag "future:remove"]{Removing θ from ρ}

I suspect that there is a variant of my calculus which is both stronger
(in the sense that it can prove more things equal) and does not require the
@es[θr] portion of the environment. The idea behind is this that a @es[θr]
can always be removed, so why add it in the first place? Specifically, I suspect that 
the @rule["emit"] and @rule["is-present"] rules can be replaced with:

@[render-specific-rules2 '(emit is-present)]

In this new system @rule["is-present"] because the rule
sensitive to @es[GO]. It says that we may take the then
branch of an @es[if] when the environment is @es[GO] and
there is an @es[emit] for that signal in a relative
evaluation context. The correctness of this rule can be
validated by the current calculus (modulo the different
environment shape).

The @rule["emit"] rule is where the extra power comes in. It
lets us reshuffle @es[emit]s arbitrarily within evaluation
contexts. This would let us, for example, lift an @es[emit]
out of a @es[seq] so that it would be in a relative
evaluation context with respect to an @es[if]. But it would
also let us move @es[emit]s elsewhere. For example, we could
validate that @es[(≡ (par (emit S) q) (seq (emit S) q))],
which has a slightly simpler circuit because there is not
synchronizer. It would also let the calculus prove
@proof-ref["unprovable-lifting"]. This rule cannot be proven by the current calculus, because in enables
reasoning about @es[emit]s when there is no @es[GO].

The definition of @es[Can] would also need to change in this variant of the calculus.
The @es[Can] function would likely still need an @es[θ] argument, therefore @es[Can]
will need to add @es[1]s to @es[θ] somehow. This could likely be done by replicating
the relative evaluation context reasoning from the @rule["is-present"] rule, but it
is not clear to me yet how exactly this would work, and proving it correct is
another thing entirely.

@subsection{Fully Abstract Compilation}

get stuff from poster

@section{Conclusion}
