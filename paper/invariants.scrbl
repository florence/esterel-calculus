#lang scribble/base
@(require "calculus-figures.rkt"
          "redex-rewrite.rkt"
          "cite.rkt"
          "util.rkt"
          "agda-fact.rkt"
          scriblib/figure
          racket/set
          rackunit
          redex/reduction-semantics
          (except-in esterel-calculus/redex/model/shared quasiquote)
          pict
          (prefix-in standard: esterel-calculus/redex/model/reduction))


@title[#:tag "sec:cb"]{Invariants of Reduction: Correct Binding}


@(define/esblock loop-term loop-term/block
   (loop
    (signal SZ
      (seq pause
           (emit SZ)))))

@(define/esblock loop-reduced loop-reduced/block
   (ρ (mtθ+S SZ absent)
      (loop^stop (seq pause (emit SZ))
                 (signal SZ
                   (seq pause (emit SZ))))))

@(check-not-false
  (member loop-reduced
          (apply-reduction-relation*
           standard:R
           (term (ρ · ,loop-term)))))

Our reduction relation does not rely on variable renaming,
as there are no rules that involve substitution. More
importantly, from the original Esterel use-case perspective,
a signal variable in Esterel corresponds to a wire in a
circuit, and wires are not changed during evaluation. Thus,
if we did require an α rule, our calculus would not be
faithful to Esterel.

@right-figure[#:lines 11 #:caption "A Schizophrenic Loop" #:tag "ex:schizophrenic"]{
 @loop-term/block
 @loop-reduced/block
}

One apparent conflict with the signals-as-wires perspective
is the @es[loop] rule. Because it duplicates the body of the
loop, and because wires are not duplicated in a circuit, we
must ensure that the variables in a loop body
are treated properly. The main reason that this duplication
is acceptable is the constraint that each loop must either
pause or terminate in a single instant. In general, the
issues surrounding signal variables in the body of a loop
are well studied in Esterel and come with their own
terminology. To understand the basic
problem, consider the program in the top of @figure-ref["ex:schizophrenic"].
It reduces to the one below it, which ends the instant.
Note that the residual term has an @es[(emit SZ)] waiting
in it, to be run in the next instant, but at the same time,
@es[SZ] is marked as absent in the environment.
When this program picks up in the next instant, that
@es[(emit SZ)] happens, making @es[SZ] present in the second
instant. But the loop body also unrolls again, just as it
did in the first instant and it introduces a second
@es[signal] form for @es[SZ] which, as in the first instant,
is @emph{not} present (with no @es[emit]) and gets set to
@es[absent]. This means that, in a single instant, the same
wire might hold two different values.

@(define multiple-incarn-note
   @note{
         Nested loops can cause a variable to be reincarnated
         more that once.
         })

Signals like @es[SZ] are called @italic{reincarnated},
@italic{schizophrenic} signals. A reincarnated
variable is one that is instantiated multiple times in the
same instance.@multiple-incarn-note A schizophrenic
variable is a reincarnated signal whose value changes
between incarnations.

The implications of such variables are well-studied by the
Esterel community and methods for compiling Esterel programs
with them exist@~cite[new-method-schizophrenic esterel02].
For our calculus, we must ensure that different
incarnations of a variable cannot directly observe the
values of different incarnations. While different
incarnations cannot have a direct effect on each other,
however, because different iterations of a loop can
communicate via a variable in an outer scope, the values of
different incarnations of a variable may indirectly affect
each other.

To capture how variables are treated by our calculus, we use
the @es[(CB p)] judgment, shown in @figure-ref["fig:cb"].
Our calculus works only with programs that have correct
binding, ensuring that variables cannot interfere with
each other during reduction. It also ensures that
sequential variables are used sequentially (as discussed in
@secref["sec:reduction"]), i.e., that any given sequential
variable appears in at most one side of any @es[par]
expression.
Also note that any Esterel program that uses its sequential
variables correctly and has no @es[ρ] expressions either
already has correct binding or can be α-renamed into one
that has correct binding (possibly requiring more wires in
the signals-as-wires analogy). Thus, the restriction that our
calculus handles only programs with correct binding is not
severe.

To understand correct binding, a good first rule to look at
is the @es[seq] rule. It says that the bound variables of
the first sub-expression must be distinct from the free
variables of the second. The only rule that manipulates
binders across a @es[seq] expression is the @rule["merge"]
rule and, based on the definition of @es[E] (in
@figure-ref["fig:supp"]), it can move a @es[ρ] out from the
first sub-expression only. Thus, in order to preserve the
binding structure of the expression as we reduce, we need
only make sure that a @es[ρ] that moves out of the first
sub-expression of a @es[seq] does not capture a variable in
the second sub-expression. The other rules all generally
follow this reasoning process for their premises, where the
case for @es[loop] takes into account the @rule["loop"]
reduction, not the @rule["merge"] reduction.

@figure["fig:cb" "Correct Binding"]{@CB-pict}

@theorem[#:label "thm:cb"]{

 @(equiv
  (list (var-prem p)
        (var-prem q)
        (var-prem C))
  (list (fact-prem (CB (in-hole C p)))
        (fact-prem (⇀ p q)))
  (CB (in-hole (∀x C hole) (∀x q nothing)))
  #:agda-conc
  (CB (in-hole (∀x C hole) (∀x q nothing))) ;; just  avoid `term` making `in-hole` go away
  "⟶₁-preserve-CB")
}

The main result is that reduction preserves correct binding,
no matter where the reduction occurs.
Here @es[C] stands for the compatible context
detailed in @figure-ref["fig:eval"].
The proof is given as @tt{CB-preservation} in the Agda code
in the supplementary material.
