#lang scribble/base
@(require "jf-figures.rkt"
          "redex-rewrite.rkt"
          "cite.rkt"
          "util.rkt"
          "agda-fact.rkt"
          scriblib/figure
          rackunit
          redex/reduction-semantics
          (except-in esterel-calculus/redex/model/shared quasiquote)
          pict
          (prefix-in standard: esterel-calculus/redex/model/reduction))


@title[#:tag "sec:cb"]{Reincarnation, Schizophrenia, and Correct Binding}


@(define/esblock loop-term loop-term/block
   (loop
    (signal SZ
      (seq pause
           (emit SZ)))))

@;;; these are not used in the current version
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

The @es[signal] form seems to be something close to a
variable binding form, familiar from conventional λ-calculus
based programming languages. It is, however, not the same
and a significant source of subtlety in Esterel. The Esterel
community has explored these issues in great detail and in
this section, we try to bring across the basic points and
then explain how our calculus handles them.

@right-figure[#:lines 6 #:caption "A Schizophrenic Loop" #:tag "ex:schizophrenic"]{
 @loop-term/block
}

The two central issues are the phenomena of schizophrenic
and reincarnated signals. To understand them, first recall the central tenant of Esterel signals: every signal must have exactly one value in a given instant. Now, consider the
example program in @figure-ref["ex:schizophrenic"]. During
the first instant of execution the signal @es[SZ] will be
absent, as the program pauses before emitting it. In the
next instant we pick up where we left off. The first thing
that happens is that we emit @es[SZ]. Then the loop
body restarts. Because we have re-entered the loop
body and encountered the @es[signal] expression afresh, the
@es[SZ] should now be absent. But this means that the signal
@es[SZ] has two different values in a single instant! 

In the literature, signals which are duplicated by a loop
body in within one instant are called
@italic{reincarnated}. If a reincarnated signal obtains
different values in each of its incarnations, it is called
@italic{schizophrenic}. Schizophrenic signals, however, merely appear
to violate the single-value-per-instant rule. Because instantaneous loops are
banned, the number of times a loop body can be entered is bounded.
This means that the number of reincarnations of any signal is also bounded.
Therefore we consider each incarnation to, in fact, be a separate signal,
removing the apparent violation.

This resolution shows up directly in Esterel
compilers and circuit semantics. Naive treatment of schizophrenic
signals can cause unstable loops in the corresponding
circuit, breaking the guarantee that all constructive
programs translate to stable circuits. Therefore, many Esterel compilers duplicate
parts of loop bodies with schizophrenic signals to remove
the apparent violation of the single-value-per-instant rule,
avoiding cross-loop cycles@~cite[new-method-schizophrenic esterel02 compiling-esterel]. In short, each incarnation of a signal
gets a separate wire.

Esterel semantics such as the Constructive Operational
Semantics@~cite[optimizations-for-esterel-programs-thesis]
and the Constructive Behavioral Semantics@~cite[esterel02]
take a different approach, handling
such signals by carefully arranging to ``forget'' a
schizophrenic signal's first value when the second one is
needed.

Our semantics takes an approach inspired by the circuit
perspective, meaning we do not treat signals in a
conventional way. More precisely, we do not assume the
variable convention@~cite[barendregt], nor do we include an
α rule. Indeed, we think of signals as if they name wires.

This perspective means that schizophrenic and reincarnated
signals are, at first glance, handled very simply. We just
duplicate the bodies of loops in the @rule["loop"] rule, so
each signal will end up in a different @es[ρ], potentially
bound to a different value---akin to the strategy that circuit semantics employ.
This approach, however, does raise a significant
concern: what happens if the @rule["merge"] rule
moves @es[ρ] expressions in such a way that the environment
captures variables it did not bind before? Our calculus avoids this problem by working only
with programs that have @italic{correct binding}, as
captured by the @es[CB] judgment form in
@figure-ref["fig:cb"]. (The @es[CB] judgment also
ensures that sequential variables are used in at most one
branch of any @es[par], which is not related to the concerns
of schizophrenia, but does ensure determinism and is
convenient to include here.)

To understand the correct binding judgment, first look at
the @es[seq] rule. It says that the bound signals of the
first sub-expression must be distinct from the free
signals of the second. Since the @rule["merge"] rule moves
binders based on the definition of @es[E] (in
@figure-ref["fig:supp"]), it can move a @es[ρ] out from the
first sub-expression only. Thus, in order to preserve the
binding structure of the expression as we reduce, we need
only make sure that a @es[ρ] that moves out of the first
sub-expression of a @es[seq] does not capture a signal in
the second sub-expression, which is precisely what the
premise avoids.

The other rules all generally follow this reasoning process
for their premises. The @es[suspend] rule's premise follows
exactly that reasoning, as binder may be lifted out past the
@es[S]. The @es[par] rule's second and third premises also
follow exactly the same reasoning. The first premise of
@es[par] is necessary to avoid the situation where the same
signal is bound in both branches and then is lifted out
from both. The fourth premise ensures that sequential
variables are used properly.

The @es[loop] rule must ensure that the bound and free
signals of its subexpression do not overlap, as it reduces
by duplicating its first subexpression into a
@es[loop^stop], which acts like a @es[seq] expression (so
the intuition for @es[seq] applies, but with both
subexpressions being the same one). Similarly, because
@es[(loop^stop p q)] behaves like @es[(seq p (loop q))], the
premises of its rule are just the premises of the @es[seq]
and @es[loop] rules, combined.

@figure["fig:cb" "Correct Binding"]{@CB-pict}

@theorem[#:label "thm:cb" #:break? #t]{
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

This theorem states that, no matter which context an
expression reduces in (with @es[C] as given in
@figure-ref["fig:eval"]), if the expression had correct
binding before reduction, it does afterwards, too. The proof
is given as @text{⟶₁}@tt{-preserve-CB} in the Agda code in
the supplementary material. From this we conclude that
programs with correct binding cannot exhibit incorrect variable capture.

It should also be noted that any Esterel program that uses
its sequential variables correctly either already has
correct binding or can be renamed into one that has correct
binding (introducing new wires, of course) before reducing
the program. Thus, the restriction that our calculus handles
only programs with correct binding is not severe, as any
already correct program can be transformed into
one which is well behaved in our calculus.
