#lang scribble/base
@(require "calculus-figures.rkt"
          "util.rkt"
          "redex-rewrite.rkt"
          scriblib/figure
          rackunit
          racket/list
          redex/reduction-semantics
          esterel-calculus/redex/model/potential-function
          esterel-calculus/redex/model/calculus
          esterel-calculus/redex/model/lset
          (except-in esterel-calculus/redex/model/shared
                     quasiquote))

@title[#:tag "sec:stdred"]{Standard Reduction}

Our standard reduction exists only in Redex (not in Agda,
unlike the rest of the semantics). We use it to
help with our testing process, as described in @secref["sec:testing"].

@Figure-ref["fig:standard"] shows the reduction rules. There
are four differences between the rules of the calculus and
the rules of the standard reduction. First, expressions
reduce only if they have an outer @es[ρ]. Second, the
@rule["absence"] and @rule["readyness"] rules set as many
signals or variables as they can in a single step. Third,
the @rule["absence"] and @rule["readyness"] rules use
@es[Can-θ] in the calculus and @es[Can] in the standard
reduction. In the standard reduction, the extra analysis
that @es[Can-θ] performs is not necessary. Finally, the
rules are oriented so that at most one applies at each step.
There are two pieces to this orientation: restricting the
context in which the rules may apply and restricting the
@rule["absence"] and @rule["readyness"] rules so they apply
only when no other rule applies.

To understand how the rules are oriented, consider
the @rule["absence"] and @rule["readyness"] rules. They
require the body to be either done or blocked, where blocked
is given in @figure-ref["fig:standard-aux"]. It captures
when an expression cannot reduce because it needs the value of
a signal or shared variable that is not known or @es[ready].

The context restriction is captured by the @es[(good θ D)]
judgment. The judgment is designed to restrict the choice of
sub-expression in @es[par] terms so only one side is
considered for reduction. There are three @es[par] rules:
one that always allows reductions in the left-hand side, and
two others that allow reduction on the right, but only when
the left is either done or blocked.

Otherwise, the reduction rules in the standard reduction
parallel those in calculus. Of course, we do not take the
compatible closure; instead we just reduce in evaluation contexts.

There is one subtle point of this standard reduction: it
is not the standard reduction relation for our calculus, but
rather the one for a slightly smaller
calculus. In particular, it does not bypass
constructiveness, unlike the calculus (as discussed in
@secref["sec:constructiveness"]). It
reaches a stuck state instead.

@;{ It is also important to consider the
 exponential behavior with respect to this reduction. In the
 example from @secref["sec:can"]:

@(define/esblock start-t start-e
   (signal S1
           (seq (present S1 pause nothing)
                (signal S2 (present S2
                                    (emit S1)
                                    nothing)))))
@(define/esblock S2-unknown-t S2-unknown-e
   (signal S1
           (seq (present S1 pause nothing)
                (ρ (mtθ+S S2 unknown)
                   (present S2
                            (emit S1)
                            nothing)))))
@(define/esblock S2-absent-t S2-absent-e
   (signal S1
           (seq (present S1 pause nothing)
                (ρ (mtθ+S S2 absent)
                   (present S2
                            (emit S1)
                            nothing)))))

@(define/esblock S1-unknown-t S1-unknown-e
   (ρ (mtθ+S S1 unknown)
      (seq (present S1 pause nothing)
           (ρ (mtθ+S S2 absent)
              (present S2
                       (emit S1)
                       nothing)))))

@(define/esblock S1-absent-t S1-absent-e
   (ρ (mtθ+S S1 absent)
      (seq (present S1 pause nothing)
           (ρ (mtθ+S S2 absent)
              (present S2
                       (emit S1)
                       nothing)))))

@(define/esblock redC-t redC-e
   (signal S1 (seq (present S1 pause nothing) hole)))


@(begin
   (define start-inner (third (third start-t)))
   (define S2-u-inner (third (third S2-unknown-t)))
   (define S2-a-inner (third (third S2-absent-t)))
   (check-equal?
    (term (in-hole ,redC-t ,start-inner))
    start-t)
   (check-equal?
    (term (in-hole ,redC-t ,S2-u-inner))
    S2-unknown-t)
   (check-equal?
    (term (in-hole ,redC-t ,S2-a-inner))
    S2-absent-t)

   (check-not-false
    (member
     S2-u-inner
     (apply-reduction-relation R start-inner)))
   (check-not-false
    (member
     S2-a-inner
     (apply-reduction-relation R S2-u-inner)))
   (check-not-false
    (member
     S1-unknown-t
     (apply-reduction-relation R S2-absent-t)))
   (check-not-false
    (member
     S1-absent-t
     (apply-reduction-relation R S1-unknown-t))))

@start-e

the exponential behavior is not strictly required to make progress on reducing the term in the
calculus. The calculus can use the compatible closure to set @es[S2] to @es[absent], then reanalyze
the term with @es[Can] to set @es[S1] to absent. Specifically:

@start-e

reduces by @rule["signal"] and @rule["absence"] under the compatible context

@redC-e

to


@S2-absent-e

Which can then reduce by @rule["signal"] and @rule["absence"] under the compatible context @es[hole]
to

@S1-absent-e

From here the program is no longer blocked on the value of @es[S1].

However the standard reduction cannot jump ahead to set @es[S2] to @es[absent]. Instead Can's
exponential behavior will reanalyze the body of the program with @es[S2] as @es[absent], avoiding
the need for the extra reduction steps.
}
