#lang scribble/base

@(require "agda-fact.rkt"
          "util.rkt"
          "redex-rewrite.rkt"
          pict
          scriblib/figure
          syntax/parse/define
          (only-in scribble/core style table-cells))

@(begin
   (provide equiv-1)
   (define-simple-macro
     (equiv-1 with-rewriters:id)
     (equiv
      #:with-rewriters with-rewriters
      (list (var-prem S_1 #:with-rewriters with-rewriters)
            (var-prem S_2 #:with-rewriters with-rewriters)
            (var-prem p #:with-rewriters with-rewriters))
      (list (newline-prem)
            (fact-prem (CB p) #:with-rewriters with-rewriters)
            (newline-prem))
      (≡e () () ()
          (signal (∀x S_1 S_1)
            (signal (∀x S_2 S_2)
              (∀x p nothing)))
          (signal (∀x S_2 S_2)
            (signal (∀x S_1 S_1)
              (∀x p nothing))))
      "ex9")))

@(begin
   (provide equiv-2)
   (define-simple-macro
     (equiv-2 with-rewriters:id)
     (equiv
      #:with-rewriters with-rewriters
      (list (var-prem S #:with-rewriters with-rewriters)
            (var-prem p #:with-rewriters with-rewriters)
            (var-prem q #:with-rewriters with-rewriters))
      (list (newline-prem)
            (fact-prem (CB p) #:with-rewriters with-rewriters)
            (newline-prem))
      (≡e () () ()
          (signal (∀x S S)
            (seq (emit (∀x S S))
                 (present
                  (∀x S S)
                  (∀x p nothing)
                  (∀x q nothing))))
          (signal (∀x S S)
            (seq (emit (∀x S S))
                 (∀x p nothing))))
      "\\ { S p q -> ex1 S p q }")))

@(begin
   (provide equiv-3)
   (define-simple-macro
     (equiv-3 with-rewriters)
     (equiv
      #:with-rewriters with-rewriters
      (list (var-prem S #:with-rewriters with-rewriters)
            (var-prem p #:with-rewriters with-rewriters)
            (var-prem q #:with-rewriters with-rewriters))
      (list (fact-prem (CB q) #:with-rewriters with-rewriters)
            (newline-prem)
            (fact-prem (L¬∈ S (->S (Can p (mtθ+S S unknown))))
                       #:with-rewriters with-rewriters)
            (newline-prem)
            (fact-prem (L¬∈ S (->S (Can q (mtθ+S S unknown))))
                       #:with-rewriters with-rewriters)
            (newline-prem))
      (≡e () () ()
          (signal (∀x S S)
            (present (∀x S S)
                     (∀x p nothing)
                     (∀x q nothing)))
          (signal (∀x S S)
            (∀x q nothing)))
      "\\ { S p q ->  λ x → ex2 S p q [] (CBsig x) }")))

@(begin
   (provide equiv-4)
   (define-simple-macro
     (equiv-4 with-rewriters)
     (equiv
      #:with-rewriters with-rewriters
      (list (var-prem S #:with-rewriters with-rewriters)
            (var-prem p #:with-rewriters with-rewriters)
            (var-prem q #:with-rewriters with-rewriters))
      (list (newline-prem)
            (fact-prem (CB (par p q)) #:with-rewriters with-rewriters)
            (newline-prem))
      (≡e () () ()
          (signal (∀x S S)
            (par (seq
                  (emit (∀x S S))
                  (∀x p nothing))
                 (∀x q nothing)))
          (signal (∀x S S)
            (seq (emit (∀x S S))
                 (par (∀x p nothing)
                      (∀x q nothing)))))
      "\\ { S p q -> ex3 S p q }")))

@(begin
   (provide equiv-5)
   (define-simple-macro
     (equiv-5 with-rewriters)
     (equiv
      #:with-rewriters with-rewriters
      (list (var-prem n #:with-rewriters with-rewriters)
            (var-prem p #:with-rewriters with-rewriters)
            (var-prem q #:with-rewriters with-rewriters))
      (list (newline-prem)
            (fact-prem (CB p) #:with-rewriters with-rewriters)
            (newline-prem)
            (fact-prem (done q) #:with-rewriters with-rewriters)
            (newline-prem)
            (fact-prem (≡e () () () p q) #:with-rewriters with-rewriters)
            (newline-prem))
      (≡e () () ()
          (trap
           (par (exit (∀x "(suc n)" 1))
                (∀x p nothing)))
          (par (exit (∀x n 1))
               (trap (∀x p nothing))))
      "ex4")))

@(begin
   (provide equiv-6)
   (define-simple-macro
     (equiv-6 with-rewriters)
     (equiv
      #:with-rewriters with-rewriters
      (list (var-prem p_1 #:with-rewriters with-rewriters)
            (var-prem p_2 #:with-rewriters with-rewriters)
            (var-prem p_3 #:with-rewriters with-rewriters)
            (var-prem S #:with-rewriters with-rewriters))
      (list (newline-prem)
            (fact-prem (L¬∈ S (->S (Can p_1 (mtθ+S S unknown))))
                       #:with-rewriters with-rewriters)
            (newline-prem)
            (fact-prem (L¬∈ S (->S (Can p_2 (mtθ+S S unknown))))
                       #:with-rewriters with-rewriters)
            (newline-prem)
            (fact-prem (CB (seq (signal S
                                  (present S p_1 p_2))
                                p_3))
                       #:with-rewriters with-rewriters)
            (newline-prem))
      (≡e () () ()
          (ρ · (seq (signal S
                      (present S
                               (∀x p_1 nothing)
                               (∀x p_2 nothing)))
                    (∀x p_3 nothing)))
          (ρ · (signal S
                 (present S
                          (seq (∀x p_1 nothing) (∀x p_3 nothing))
                          (seq (∀x p_2 nothing) (∀x p_3 nothing))))))
      "\\ { p q r S -> ex8 S p q r }")))

@figure["fig:equivalences" "Equivalences Provable in our Calculus"]{
 @tabular[#:style (style #f (list (table-cells (list (list (style #f '(baseline))
                                                           (style #f '(baseline))
                                                           (style #f '(baseline))
                                                           (style #f '(baseline)))
                                                     (list (style #f '(baseline))
                                                           (style #f '(baseline))
                                                           (style #f '(baseline))
                                                           (style #f '(baseline)))))))
          (list (list
                 @theorem[#:label "thm:one" #:break? #t]{@(equiv-1 with-paper-rewriters)}
                 @theorem[#:label "thm:two" #:break? #t]{@(equiv-2 with-paper-rewriters)}
                 @theorem[#:label "thm:three" #:break? #t]{@(equiv-3 with-paper-rewriters)}
                 'cont)
                (list
                 @theorem[#:label "thm:four" #:break? #t]{@(equiv-4 with-paper-rewriters)}
                 @theorem[#:label "thm:five" #:break? #t]{@(equiv-5 with-paper-rewriters)}
                 @theorem[#:label "thm:six" #:break? #t]{@(equiv-6 with-paper-rewriters)}
                 'cont))]
}

@title[#:tag "sec:examples"]{What the Calculus Can and Cannot Prove}

Our semantics lends itself to establishing
equivalences between program fragments because
any two expressions that are @es[≡e] to each other
always produce the same result in the evaluator:

@theorem[#:label "thm:equivimplieseval" #:break? #t]{
@(equiv
  (list (var-prem p)
        (var-prem θ_1)
        (var-prem 𝕊_1)
        (var-prem q)
        (var-prem θ_2)
        (var-prem 𝕊_2))
  (list (newline-prem)
        (fact-prem (CB (ρ θ_1 p)))
        (newline-prem)
        (fact-prem (≡e () () () (ρ θ_1 p) (ρ θ_2 q)))
        (newline-prem)
        (fact-prem (Eval () () () p θ_1 𝕊_1))
        (fact-prem (Eval () () () q θ_2 𝕊_2))
        (newline-prem))
  (same 𝕊_1 𝕊_2)
  "≡ₑ=>eval")
 }
The proof of this is a straightforward consequence of @es[≡e]
being consistent; the proof is given as @tt{≡@|sub-e|=>eval}
in the Agda code in the supplementary material.

The remainder of this section explores various equivalences
(shown in @figure-ref["fig:equivalences"])
as well as some limitations of the calculus. Their proofs
are all given in @tt{calculus-examples.agda} in the
supplementary material.

The first example, @theorem-ref["thm:one"], shows that we can rearrange signal forms.
This example works well in our calculus. It requires only that
the body expression has correct binding, allowing us to
rearrange adjacent @es[signal] forms arbitrarily.

Next, @theorem-ref["thm:two"] shows that if an @es[emit] is followed by a
@es[present], the @es[present] can always be replaced by
the taken branch.
This example exposes a first limitation of the calculus.
Although it is still true, our calculus cannot prove this
equivalence without the @es[signal] form being visible in an
evaluation context surrounding the @es[seq] form.

In a dual to @theorem-ref["thm:two"], @theorem-ref["thm:three"] shows that
if we know that neither branch of the
@es[present] expression can @es[emit] @es[S], we can replace
it with the absent branch.

@Theorem-ref["thm:four"] lets us lift a @es[seq] expression that starts
with an @es[emit] out of a @es[par] branches. Intuitively,
this is a consequence of Esterel's deterministic
parallelism. Because @es[emit] does not block, we can do it
in parallel to @es[q] or before @es[q] starts, whichever
is more convenient.

When a @es[trap] is outside a @es[par], our calculus
allows us to push the @es[trap] inside,
in some situations. @Theorem-ref["thm:five"] is one such.
This calculation requires @es[p] to be equivalent
to some @es[done] expression @es[q], but that is a weakness
of our calculus. In general, that is not required for the
equivalence to be true.

@Theorem-ref["thm:six"] shows a restricted situation in which we
can prove that we can push an @es[seq] expression inside
a @es[present].
In the general case, this equivalence is true, even without
the @es[signal] form or the @es[ρ] expression outside. Our
calculus cannot prove it, however, because it needs an outer
@es[ρ] expression in order to perform a @rule["merge"] in
the middle of the proof.

We explored a calculus that includes a “lifting” rule that
allows us to move a @es[ρ] term up and down in an evaluation
context. This rule makes it difficult to establish
confluence of the calculus, however, as the would-be lifting
rule and the @rule["merge"] rule interact with each other in
complex ways. In particular, our evaluation contexts do not
have unique decomposition, due to @es[par]. Accordingly, a
use of the lifting rule from one side of a @es[par] expression
can block a use of the @rule["merge"] rule from the other side.
We conjecture that a lifting rule would be confluent, but have
not proven it.
