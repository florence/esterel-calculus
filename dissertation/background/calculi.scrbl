#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/lambda.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          "../lib/rule-figures.rkt"
          "../lib/jf-figures.rkt"
          "../lib/misc-figures.rkt"
          redex/reduction-semantics
          redex/pict
          pict)

@title[#:style paper-title-style #:tag "background-calculi"]{Language Calculi}

This section will give the background about language
calculi. It covers the call-by-value
λ-calculus@~cite[plotkin], small step operational semantics,
evaluation contexts@~cite[felleisen-friedman] and the state
calculus@~cite[felleisen-hieb]. The material summarized here
can be read about in depth in Chapters
I.1, I.3.1, I.3.2, I.4.2, I.4.5, I.4.7, I.5.1, and I.8 of
@cite/title[redex-book].

A semantics is some mapping from (possibly partial) programs to
their meaning. For example: evaluators are
functions mapping programs to the result of running them; and denotational semantics
 give meaning by mapping programs to elements of some external
domain, like the circuit semantics for Esterel. The
semantics I plan to build will give meaning to terms by
mapping them to a set of terms to which they are equivalent---an equivalence
class.
Specifically I will do this by giving a set of axioms that
define an equivalence relation, which will implicitly define
this mapping from terms to sets of terms.

This equivalence relation will let us reason about programs
like we reasoned about arithmetic in grade school: if we can
show two terms are equal, then we can safely replace of
those terms for another in some larger program without
changing its meaning. I refer to this as a calculus (taking
the name from Church's λ-calculus). This means that calculi
are syntactic and local @italic{by construction}.


This section will use as an example the call-by-value
λ-calculus@~cite[plotkin]. The grammar of
this language is:
@[centered
  (vl-append
   @with-paper-rewriters[@render-language[λ_v #:nts '(e)]]
   @[with-paper-rewriters (nt-∈-line "x" "Variable Names" (blank))])]
That is, expressions consist of variables, anonymous functions of one
argument, function applications, and built in constants (which may contain primitive functions). Another
useful grammatical definition is that of a value:
@centered[@with-paper-rewriters[@render-language[λ_v #:nts '(v)]]]
which is to say, just functions and constants. They
represent fully evaluated terms.



@section{Notions of Reduction}

To build a calculus we first build a small@note{Well, okay, @italic{technically}
 the relation is infinite in size, but it has a small number of rules.}
relation called the notions of reduction. This represents
the core notions of computation in this language. I will write this
relation as @|hookup|. In general I will add a superscript to all notation
to show which language they refer to. For example the notions
of reduction for @lam[λ_v] will be written as @lam[⇀λ].
The notions of reduction for @lam[λ_v] are:
@(centered
  (with-paper-rewriters
   (with-continuation-mark 'current-reduction-arrow 'lambda
     (parameterize ([render-reduction-relation-rules #f]
                    [rule-pict-style (render-rules 'λ
                                                   ⇀λ
                                                   `(("" β_v δ))
                                                   calculus-side-condition-beside-rules)])
       (render-reduction-relation ⇀λ)))))

Metafunction application (that is, functions that are outside
of the language rather than functions in the language, e.g. @lam[subst]) is written
@lam/unchecked[(name-of-function args ...)]. The name of this
particular rule is bracketed to the left.

Thus, there are two rules here. The first, @rule["β_v"], handles function application
by substituting a value for a variable in the body of a function. The
second handles primitive function application by delegating out to a metafunction
@es[δ1], which the calculus is parameterized over.

@section{Equality relation}

Using the notions of reduction, a calculus is built as an equality relation
that operates under program contexts, @lam[C]. In this case of @lam[λ_v], these
contexts are:
@[centered
  [with-paper-rewriters
   [render-language λ_v #:nts '(C)]]]

With these contexts the equality is given by the closure of the notions
of reduction under transitivity, reflexively, symmetry, and program contexts:

@[centered
  [with-layout
   `(("step" "refl")
     ("ctx" "trans" "sym"))
   (λ () (render-judgment-form ≡λ))]]

The @rule["step"] rule says that two terms are equal if they are related by the
notions of reduction. The @rule["refl"] rule says that all terms are equal to themselves.
The @rule["trans"] rule says that we can chain reasoning steps together, if @es[a] is equal
to @es[b], and @es[b] is equal to @es[c], then @es[a] must therefore be equal to @es[c]. The @rule["ctx"]
rule says that our reasoning applies in any program context. This is gives us locality, as
we know that we can apply our reasoning anywhere. The final rule, @rule["sym"] says that
if @es[a] is equal to @es[b] then @es[b] is equal to @es[a]. This rule is actually one
of the most important in this relation, as it allows us to run the notions of reduction backwards,
enabling reasoning about many more program transformations (for example, common subexpression elimination
requires this axiom).

@section{Evaluators}

In the end what programs do is run. Therefore a calculus should be able to define
a function which defines what it means for a program to run. I don't, by this,
mean it gives an effective means to compute a program, but rather that it
gives a mathmatical definition of what the results of such a function should be. For example,
for @es[λ_v], the evaluator might be:

@definition[#:notation @lam/unchecked[(evalλ e)]]{
 @[with-paper-rewriters
    [render-metafunction evalλ #:contract? #t]]
}

Which says that if a program is equivalent to a constant,
then that program must evaluate to that constant. If the program is
equivalent to an anonymous function, then the result is the special symbol
@lam[procedure]. Note that it is not a given then @es[evalλ] is a function:
its entirely possible it could map one expression to two different results. This gives us the
definition of consistency for a calculus: The evaluator it defines is a function.

@section{State}

One more important piece of background is how one can handle state in calculi.
State is tricky because it is inherently non-local. The two key pieces for handling state
are evaluation contexts@~cite[felleisen-friedman] and local environments@~cite[felleisen-hieb].
The description I give here is adapted from the state calculus in @citet[felleisen-hieb]. I will
call this state calculus @es[λ_σ].
To start with, we must be able to control the order of evaluation of terms, as state is order
sensitive. To do this we need a new kind of context, which only allows holes in specific places
depending on how far along the program is in evaluating. For @es[λ_σ] they are:
@[centered
  [with-paper-rewriters
   [render-language λ_v #:nts '(E)]]]

Which states that evaluation can take place at the first non-value term of a function application.
From here we add local state to the syntax of the language, represented by the form, @lam[(ρ1 θ e)],
and a form to mutate variables, @es[(set! x e)]:
@[centered
  (vl-append
   [with-paper-rewriters
    [render-language λ_σ #:nts '(e E)]]
   (hbl-append
    (rbl-superimpose
     (hbl-append (es θ) (text " : " (default-style) (default-font-size))))
    (lam x)
    (text " → " (default-style) (default-font-size))
    (lam v)))]

The @lam[ρ] form adds a map @es[θ] to a term. This map associates bound mutable variables with their
current values. From here we can define the notions of reduction:

@(centered
  (with-paper-rewriters
   (with-continuation-mark 'current-reduction-arrow 'state
     (parameterize ([render-reduction-relation-rules #f]
                    [rule-pict-style (render-rules 'σ
                                                   ⇀s
                                                   `(("" β_σ σ D lift δ))
                                                   calculus-side-condition-beside-rules)])
       (render-reduction-relation ⇀s)))))

The first rule is our @lam[β] rule, which handles function application by allocating a new local
environment for that term. The next two rules handle setting and dereferencing variables.
If a @lam[set!] is within an evaluation context of an environment which contains its variable,
that means that the @lam[set!] is the next term to run with respect to that environment.
Therefore it can be run, changing the mapping in the environment to the new value. An arbitrary
value is left in place of the @lam[set!]. Dereferencing works in a similar way:
if a variable is within an evaluation context of its environment, then dereferencing
that variable is the next step than can be taken with respect to that environment.
Environments can be shifted around via the @rule["lift"] rule, exposing new redexs.
The final rule is the same @rule['δ] rule as in @lam[λ_v].


@section{Contextual equivalence}

The strongest notion of equivalence between programs we can have is called contextual
equivalence, which I will write as @lam[≃]. Contextual equivalence
is, generally, defined as a relation between programs which cannot be distinguished in any
context. For example, for @lam[λ_v], we could define contextual equivalence as

@definition[#:notation @lam[(≃λ e_1 e_2)]]{
 @lam[(≃λ e_1 e_2)] if and only if, for all contexts @lam[C],
 @lam/unchecked[(= (evalλ (in-hole C e_1)) (evalλ (in-hole C e_1)))].
}

The definition of contextual equivalence depends on the language in question.

@section{Summary of Notation}
@(define (def-t str) (text str (default-style) (default-font-size)))
@[itemlist
  @item{@[with-paper-rewriters [mf-t "eval"]]: The evaluator for a language.}
  @item{@|hookup|: The notions of reduction for a language.}
  @item{@(with-paper-rewriters (def-t "≡")): The equivalence relation defined by a calculus.}
  @item{@lam[≃]: Contextual Equivalence.}
  @item{@lam[C]: Program Contexts.}
  ]

I will, in general, use superscripts to distinguish evaluators and relations from different languages.