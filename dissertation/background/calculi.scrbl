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
@lam[λ]-calculus@~cite[plotkin], small step operational semantics,
evaluation contexts@~cite[felleisen-friedman] and the state
calculus@~cite[felleisen-hieb]. The material summarized here
can be read about in depth in Chapters
I.1-5, and I.8-I.9 of @cite/title[redex-book]---excluding the
subsections that deal only with proofs---and sections
1 and 4 of @cite/title[felleisen-hieb].

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
this mapping from terms to sets of terms. This set of terms
is defined as the set of terms which the given term can
be simplified to by the axioms of the calculus.

This equivalence relation will let us reason about programs
like we reasoned about arithmetic in grade school: if we can
show two terms are equal, then we can safely replace of
those terms for another in some larger program without
changing its meaning. I refer to kind of equality relation as a calculus (taking
the name from Church's @lam[λ]-calculus).


This section walks through an example of a calculus---the call-by-value
@lam[λ]-calculus@~cite[plotkin], also called @lam[λ_v]---and the key definitions needed for a calculus. The grammar of
this the example language is:
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
relation called the @as-index{notions of reduction}. This represents
the core notions of computation in this language. I will write this
relation as @|hookup|. In general I will add a superscript relations
to show which language they refer to. For example the notions
of reduction for @lam[λ_v] will be written as @lam[⇀λ] (the superscript
drops the @lam[v] to avoid a subscript in a superscript).
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

The left most part of each line is the rule name. Then comes
a pattern which describes what goes on the left of the
relation, what we might think of as its ``input'': functions
applied to a value for @rule['β_v], and primitive constants
applied to many values for @rule['δ]. On the right is a
pattern which describes what is on the right of the relation, what
we might think of at its ``output''. In this case both right
hand sides consist of Metafunctions, that is functions in
our metalanguage, rather than functions in @lam[λ_v].
Metafunction application is written
@lam/unchecked[(name-of-function args ...)]. The @rule['β_v] rule,
which describes anonymous function application, relates the
application of a function to that functions body, but with
every occurrence of the variable @es[subst]ituted with the argument.
The rule @rule['δ] handles primitive function application, by
calling out to the metafunction @lam[δ*], which the calculus
is parameterized over. In a sense this function represents
the ``runtime'' of the @lam[λ_v]. So, for example, if
@lam[const] includes @lam[+] and numbers, then @lam[δ*] would
include a specification of addition.

The relation @lam[⇀λ] can be called the notions of reduction because, at
least so far,
each clause of @lam[⇀λ] is some atomic step in evaluating the program.
Since @lam[λ_v] only contains functions, the only rules in @lam[⇀λ]
handle function application.


@section{Alpha Equivalence}

Not all rules may be computationally relevant, but may instead simply describe
equivalences we wish to hold. For example, a common rule in @es[λ]-calculi
is @rule['α]:
@(centered
  (with-paper-rewriters
   (with-continuation-mark 'current-reduction-arrow 'lambda
     (parameterize ([render-reduction-relation-rules #f]
                    [rule-pict-style (render-rules 'λ
                                                   ⇀α
                                                   `(("" α))
                                                   calculus-side-condition-beside-rules)])
       (render-reduction-relation ⇀α)))))
This rule describes consistent renaming of terms: one term may step to another if
we replace a bound variable with a new name that is not free in the term. We can think
of this rule as describing the renaming refactoring found in IDEs. Two terms
which can step to each other via only the @rule['α] rule are said to be alpha equivalent.

@section{Equality relation}

Using the notions of reduction, a calculus is built as an
equality relation which says, essentially, if some part of
two programs could be run forwards or backwards to new
terms, such that the two programs are become textually equal, then
they two programs must be equivalent.

To start with, we must describe what ``some part of the programs'' means. To do this we use the notion
of a context, which lets us split programs into an inner and outer piece. For a calculus we use
program contexts, @lam[C]. In this case of @lam[λ_v], these
contexts are:

@[centered
  [with-paper-rewriters
   [render-language λ_v #:nts '(C)]]]
This states that we can break a program @lam[e_1] into two
parts, @lam[C] and @lam[e_2], written
@lam[(= e_1 (in-hole C e_2))] by tracing down the top of
@lam[e_1] following the path laid out by the grammar of
@lam[C]. For instance, any program can be broken into the
empty context @lam[hole] and itself:
@lam[(= e_1 (in-hole hole e_1))]. The program
@lam[(+ 3 (+ 1 2))] could be broken into
@lam[(in-hole (+ hole (+ 1 2)) 3)],
@lam[(in-hole (+ 3 hole) (+ 1 2))], and
@lam[(in-hole (+ 3 (+ 1 hole)) 2)], among others.

Note that the program contexts @lam[C] can be generated algorithmically for some non-terminal:
they simply go under every single recursive part of that non-terminal. Therefore
from here on out I will not write out the definitions of @lam[C].

With this in hand we can describe the two axioms of the equality relation which describe evaluating
anywhere in the program:
@[centered
  [with-layout
   `(("step" "ctx"))
   (λ () (render-judgment-form ≡λ))]]
The @rule["step"] rule says that two terms are equal if they
are related by the notions of reduction. The @rule["ctx"]
rule says that our reasoning applies in any program context.
This gives us locality, as we know that we can apply our
reasoning anywhere. From here we turn this into an equality relation: that is we make it transitive, reflexive,
and symmetric:
@[centered
  [with-layout
   `(("refl""trans" "sym"))
   (λ () (render-judgment-form ≡λ))]]
The @rule["refl"] rule says that all terms are equal to
themselves. The @rule["trans"] rule says that we can chain
reasoning steps together, if @lam[A] is equal to @lam[B],
and @lam[B] is equal to @def-t["C"], then @lam[A] must therefore
be equal to @def-t["C"]. The final rule, @rule["sym"] says that
if @lam[A] is equal to @lam[B] then @lam[B] is equal to
@lam[A]. This rule is the one that allows us to ``run''
programs backwards.

Sometimes it is valuable to be able to describe stepping forward.
This relation is given as closure of the notion of reduction under program
contexts---the same as just the @rule['step] and @rule['ctx] rules of
the equivalence relation. This is noted with @[def-t "⟶"], and
will be superscripted to show with language it comes from.
This closure under program contexts is also called the @as-index["compatible closure"].

@section["Reasoning with a calculus"]

Now that we have a calculus, what can we do with it? The
core idea of how to reason with a calculus is the same as
how we reason in our algebra classes from grade school: we
``run'' our core equalities backwards and forwards until we
massage the term into the form we want.

For example, let us say we want to perform something like common
subexpression elimination, and prove that:
@centered[@lam/unchecked[(≡λ (+ (+ 1 1) (+ 1 1)) ((λ x (+ x x)) (+ 1 1)))]]
The reasoning process might go something like this:
@itemlist[
 #:style 'ordered
 @item{By @rule["step"] and @rule["δ"], @lam/unchecked[(≡λ (+ 1 1) 2)].
  That is we can run parts of the program forward one step.}
 @item{By @rule["cxt"] and (1), (twice, by @rule["trans"])
  @lam/unchecked[(≡λ (+ (+ 1 1) (+ 1 1)) (+ 2 2))]. That is we can use
  @rule["ctx"] to substitute @lam[≡λ] terms in a larger term.
  Now we are working with @lam[(+ 2 2)].}
 @item{By @rule["step"] and @rule["β_v"],
  @lam/unchecked[(≡λ ((λ x (+ x x)) 2) (+ 2 2))]. We are just running the
  program forward again.}
 @item{By @rule["sym"] and (3),
  @lam/unchecked[(≡λ (+ 2 2) ((λ x (+ x x)) 2))]. @rule["sym"] lets us take
  our previous ``run forwards'' example and use it to actually
  run backwards. Now we are working with
  @lam/unchecked[((λ x (+ x x)) 2)].}
 @item{By @rule["sym"], @rule["ctx"], (1), and @rule["trans"],
  @lam/unchecked[(≡λ ((λ x (+ x x)) 2) ((λ x (+ x x)) (+ 1 1)))]. We're
  running backwards again, and substituting into a larger
  context. Now we have our final term
  @lam/unchecked[((λ x (+ x x)) (+ 1 1))].}
 ]


@section{Evaluators}

For a calculus to be adequate, it must be able to define
an evaluator for its language. I don't, by this,
mean it gives an effective means to compute a program, but rather that it
gives a mathematical definition of what the results of such a function should be. For example,
the @lam[λ_v] evaluator might be:

@definition[#:notation @lam/unchecked[(evalλ e)]]{
 @(parameterize ([metafunction-pict-style 'left-right/beside-side-conditions])
    @[with-paper-rewriters
      [render-metafunction evalλ #:contract? #t]])
}

Which says that if a program is equivalent to a constant,
then that program must evaluate to that constant. If the program is
equivalent to an anonymous function, then the result is the special symbol
@lam[procedure]. Note that it is not a given that @lam[evalλ] is a function:
it is entirely possible it could map one expression to two different results. This gives us the
definition of consistency for a calculus: the evaluator it defines is a function.



@section{State}

One more important piece of background is how one can handle state in calculi.
State is tricky because it is inherently non-local. The two key pieces for handling state
are evaluation contexts@~cite[felleisen-friedman] and local environments@~cite[felleisen-hieb].
The description I give here is adapted from the state calculus in @citet[felleisen-hieb].
In this section we extend @lam[λ_v] to support state, and call the extension
@lam[λ_σ].
To start with, we must be able to control the order of evaluation of terms, as state is order
sensitive. To do this we need a new kind of context, which only allows holes in specific places
depending on how far along the program is in its evaluation. For @lam[λ_σ] they are:
@[centered
  [with-paper-rewriters
   [render-language λ_v #:nts '(E)]]]
These contexts limit where holes may be place, so that evaluation can only
take place at the first non-value term of a function application.
From here we add local state to the syntax of the language, represented by the form, @lam[(ρ1 θ e)],
and a form to mutate variables, @lam[(set! x e)]:
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

The @lam[ρ] form adds a map @lam[θ] to a term. This map associates bound mutable variables with their
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
value is left in place of the @lam[set!].@note{In the grand tradition of
 The Hitchhikers Guide to the Galaxy, the best arbitrary value is @es[42].} Dereferencing works in a similar way:
if a variable is within an evaluation context of its environment, then dereferencing
that variable is the next step than can be taken with respect to that environment.
Environments can be shifted around via the @rule["lift"] rule, exposing new redexs.
The final rule is the same @rule['δ] rule as in @lam[λ_v].

From here we define the equality relation @lam[≡^σ] the same way we defined @lam[≡λ]:
by closing the notions of reduction over program contexts, transitivity, reflexively,
and symmetry:
@[centered
  [with-layout
   `(("step" "ctx")
     ("refl""trans" "sym"))
   (λ () (render-judgment-form ≡σ))]]

@section{Contextual equivalence}

The strongest notion of equivalence between programs we can have is called contextual
equivalence@~cite[morris], which I will write as @lam[≃]. Contextual equivalence
is, generally, defined as a relation between programs which cannot be distinguished in any
context. For example, for @lam[λ_v], we could define contextual equivalence as

@definition[#:notation @lam[(≃λ e_1 e_2)]]{
 @lam[(≃λ e_1 e_2)] if and only if, for all contexts @lam[C],
 @lam/unchecked[(= (evalλ (in-hole C e_1)) (evalλ (in-hole C e_1)))].
}

The definition of contextual equivalence depends on the language in question.

In general contextual equivalence is a ``stronger''
equivalence relation than the relation defined by a
calculus; however for a calculus to be sound it must be that
@lam[≡] is a subrelation of @lam[≃]. That is, if
@lam/unchecked[(≡λ e_1 e_2)] then it must be that
@lam/unchecked[(≃λ e_1 e_2)], but the converse does not need
to hold.

@section[#:tag "goawaywarning"]{Summary of Notation}
@(define (def-t str)
   (with-paper-rewriters (text str (default-style) (default-font-size))))
@[itemlist
  @item{@lam/unchecked[(name-of-function args ...)]: Metafunction application.}
  @item{@[as-index [with-paper-rewriters [mf-t "eval"]]]: The evaluator for a language.}
  @item{@[as-index |hookup|]: The notions of reduction for a language.}
  @item{@[as-index (with-paper-rewriters (def-t "≡"))]: The equivalence relation defined by a calculus.
  Defined as closure of @[def-t "⇀"] under program contexts, symmetry, reflexivity, and transitivity.}
  @item{@[as-index (with-paper-rewriters (def-t "⟶"))]: The equivalence relation defined by a calculus.
  Defined as closure of @[def-t "⇀"] under program contexts.}
  @item{@[as-index @lam[≃]]: Contextual Equivalence.}
  @item{@[as-index @lam[C]]: Program Contexts.}
  ]

I will, in general, use superscripts to distinguish evaluators and relations from different languages.