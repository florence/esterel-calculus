#lang scribble/base
@(require "cite.rkt"
          "redex-rewrite.rkt"
          "calculus-figures.rkt"
          scriblib/figure)

@(define |Esterel v5| @nonbreaking{Esterel v5})

@title[#:tag "sec:related"]{Related Work}

@figure["fig:standard" @elem{Standard Reduction Rules}]{
 @standard-reduction-pict
}

@figure["fig:standard-aux"
        @elem{Standard Reduction Auxiliary Judgments}]{
 @standard-reduction-aux-pict
}

@figure["fig:standard-aux2"
        @elem{Standard Reduction Auxiliary Metafunctions}]{
 @standard-meta-pict
}



@section{Semantics of Esterel}

Three decades of work on Esterel have resulted in a diversity of
semantic models. All of the semantics differ from ours mainly in that
ours is a calculus rather than merely a reduction system---it has
an equational theory. This should make it better for
discussing transformations to Esterel programs.

Prior semantics of Esterel can be broadly categorized as follows:

@itemlist[

    @item{Macrostep operational semantics compute the result of an
    instant in big-step style, where evaluation relates the state of a
    program at the beginning of an instant to the state at the end.}

    @item{Microstep operational semantics compute the result of an
    instant as a series of small-step style transitions until the
    instant is considered terminated. Our semantics is in this style.}

    @item{Circuit semantics gives denotations for Esterel programs in
    terms of Boolean circuits.}

]

Semantics of Esterel are also classified as logical or
constructive. Logical semantics is simpler, but gives
meaning to programs that are logically correct but non-constructive.
Constructive semantics use constructive information
propagation to enforce both@~cite[esterel02].

Finally, semantics of Esterel are distinguished by how much of the
language they cover. Some cover all of kernel Esterel, while others cover only pure Esterel, which omits variables.

@citet[esterel92] give two operational semantics of Esterel, a macrostep
logical semantics called the behavioral semantics and a
microstep logical semantics called the execution
semantics. They have proved these equivalent, and for the latter proved
a confluence theorem.

@citet[esterel02] gives an update to the logical behavioral (macrostep)
semantics to make it constructive. The logical behavioral semantics requires existence and uniqueness of a behavior, without explaining how it could be computed, while the constructive semantics introduces @es[Can] to do it in an effective but restricted way.
@citet[esterel02] also gives two more semantics for Esterel:
The state behavioral
semantics is another macrostep semantics. Unlike the other semantics,
which reduce Esterel programs, the state semantics decorates them with
the equivalent of a program counter. A translation to constructive
circuits gives a denotational semantics for Esterel programs.

The constructive operational semantics (COS) appears in
@citet[optimizations-for-esterel-programs]. Like the state semantics, it
uses program decorations to avoid rewriting the program.
The COS model, like the constructive behavioral semantics, avoids giving
meaning to logically incorrect programs, but unlike the
behavioral semantics, it provides a guide toward efficient implementation.

Circuit semantics, such at those that appear in
@citet[esterel02] and @citet[compiling-esterel], are the
semantics generally used by Esterel implementations like
HipHop and @|Esterel\ v5|. These implementations use circuits
as an intermediate representation during compilation.

Additional semantics include those of @citet[tardieu-deterministic], who
uses a different technique than constructiveness to eliminate
logically incorrect programs. It handles only
pure Esterel.

@section{Semantics of state}

Our semantics of Esterel closely follows the work of
@citet[felleisen-hieb] on semantics for programs with state. In
particular, we borrow the idea of internalizing state into terms using a
@es[ρ] term that binds a partial store embedded at any level in
a term. However, unlike Felleisen and Hieb, because of Esterel's
@es[par] construct, we do not have unique decomposition into an
evaluation context and redex. This means that the @rule["merge"] rule can
merge from both sides of a @es[par] into the same position, which
complicates our proofs.
