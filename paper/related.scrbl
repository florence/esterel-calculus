#lang scribble/base
@(require "cite.rkt"
          "redex-rewrite.rkt"
          scriblib/figure
          (only-in scribble/acmart/lang acks))

@(define |Esterel v5| @nonbreaking{Esterel v5})

@title[#:tag "sec:related"]{Related Work}

Three decades of work on Esterel have resulted in a
diversity of semantic models. A fundamental difference of
our semantics is that ours is a calculus rather than merely
a reduction system---it has an equational theory. In
general, the nature of our semantics makes it better for
discussing transformations to Esterel programs and, more
specifically, it lets us prove equivalences in arbitrary
contexts, like those discussed in @secref["sec:examples"].
By the same token, our semantics is not particularly
well-suited to implementing Esterel.

Prior semantics of Esterel can be broadly categorized as follows:

@itemlist[

 @item{Macrostep operational semantics compute the result
  of an instant in big-step style, where evaluation relates
  the state of a program at the beginning of an instant to the
  state at the end.}

 @item{Microstep operational semantics compute the result
  of an instant as a series of small-step style transitions
  until the instant is considered terminated. Our semantics is
  in this style.}

 @item{Circuit semantics gives meaning to Esterel programs
  by translation to Boolean circuits.}

]

Semantics of Esterel are also classified as logical or
constructive. Logical semantics are simpler, but give
meaning to programs that are logically correct but non-constructive.
Constructive semantics use constructive information
propagation to enforce both@~cite[esterel02].

Finally, semantics of Esterel are distinguished by how much of the
language they cover. Some cover all of Kernel Esterel, while others cover only Pure Esterel,
which omits shared and sequential variables.

@citet[esterel92] give two operational semantics of Esterel, a macrostep
logical semantics called the behavioral semantics and a
microstep logical semantics called the execution
semantics. They have proved these equivalent and, for the latter, proved
a confluence theorem.

@citet[esterel02] gives an update to the logical behavioral (macrostep)
semantics to make it constructive. The logical behavioral semantics requires existence and uniqueness of a behavior, without explaining how it could be computed, while the constructive behavioral semantics introduces @es[Can] to do it in an effective but restricted way.
@citet[esterel02] also gives the state behavioral
semantics, another macrostep semantics.

The constructive operational semantics (COS) first appears in
@citet[optimizations-for-esterel-programs-thesis]'s thesis. It is a microstep
semantics that uses program decorations track control flow and avoid rewriting the program.
The COS model, like the constructive behavioral semantics, avoids giving
meaning to non-constructive programs, but unlike the
behavioral semantics, it provides a guide toward efficient implementation.

Like some of those semantics, our semantics handles the
larger language (Kernel Esterel) and accounts for
constructiveness. Unlike all of those semantics, our
semantics works by term rewriting, substituting
equals for equals and simplifying programs, which makes it
a good basis for proving program fragment equivalences.

Circuit semantics, such at those that appear in
@citet[esterel02] and @citet[compiling-esterel], are the
semantics generally used by Esterel implementations like
Hiphop.js and @|Esterel\ v5|. These implementations use circuits
as an intermediate representation during compilation.

These semantics can be used for program optimization (as ours can too),
but in a different way than ours. Because the translation
to circuits is complex, it is difficult to connect transformations
done at the circuit level back to the source level, so these
semantics would not form a good basis for, say, refactoring tools,
or other more human-centered tasks. Another contrast is that these
semantics are much better suited to whole-program optimizations
(e.g., using existing CAD tools to simplify the circuit) whereas
our semantics is better suited to local transformations.

Additional semantics include @citet[tardieu-deterministic]'s, who
uses a different technique than constructiveness to eliminate
logically incorrect programs. It handles only
Pure Esterel.

Our semantics of Esterel closely follows the work of
@citet[felleisen-hieb] on semantics for programs with state. In
particular, we borrow the idea of internalizing state into terms using a
@es[ρ] term that binds a partial store embedded at any level in
a term. However, unlike Felleisen and Hieb, because of Esterel's
@es[par] construct, we do not have unique decomposition into an
evaluation context and redex. This means that the @rule["merge"] rule can
merge from both sides of a @es[par] into the same position, which
complicates our proofs. Our semantics also has to handle many
Esterel-specific notions, which are not a concern in @citet[felleisen-hieb]'s
work.


@acks{
 Thanks to Daniel Feltey, Christos Dimoulas, and Vincent St-Amour for their
 feedback on drafts of this paper. Thanks to Colin Vidal,
 Gérard Berry, and Manuel Serrano for their help with Hiphop.js,
 Esterel v5 and, more generally, understanding Esterel's
 semantics and feedback on this work. Thanks to Matthias
 Felleisen for his help with how to structure the proofs
 and help understanding the semantics of state. A special
 thanks to Gérard Berry for suggesting that we use Newman's lemma;
 without it we would probably never have finished the proof
 of confluence.
 This work was supported by NSF proposal CCF-1526109.
}

