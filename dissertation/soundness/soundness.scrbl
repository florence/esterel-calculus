#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          (only-in
           "../lib/circuit-diagrams.rkt"
           emit-pict nothing)
          "../lib/proof-extras.rkt"
          "../proofs/proofs.scrbl"
          (only-in scribble/manual racket)
          scriblib/figure)

@title[#:style paper-title-style #:tag "just"]{Justifying the Calculus}

The four properties I promise the Calculus for Esterel would have are:
Syntactic, Local, Sound, and Adequate. This section justifies that
the calculus has each of these properties.

@section[#:tag "just:syntactic"]{Justifying Syntactic}

On the surface the calculus is clearly syntactic: it only
deals with the syntax of terms. However there are two
justifications I must make to argue that it true is
syntactic: that the extensions to the language @es[ρ] and
@es[loop^stop] map back to the surface language, and that
the syntax of Kernel Esterel is meaningful when reasoning
about Full Esterel.

@subsection[#:tag "just:syntactic:rho"]{Extensions}


@subsection[#:tag "just:syntactic:full"]{Full Esterel}
Can map back.

@subsubsection[#:tag "just:syntactic:macro"]{Expressibilty}
Macro Expressive (up to trap)

@subsubsection[#:tag "just:syntactic:tasks"]{Tasks}

Tasks are one way that Full Esterel can interoperate with the host language.
Tasks allow Esterel to launch Asynchronous processes within the host language that
can be controlled by 

@section[#:tag "just:local"]{Justifying Local}

Contexts
GO

@section[#:tag "just:sound"]{Justifying Soundness}



As mentioned in @secref["intro:sound"],
soundness here refers to two theorems: Mathematical
Soundness, usually called Consistency, and Soundness with
respect to some external model, usually just called Soundness.


Consistency, at it's core, means that a theory cannot
disagree with itself. In the case of programming language semantics
this can be boiled down to a single property: That @es[eval^esterel] is a function.
Or, more formally:

@proof-splice["consistent"]

The full proof is given in the apendecies as
@proof-ref["consistent"]. Usually, consistency is proven
using the confluence of the underlying reduction semantics.
However, in this case proving confluence is not necessary:
consistency here follows as a correlary of the adequacy of
the calculus. I will discuss this later in
@secref["just:adequacy-and-consistency"].



Soundness, on the other had, relates a calculus to some external definition
of the language which we take to be ground truth for it's behavior. As ground
truth I take the circuit semantics as given by @citet[esterel02],
with some minor modifications that were implemented in the Estere v7 compiler.

@subsection[#:tag "just:sound:compiler"]{The compiler}
@subsection[#:tag "just:sound:pure"]{Loop Free, Pure Esterel}

@subsection[#:tag "just:sound:instants"]{Instants}



@subsection[#:tag "just:sound:CB"]{Names and the correct binding judgment}

@subsection[#:tag "just:sound:thrm"]{The theorem of soundness}

As the calculus relates terms within a single execution,
the statement of soundness will too. An informal justification
for multi-instant reasoning is given in @secref["just:instants"].
The formal statement of soundness is:

@proof-splice["soundness"]

The proof is given in the appendix as @proof-ref["soundness"]. Note that this proof is particulary strong
as it demands that both the constructivity of two terms and the values of TODO something signals.

At it's core the proof proceeds by showing that it holds for
each rule of @es[⇀]. These proofs all rely on the idea that,
because the set of inputs to the circuit is finite.
Therefore each of these proofs---which are given in detail
in @secref["proof:reduction"]---proceeds by induction on the
term to eventually find a concrete circuit. Then the
circuits on the each side are given to a solver which proves
that they are equal.

@subsection[#:tag "just:sound:solver"]{The Solver}


The solver I use is an implementation of the algorithm for
executing constructive circuits given by
@citet[malik-circuit] (and extended by
@citet[constructive-boolean-circuits] to handle registers),
implemented in the language Rosette@~cite[rosette].

Rosette is an domain specific language embeded within
Racket@~cite[plt-tr1], which is designed for defining other domain specific
languages so that the programs written in those language can
be reasoned about using an SMT solver. Specifically Rosette
allows for symbolic execution of programs such that the
result of a program is not a value, but a symbolic
expression which represents the value. This symbolic value
may then be turned into a logic formal that can be reasoned
about using an SMT solver.

In this case I have implement an interpreter using circuits.
Two circuits can then be run on symbolic inputs, and the
statement that the outputs are equal for all possible input
assignments is validated by an SMT solver. The source
for this solver may be found at https://github.com/florence/circuitous/,
and the core of the solver is listed in @secref["ap:solver"].

As an example of how this solver works, take the circuits for
@es[(compile nothing)] and
@es[(compile (emit S))]:

@centered[nothing]
@centered[emit-pict]

@[define x
  @[check
    (define nothing
      (compile-esterel (term nothing)))
    (define emit
      (compile-esterel (term (emit S))))]]

This may be defined using the sovler like so:

@[check
  (define nothing
    (circuit #:inputs (GO) #:outputs (K0)
     (K0 = GO)))
  (define emit
    (circuit #:inputs (GO)
     #:outputs (S K0)
     (S = GO)
     (K0 = GO)))]

Or alternatively they can be defined directly:

@x

We can then get a symbolic interpretation of the circuit. As a trivial example,
we can prove that @es[emit] is equal to itself:

@[check
  (assert-same emit emit)]

However @es[emit] and @es[nothing] are not the same:

@[check
  (eval:error
   (assert-same emit nothing))]

In this case we are given back an unsatisfiable core which is an explicit counterexample
to the assertion that the two circuits are the same. Each input wire is encoded
as two symbolic variables, the @racket[-pos] variant being true if and only if
the wire carries an @es[1], and the @racket[-neg] variant being true if and only
if the wire carries an @es[0].@note{In Racket, true and false are written as @racket[#t]
 and @racket[#f].} If both variables are false, then the wire carries the special value @es[⊥].
Both variables may not be true at the same time. Therefore, the above error message can be interperted
as saying the two models differ when the @es[GO] wire is bottom. This is because in @es[nothing] the
lack of an @es[S] wire means that it is interpreted as always begining @es[0].

Circuitous can also handle register and assertions over multiple instants. Concider:


@[check
  (define delay1
    (circuit #:inputs (a) #:outputs (b)
     (reg in out = a)
     (b = out)))
  (define delay2
    (circuit #:inputs (a) #:outputs (b)
     (reg in1 out1 = a)
     (reg in2 out2 = out1)
     (b = out2)))]

The circuit @racket[delay1] moves it input to its output after one cycle,
and @racket[delay2] moves it's input to its output after two cycles. Circuitous
can show us that these circuits may differ after the first instant, as shown in @figure-ref["delay-check"].

@figure["delay-check"
        "Verifying if two circuits with registers are not the same"
        @[check
          (eval:error
           (assert-same delay1 delay2))]]

In the multi-instant case a new symbolic variable is created
for each input on evey instant. In this case the first line
after model shows us that the circuits differ in the second
instant, where the value of @racket[b] is flipped. This
occurs when @racket[a] is true in the first instant (that is
@racket[pos-a$0] is true).

The last important part of circuitous for the proofs is the
ability to determine constructiveness:

@[check
  (assert-totally-constructive emit)
  (eval:error
   (assert-totally-constructive
    (circuit #:inputs () #:outputs ()
             (a = a))))]

The function @racket[assert-totally-constructive] verifies
that, assuming all inputs are not @es[⊥], then no internal
wires are @es[⊥].@note{When there is an input which is
 @es[⊥], then the circuit is trivially non-constructive,
 therefore this case is uninteresting.}


TODO describe constraints.

@subsection[#:tag "just:sound:lemma"]{Other important lemma's}

θr TODO discuss why

@section[#:tag "just:adequacy"]{Justifying Adequacy}

@proof-splice["comp-ad"]

@subsection[#:tag "just:adq:sketches"]{proof sketches}

@subsection[#:tag "just:adequacy-and-consistency"]{Adequacy and Consistency}.

@section[#:tag "just:knot"]{Putting it together}
@section[#:tag "just:extensions"]{Extensions}
@subsection[#:tag "just:instants"]{Instants}