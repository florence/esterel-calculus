#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          (only-in
           "../lib/circuit-diagrams.rkt"
           emit-pict nothing)
          "../lib/proof-extras.rkt"
          (only-in "../proofs/proofs.scrbl")
          (only-in "../notations.scrbl")
          (only-in scribble/manual racket)
          scriblib/figure)

@title[#:style paper-title-style #:tag "just"]{Justifying the Calculus}

The four properties I promise the Calculus for Esterel would have are:
Syntactic, Local, Sound, and Adequate. This section justifies that
the calculus has each of these properties.


@section[#:tag "just:syntactic"]{Justifying Syntactic}

One could argue that the Calculus is not syntactic, in that it
does not literally talk about the syntax of the programs one writes
in Full Esterel. However I would argue that it is ``syntactic enough'',
which is to say it is purely syntactic except in a few places where
something new has been added by necessity.

The first place it steps outside the syntax of normal
Esterel is in adding @es[GO].@note{Not that environments
 that contain @es[WAIT] can be completely removed by running
 the @rule["emit"] and @rule["signal"] rules backwards,
 therefore they will never show up at the "end" of a chain of
 reasoning.} The calculus needs @es[GO] to be sound and
adequate because it needs to localize the notion of whether
or on control reaches a particular point. So while this is a
minor deviation from the syntax of normal Esterel, it is
necessary@note{In fact, I would argue that the @es[GO] is
 the novel element I have added it make a calculus which is
 sound @italic{and} adequate in the first place.} and does
not stray to far from the syntax of programs.

The same can be said of @es[loop^stop]: while it is not part
of the original Esterel syntax, it is necessary to reason about programs
which have not been proven to contain instantaneous loops. In essence
@es[loop^stop] lets us track potential instantaneous loop errors
my adding a new form. As this is a minor, and necessary, addition
I do not find that it detracts from the overall syntacticness of
the calculus.

TODO How to talk about full esterel and missing features in the context

@section[#:tag "just:local"]{Justifying Local}

Justifying that the calculus allows for local reasoning is
not difficult. The relation @es[≡] contains a context rule
which states that the the rules of the calculus apply in any
program context. I would argue that this is the definition
of locality in terms of calculi.

@section[#:tag "just:setup"]{Setup for the proofs}


@subsection[#:tag "just:sound:compiler"]{The compiler}

TODO

@subsection[#:tag "just:sound:pure"]{Pure Esterel}

There is a caveat to the proofs of both soundness and adequacy theorems:
They both work on Pure Esterel programs. I find this,
however, to not restrict the validity of the theorems much.

Pure Esterel, the subset of Esterel which does not handle
Host Language Programs,@note{ That is Pure Esterel is the
 part of Esterel which contains only Esterel terms, not a
 ``side-effect free'' fragment of Esterel} defines the
essence of Esterel. The addition forms either add
traditional programming language variables (@es[var]), or
extend the reasoning mechanism used for signals to allow
them to carry values (@es[shared]). These extensions either
re-use much of the mechanisms that are proven correct by the
soundness and adequacy proofs, or are traditional enough
that there is little interesting added when reasoning about
them. Therefore I would argue that a the proofs for Pure
Esterel intuitively generalize to Esterel with Host Language
terms.

@subsection[#:tag "just:sound:free"]{Loop Free}

My proofs are also only give on the fragment of Pure Esterel
which does not contain loops. This is for a similar reason
to using Pure Esterel: Proving the calculus correct on loop
is difficult but adds little value. At the core, this is
because of Schizophrenia (See @secref["back:esterel:schizo"]
for a refresher). The calculus, rather trivially, does not
suffer from schizophrenia because it duplicates the loop
body on reduction, preventing conflict between different
iterations of the loop. Handling schizophrenia in the
circuit semantics is a more complicated problem. While one
could just duplicate the loop body@note{This is the solution
 that the random tests for my calculus use.} this is makes
the compilation of the program quadratic, which is rather
terrible. Much work has gone in to handling loop compilation
correctly and efficiently (such as chapter 12 of
@citet[esterel02], as @citet[new-method-schizophrenic]), and
thus I defer to the community on the correct way to handle
loop compilation, and do not touch on it here. Therefore I
defer to the community on showing that duplicating loop
bodies is equivalent to these more complex methods, and do
not touch on them in my proofs. In short, because 1) the
primary issues with loops are schizophrenia and
instantaneous loop bodies, 2) my calculus handles these in a
fairly intuitive and simple way, and 3) proving correctness
of these cases would be tedious, difficult, and probably not
very informative, I simply postulate the correctness of the
calculus on loops.

@subsection[#:tag "just:sound:instants"]{Instants}


One final caveat: The proofs of soundness and adequacy
restrict themselves to a single instant of execution. I
postulate, however, that they hold between instants. This is
because the inter-instant translation function
@es[next-instant] is nearly identical to the same function
from @citet[esterel02]@note{Section 8.3, page 89 of the
 current draft} which as been proven correct by Lionel Rieg
in Coq.@note{ Unfortunately, as of the writing of this
 dissertation this work is unpublished.}, but with trivial
extensions to handle @es[loop^stop] and @es[ρ]. Therefore I feel comfortable postulating
that the calculus is correct across instants.

@subsection[#:tag "just:sound:testing"]{Evidence via Testing}

@(require racket/runtime-path racket/system racket/port racket/string racket/format)
@(define-runtime-path loc "../..//final-tests/logs/")
@(define impure-test-count*
   (string->number
    (string-trim
     (call-with-output-string
      (lambda (o)
        (parameterize ([current-directory loc]
                       [current-output-port o])
          (system
           "racket -e \"(+ `for x in *ternal*; do grep \"running test\" $x | tail -1; done | awk '{ print $3 }'` )\"")
          ))))))

@(define circuit-test-count*
   (string->number
    (string-trim
     (call-with-output-string
      (lambda (o)
        (parameterize ([current-directory loc]
                       [current-output-port o])
          (system
           "racket -e \"(+ `for x in *circuit*; do grep \"running test\" $x | tail -1; done | awk '{ print $3 }'` )\"")
          ))))))


@;{@(unless (number? impure-test-count*)
   (error 'arg "expected a test count, got ~a" test-count))}
@;{@(unless (number? circuit-test-count*)
   (error 'arg "expected a test count, got ~a" test-count))}

@(define impure-test-count
   (if impure-test-count*
       (* 100000 (floor (/ impure-test-count* 100000)))
       "TODO"))

@(define circuit-test-count
   (if circuit-test-count*
       (* 100000 (floor (/ circuit-test-count* 100000)))
       "TODO"))
@(define |Esterel v5| @nonbreaking{Esterel v5})

@(define itemlistheader bold)
   
While I have presented the above as caveats, I have evidence
that the postulates above hold, in addition to evidence that
my theorems are correct beyond the proofs themselves. This
evidence comes from random testing. To do this, I provide
the following:

@itemlist[@item{@itemlistheader{Redex COS model} I built a
           Redex@~cite[redex-book] model of the COS semantics. The semantics is a
           rule-for-rule translation of the COS semantics from @citet[compiling-esterel],
           aside from some minor syntax differences. This provides an executable model
           of the COS semantics.}
          @item{@itemlistheader{Redex calculus model} I have also build
           a Redex model of the calculus. This defines two relations:
           the core relation of the calculus @es[⇀], and a new
           relation @es[⇁] which gives an evaluation strategy for @es[⇀].
           The @es[⇁] relation and the @es[next-instant] function is used to define a
           multi-evaluator for Esterel. This evaluator checks at
           every reduction step that the step taken by @es[⇁] is also
           in @es[⇀].}
          @item{@itemlistheader{Redex/Hiphop.js bridge} 
           HipHop.js is an Esterel implementation embedded into Javascript. We
           built a library that can translate Redex expressions into
           Hiphop.js@~cite[hiphop] programs and then evaluate them.@note{Special thanks to Jesse Tov
           for helping out with this.}
           There is also a
           compiler form a subset of Hiphop.js to the Redex model of the calculus,
           allowing many of the Hiphop.js tests be run directly against the calculus. This translator does not accept
           all Hiphop.js programs, because Hiphop.js programs embed
           JavaScript code as the Redex model cannot evaluate the
           JavaScript.}
          @item{@itemlistheader{Redex/@|Esterel\ v5| bridge}
           There is also built a translator that produces @|Esterel\ v5| programs
           from Redex terms.}
          @item{@itemlistheader{Redex circuit compiler}
           Finally I have built a compiler from pure Esterel (with loops)
           to circuits, which runs on top of the circuit library Circuitous.}]


I have run @(~a impure-test-count) tests which on Full
Esterel programs which test that the Hiphop.js,
@|Esterel\ v5|, the COS, the calculus, and the circuit
compiler agree on the result of running programs for
multiple instants.@note{Each test runs for a random number
 of instants.} These tests are to provide evidence for
adequacy, not just against the circuit semantics but against
real implementations as well. The real implementations are
import because they accept Esterel terms that use host
language expressions, which the circuit compiler does not.
Therefore these tests in particular give evidence that
adequacy holds in the presence of Full Esterel.


In addition I have run @(~a circuit-test-count) random test
which generate a random pure program (with loops), apply a
random rule from the calculus, and then checked that the
circuits were equal using the Circuitous library. These
tests provide evidence for soundness, and especially for the
soundness with loops.


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

The full proof is given in the appendices as
@proof-ref["consistent"]. Usually, consistency is proven
using the confluence of the underlying reduction semantics.
However, in this case proving confluence is not necessary:
consistency here follows as a corollary of the adequacy of
the calculus. I will discuss this later in
@secref["just:adequacy-and-consistency"].

Soundness, on the other had, relates a calculus to some external definition
of the language which we take to be ground truth for it's behavior. As ground
truth I take the circuit semantics as given by @citet[esterel02],
with some minor modifications that were implemented in the Esterel v7 compiler.



@subsection[#:tag "just:sound:thrm"]{The theorem of soundness}

As the calculus relates terms within a single execution,
the statement of soundness will too. An informal justification
for multi-instant reasoning is given in @secref["just:instants"].
The formal statement of soundness is:

@proof-splice["soundness"]

The proof is given in the appendix as
@proof-ref["soundness"]. To pick the statement apart, it
says that if two terms are @es[≡] the, when we restrict
ourselves to looking at a single instant, the compilation of
those circuits is @es[≃^circuit].

This proof proceeds by induction over the structure of the
equality relation @es[≡]. Thus, the majority of the work in
the proof goes into showing that it holds for each rule of
@es[⇀]. These proofs all rely on the idea that, because the
set of inputs to the circuit is finite. Therefore each of
these proofs---which are given in detail in
@secref["proof:reduction"]---proceeds by induction on the
term to eventually find a concrete circuit. Then the
circuits on the each side are given to a solver which proves
that they are equal.

@subsection[#:tag "just:sound:solver"]{The Solver}

The solver I use is an implementation of the algorithm for
executing constructive circuits given by
@citet[malik-circuit] (and extended by
@citet[constructive-boolean-circuits] to handle registers),
implemented in the language Rosette@~cite[rosette].

Rosette is an domain specific language embedded within
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
Both variables may not be true at the same time. Therefore, the above error message can be interpreted
as saying the two models differ when the @es[GO] wire is bottom. This is because in @es[nothing] the
lack of an @es[S] wire means that it is interpreted as always beginning @es[0].

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
for each input on every instant. In this case the first line
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

Finally, both of @racket[assert-totally-constructive]
and @racket[assert-same] may take in assumptions about the environment
which can be used to constrain what they check. For example:
@[check
  (assert-same
   #:constraints '(not a)
   delay1 delay2)
  (eval:error
   (assert-same 
    #:constraints 'a
    delay1 delay2))]

Which show that @racket[delay1] and @racket[delay2] are
equal when @racket[a] is always false, but not equal when
@racket[a] is always true.


@subsection[#:tag "just:sound:lemma"]{Important lemma's}

This section will discuss the most interesting or
informative lemma's needed to prove soundness of the various
rules of @es[⇀]. May of the lemma's are trivial or uninformative, and so will not be discussed here.
The interested reader may seem them in all of their gory detail in @secref["proof:sound"]
and @secref["proof:reduction"].

A first informative proof to look at is the proof that @rule["trap"] is sound:

@proof-splice["trap"]

The full proof may be found at @proof-ref["trap"]. The first
thing to note is that this proof does not require the
premise that we are in the first instant. Many of the
equations do not touch @es[pause], and therefore are not
sensitive to instants. This proofs proceeds by induction over
the structure of @racket[stopped]. The two base cases
are @es[(= stopped nothing)] and @es[(= stopped (emit 0))].
These case simply invoke the solver, for example:
@check[(assert-same
        (compile-esterel (term (trap nothing)))
        (compile-esterel (term (harp nothing))))]
The last case proceeds by induction on @es[(emit n)] for @es[(> n 0)].
It's relatively easy to argue that if the rule is sound for @es[n],
its sound for @es[(Σ n 1)].

The next proof of interest is the proof that @rule["emit"] is sound.
This proof is more complex because it must deal with both evaluation contexts
and environments.

@proof-splice["emit"]

The full proof is given in @proof-ref["emit"]. This proof
proceeds by induction over @es[E-pure]. The base case is
rather trivial: when @es[(= E-pure hole)] the two circuits
look identical, as the @es[1] from the @es[GO] wire is
directly connected to the @es[S] wire. The inductive case is
more interesting. The proof uses the idea that evaluation
contexts correspond exactly to the set of contexts such that
in @es[(compile (in-hole E-pure p-pure))], the @es[GO] and
signal wires from the top of the term are passed, unchanged,
to @es[p-pure]. This is stated formally with these two
lemma's:

@proof-splice["S-maintains-across-E"]
@proof-splice["GO-maintains-across-E"]

The full proof of which are given, in
@proof-ref["S-maintains-across-E"] and
@proof-ref["GO-maintains-across-E"]. Both lemma's follow
directly by induction on @es[E-pure] and the definition of
@es[compile]. These two lemma's together give that the
inputs of the circuit are unchanged. The remainder of the
inductive case follows that the @es[So] wires are always
@es[or]ed with each other, therefore a @es[1] in any subterm
leads to the overall signal wire being @es[1].

The last proof I will describe here is the proof for @rule["is-absent"].

@proof-splice["is-absent"]

The full proof is given in @proof-ref["is-absent"]. This
proof is one of key proofs which requires the premise that
we are in the first instant. This is because this proof
relies on @es[Can], which assumes that it is in the first
instant. Other variations of @es[Can], such as those from
the State Behavioral Semantics@~cite[esterel02] or the
Constructive Operation
Semantics@~cite[optimizations-for-esterel-programs-thesis]
drop this assumption by reflecting register state back in
the syntax of the program. However since our semantics
relies on an inter-instant translation function, we restrict
this proofs to a single instant.

This proof is essentially just a chaining of several other lemmas. As
with @proof-ref["emit"], @proof-ref["S-maintains-across-E"] and @proof-ref["GO-maintains-across-E"]
are used to shed the evaluation contexts in the rule. From there the proof mostly follows from the following
lemma:

@proof-splice["Can-S-is-sound"]

To understand this proof statement, I must explain a little bit of notation. The phrase
@es[(binds (compile p-pure) θ)] exists to tie the syntactic world of Esterel to the circuit world.
In, in essence, states that the knowledge contained in the map @es[θ] also holds when reasoning about the circuit.
Formally, it is defined as:

@extract-definition["binds"]

With this in hand we can interpret
@proof-ref["Can-S-is-sound"] and
@proof-ref["Can-rho-S-is-sound"]: If we restrict our view to the
first instant, and the environment given to @es[Can] is
valid with respect to the circuit, then @es[Can] accurately
predicts when signal wires will be set to @es[0] (or rather,
the complement of @es[Can] accurately predicts this).

The proof of @proof-ref["Can-S-is-sound"] proceeds by
induction over the structure of @es[p-pure], following the
cases laid out by @es[Can]. The majority of this lemma
consists of tracing how the definition of can walks the
program, and compares that to the structure of the generate
circuit. In most cases the result follows fairly directly.
In the end there are two interesting cases: @es[signal] and
@es[seq]. The @es[signal] case in interesting only when the
bound signal is not in the result of @es[Can]. In this case
we must use our inductive hypothesis to show that the output
of the bound signal is @es[0], and use that to invoke our
inductive hypothesis to show that the goal signal is also
@es[0]. The @es[seq] case of @es[Can] relies on the return
codes. Thus we use an pair auxiliary lemmas to reason about
those codes:

@proof-splice["Can-K-is-sound"]

Which is similar to @proof-ref["Can-S-is-sound"], except that it
tells us which return code wires must be @es[0]. The proof
of which is essentially the same as @proof-ref["Can-S-is-sound"].

These two lemmas also have counterparts for @es[Can-θ]:

@proof-splice["Can-rho-S-is-sound"]
@proof-splice["Can-rho-K-is-sound"]

However as @es[Can-θ] is essentially just repeated applications of the @es[signal]
case of @es[Can], these proofs are relatively uninteresting.

@section[#:tag "just:adequacy"]{Justifying Adequacy}

@proof-splice["comp-ad"]

@subsection[#:tag "just:adq:sketches"]{proof sketches}

@subsection[#:tag "just:adequacy-and-consistency"]{Adequacy and Consistency}.

@section[#:tag "just:knot"]{Putting it together}
@section[#:tag "just:extensions"]{Extensions}
@subsection[#:tag "just:instants"]{Instants}