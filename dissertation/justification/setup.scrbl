#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          (only-in
           "../lib/circuit-diagrams.rkt"
           emit-pict nothing
           compile-def
           esterel-interface)
          "../lib/proof-extras.rkt"
          (only-in "../proofs/proofs.scrbl")
          (only-in "../notations.scrbl")
          (only-in scribble/manual racket)
          scriblib/figure
          racket/match)

@title[#:style paper-title-style #:tag "just:setup"]{Setup for the proofs}

The justifications for Soundness, Consistency, and Adequacy involve
formal proofs. However these proofs have some require some setup and have
some caveats. The purpose of this section is to give the rest of the setup
needed to understand the statements of the theorems and their proofs.


@section[#:tag "just:sound:compiler"]{The compiler}

The proofs of soundness and adequacy are proved with respect
the circuit semantics of Esterel. This semantics is, in
general, both the ground truth for most other semantics and
guides the actual implementation of Esterel implementation.
The core of this semantics is the compilation function
@es[compile]. This function translates Pure Esterel programs
(That is, programs that to not refer to the host language)
into circuits of the the shape given in
@figure-ref["circ-shape"]. The circuit compiler I describe
here is the same as the one given in @citet[esterel02],
except for two changes in the compilation of @es[par]. These
changes are necessary for soundness, and were implemented in
the Esterel v7 compiler. I will describe them more later.

@figure["circ-shape"
        @list{The shape of circuits returned by @es[(compile p-pure)]}
        (esterel-interface @es[(compile p-pure)])].

The four input wires on the left of the diagram (@es[GO], @es[RES], @es[SUSP], @es[KILL])
are control wires which guide the execution of the circuit. The @es[GO] wire is true
when the circuit is supposed to start for the first time. The @es[RES] wire is true
when the circuit may resume execution in a previous instant (when, say, it has
a register containing an @es[1]). The @es[SUSP] wire is used by the compilation
of @es[suspend] to, well, suspend a term. The @es[kill] wire is used by @es[trap]
and @es[exit] to abort the execution of a circuit.

The two wires on the top @es[E_i] and @es[E_o] represent bundles of wires
that are input and output signals of the term. Any free variable which is used
in an @es[present] will have a corresponding wire in @es[E_i]. Any
free variable which is use in an @es[emit] will have a corresponding
wire in @es[E_o].

The bottom output wires on the right (@es[K0] and friends) are encode the return codes.
The wire @es[K0] is @es[1] when the term completes, @es[K1] is @es[1] when
the term would @es[pause], @es[K2] is @es[1] when the term would exit to the first
@es[trap], etc. Only one of the @es[Kn] wires may be @es[1] at a given time. In circuit speak,
the @es[Kn] wires are a one-hot encoding of the return code.

The final output wire @es[SEL] is @es[1] if there is any register in the circuit which holds a @es[1].
Registers are used to encode whether or not the program @es[pause]ed with the term. That is, each @es[pause]
will generate a register, and that register will have an @es[1] when the term should resume from that @es[pause].

A quick note about these circuits: their activation is
completely controlled by @es[GO], @es[RES], and @es[SEL]: if
@es[GO] and either @es[RES] or @es[SEL] are @es[0], then all
of the output signals and return codes will be @es[0] and
the circuit will be constructive. This is proven formally in
@proof-ref["activation-condition"], and follows fairly
easily by induction. In addition the compilation function
assume that @es[GO] and @es[SEL] are mutually exclusive:
a @es[SEL]ected term may not be started for the first time.
This assumption, however, can be removed with a small
change, which is discussed about in @secref["future"].

@[begin
   (define (circ-fig n)
     (match-define (list _ _ pict circ) (assoc n compile-def))
     (figure (~a "comp:" n)
             @list{The compilation of @pict}
             circ))
 ]

The simplest clause of the compiler is the compilation of @es[nothing], see in @figure-ref["comp:nothing"].
This compilation connect the @es[GO] wire directly to @es[K0], as if @es[nothing] is reached
it immediately terminates. Remember that any wire not draw in the diagram is taken to be @es[0], therefore
this term can never be selected, and can never have a different exit code.

@circ-fig['nothing]

The next simplest compilation clause is @es[exit], which just connects @es[GO] to the return code wire
corresponding to the return code for that @es[exit].

@circ-fig['exit]

Next, we have the compilation of @es[emit], found in
@figure-ref["comp:emit"]. Like @es[nothing], this connects
@es[GO] to @es[K0] as this term terminates immediately. It
also adds the wire @es[So] to the output environment, as
this signal will be emitted immediately when the term
executes. Note that I will always name the output wires for
a signal @es[S] as @es[So], and the input wires @es[Si].

@circ-fig['emit]

The last term without subterms, @es[pause] is also significantly more complex than the others.
It's compilation is in @figure-ref["comp:pause"]. Firstly, the @es[GO] wire is connected
to the @es[K1] wire, as a @es[pause] will, well, pause the first time is reached.
The @es[SEL] wire is fairly simple: it is true when the register is true. The @es[K0] wire
just says that a @es[pause] finishes when it is @es[SEL]ected, and @es[RES]umed. The complex part
goes into determining if the term gets selected. A term is selected if it is not @es[KILL]ed, and
if either it is reached for the first time (@es[GO]) or it was already selected and it is being @es[SUSP]ended,
in which case it's selection status needs to be maintained.

@circ-fig['pause]

The compilation of @es[signal] (@figure-ref["comp:signal"]) is fairly simple: the inner term is compiled,
and the wires for the given signal are re

@circ-fig['signal]

The compilation of @es[present] (@figure-ref["comp:present"]) compiles both terms, and broadcasts all inputs except for @es[GO]
to both subcircuits. All outputs are or'ed. The @es[GO] wire is wire of both subcircuits
is given by the overall @es[GO] and which value of the conditioned signal. The @es[(compile p-pure)]
subcircuit activates if and only if both @es[GO] and @es[Si] are @es[1]. The @es[(compile p-pure)]
subcircuit activates if and only if @es[GO] is @es[1] and @es[Si] is @es[0]. That is a branch is activated
if and only if the @es[present] is activated and the signal is in the corresponding state.

@circ-fig['present]

The compilation of @es[suspend] (@figure-ref["comp:suspend"]) does nothing special to @es[GO]:
remember @es[suspend]ed term's behave normally on the first instant they are reached. The however
the compilation intercepts the @es[RES] wire, and only @es[RES]umes the subcircuit
if the suspension signal @es[S] is @es[0]. If the signal is @es[1] then the circuit is suspended
instead, and this information is passed to the @es[K1] wire. All of this only occurs, however,
if the subcircuit is @es[SEL]ected. If it is not, the @es[RES] and @es[SUSP] wires are suppressed.

@circ-fig['suspend]

The compilation of @es[seq] (@figure-ref["comp:seq"]) wires
the @es[K0] wire of the first subcircuit to the @es[GO] wire
of the second, causing the second subcircuit to start when
the first finishes. The overall @es[K0] wire is thus just
the @es[K0] wire of the second subcircuit, as the @es[seq]
only completes when it does. The remainder of the outputs
are or'ed. and the remainder of the inputs are broadcast to
the subciruits.

@circ-fig['seq]

The compilation of @es[trap] (@figure-ref["comp:trap"])
intercepts the @es[K2] wire (which represents the abortion
of this term) and passes it back to the @es[KILL] wire of
the subcircuit. It then shifts the return codes in the same
way as @es[↓].

@circ-fig['trap]

TODO par

TODO loop

TODO ρ

@section[#:tag "just:sound:pure"]{Pure Esterel}

There is a caveat to the Soundness, Consistency, and Adequacy theorems:
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

@section[#:tag "just:sound:free"]{Loop Free}

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

@section[#:tag "just:sound:instants"]{Instants}


One final caveat: The theorems soundness, consistency, and adequacy
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

@section[#:tag "just:sound:testing"]{Evidence via Testing}

@(require racket/runtime-path racket/system racket/port racket/string racket/format)
@(define-runtime-path loc "../../final-tests/logs/")
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
       (max impure-test-count*
            (* 100000 (floor (/ impure-test-count* 100000))))
       "TODO"))

@(define circuit-test-count
   (if circuit-test-count*
       (max
        circuit-test-count*
        (* 100000 (floor (/ circuit-test-count* 100000))))
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
           multi-instant evaluator for Esterel. This evaluator checks at
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
 of instants.} These tests are to provide evidence for consistency and
adequacy, not just against the circuit semantics but against
real implementations as well. The real implementations are
import because they accept Esterel terms that use host
language expressions, which the circuit compiler does not.
Therefore these tests in particular give evidence that
adequacy holds in the presence of Full Esterel.


In addition I have run @(~a circuit-test-count) random test
which generate a random pure program (with loops), apply a
all rules from the calculus (specifically from @es[⟶], the
compatible closure of @es[⇀]), and then check that the
circuits were equal using the Circuitous library. These
tests provide evidence for soundness, and especially for the
soundness with loops.