#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/cite.rkt"
          (only-in
           "../lib/circuit-diagrams.rkt"
           emit-pict nothing
           compile-def
           esterel-interface
           synchronizer)
          racket/format
          "../lib/proof-extras.rkt"
          (only-in "../proofs/proofs.scrbl")
          (only-in "../notations.scrbl")
          (only-in scribble/manual racket)
          scriblib/figure
          racket/match)

@title[#:style paper-title-style #:tag "just:setup"]{Setup for the proofs}

The justifications for Soundness and Adequacy involve formal
proofs. The purpose of this section is to give
the setup needed to understand the statements of the
theorems and their proofs.


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
changes are necessary for soundness, and were derived from
the Esterel v7 compiler. I will describe them more later.


@figure["circ-shape"
        @list{The shape of circuits returned by @es[(compile p-pure)]}
        (esterel-interface @es[(compile p-pure)])]

The circuit compilation function, in essence, takes the program graphs described
in @secref["back:esterel:cannot"], and expresses them as a circuit. The circuits
are more complex, as they handle more of Esterel than the simple diagrams I used before,
but at their core they expressed the same execution model.
The four input wires on the left of the diagram (@es[GO], @es[RES], @es[SUSP], @es[KILL])
are control wires which guide the execution of the circuit. The @es[GO] wire is true
when the circuit is supposed to start for the first time---it corresponds
to an coming control edge that connects to the start of the program in the program graph model.
The @es[RES] wire is true
when the circuit may resume execution in a previous instant (when, say, it has
a register containing an @es[1])---it corresponds to an control edge that
connects the ``output'' from a pause. The @es[SUSP] wire is used by the compilation
of @es[suspend] to suspend a term. The @es[KILL] wire is used by @es[trap]
and @es[exit] to abort the execution of a circuit. Neither @es[SUSP] nor @es[KILL]
are expressed in the program graph model.

The two wires on the top @es[E_i] and @es[E_o] represent
bundles of wires that are input and output signals of the
term. Any free variable which is used in an @es[if]
will have a corresponding wire in @es[E_i]. Any free
variable which is use in an @es[emit] will have a
corresponding wire in @es[E_o].

The bottom output wires on the right (@es[K0] and friends) are encode the return codes.
The wire @es[K0] is @es[1] when the term completes, @es[K1] is @es[1] when
the term would @es[pause], @es[K2] is @es[1] when the term would exit to the first
@es[trap], etc. Only one of the @es[Kn] wires may be @es[1] at a given time. In circuit speak,
the @es[Kn] wires are a one-hot encoding of the return code.

The final output wire @es[SEL] is @es[1] if there is any register in the circuit which holds a @es[1].
Such a circuit is said to be @es[SEL]ected.
Registers are used to encode whether or not the program @es[pause]d with the term. That is, each @es[pause]
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

The simplest clause of the compiler is the compilation of @es[nothing], shown in @figure-ref["comp:nothing"].
Its compilation connects the @es[GO] wire directly to @es[K0], as when @es[nothing] is reached
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

The last term without subterms, @es[pause], is also significantly more complex than the others.
It's compilation is in @figure-ref["comp:pause"]. Firstly, the @es[GO] wire is connected
to the @es[K1] wire, as a @es[pause] will, well, pause the first time is reached.
The @es[SEL] wire is similarly straightforward: it is true when the register is true. The @es[K0] wire
just says that a @es[pause] finishes when it is @es[SEL]ected, and @es[RES]umed. The complex part
goes into determining if the term gets selected. A term is selected if it is not @es[KILL]ed, and
if either it is reached for the first time (@es[GO]) or it was already selected and it is being @es[SUSP]ended,
in which case it's selection status needs to be maintained.

@circ-fig['pause]

The compilation of @es[signal] (@figure-ref["comp:signal"]) is fairly simple: the inner term is compiled,
and the wires for the given signal are connected to each other.

@circ-fig['signal]

The compilation of @es[if] (@figure-ref["comp:present"]) compiles both terms, and broadcasts all inputs except for @es[GO]
to both subcircuits. All outputs are or'ed. The @es[GO] wire of both subcircuits
is given by the overall @es[GO] and value of the conditioned signal. The @es[(compile p-pure)]
subcircuit activates if and only if both @es[GO] and @es[Si] are @es[1]. The @es[(compile p-pure)]
subcircuit activates if and only if @es[GO] is @es[1] and @es[Si] is @es[0]. That is a branch is activated
if and only if the @es[present] is activated and the signal is in the corresponding state.

@circ-fig['present]

The compilation of @es[suspend] (@figure-ref["comp:suspend"]) does nothing special to @es[GO]:
remember @es[suspend]ed term's behave normally on the first instant they are reached. The however
the compilation intercepts the @es[RES] wire, and only @es[RES]umes the subcircuit
if the suspension signal @es[S] is @es[0]. If the signal is @es[1] then the circuit is @es[SUSP]ended
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
the subcircuit, killing it when this @es[trap] catches it corresponding
@es[exit]. It then shifts the return codes in the same
way as @es[↓].

@circ-fig['trap]

The @es[par] circuit (@figure-ref["comp:par"]) circuit is
the most complex of the compilation clauses, and has two
changes from the compiler given in @citet[esterel02]. To
start with, the easy part: The @es[GO], @es[RES], @es[SUSP]
and @es[E_i] wires are broadcast to the subcircuits. The @es[SEL] and
@es[E_o] wires are the or'ed from the subcircuits. The complex part
is in handling the return codes and the @es[KILL] wire.

@circ-fig['par]

To start with, the return codes are joined together by a
synchronizer, which is given in @figure-ref["comp:sync"].
The synchroniziser implements the @es[max] operation, as is
used in @es[Can]. That is, the return code for the overall
circuit is the max of the return code of the subcircuits
(the @es[Ln] and @es[Rn] wires). However this is complicated
by multi-instant execution: special behavior is needed if
one branch finished in a previous instant. In this case the
return code of the live branch must be used. This is handled
by the @es[LEM] and @es[REM] wires, which encode if the
other branch is the only live branch. Which is to say,
@es[LEM] is true if and only if the circuit
is resuming, the @es[p-pure] branch is dead, and the @es[q-pure] branch
is @es[SEL]ected. The reverse holds for @es[REM]. There @es[LEM]
and @es[REM] wires make it look like the dead branch has exit code @es[0],
which, as the lowest return code, causes the synchronizer to give
the other branches return code.

The last part of the synchronizer is the handling of
@es[KILL]. The compilation of @es[par] needs to account for
if one branch has an exit code greater than @es[1], which
must abort the other branch. Normally this would be handled
by the compilation of @es[trap], but in this case we would
loose local reasoning if we did that, as we do not know if
the program is in fact, closed, by a @es[trap]. Therefore
both subcircuits are killed if the outer @es[KILL] wire is
@es[1], or if the over all return code is @es[2] or greater.


@figure["comp:sync" "The parallel synchronizer" synchronizer]

The two changes to this from the compiler in @citet[esterel02] are the @es[KILL]
wire including the return codes, and the definition of the @es[LEM] and @es[REM] wires.
The old compiler would have broadcast the @es[KILL] wires directly to the subcircuit.
In addition it would have defined @es[(= REM (not (or GO p-SEL)))] (and @es[LEM]
using @es[q-SEL]). Both of these definitions result in unsoundness under local rewrites
that should hold. Both of these changes were used in the Esterel v7 compiler, however
they have not yet been published anywhere.

The change to the @es[REM] and @es[LEM] wires can be
explained by noticing that it we expect it to be the case
that @centered[@es[(≃^esterel (trap (par (exit 0) pause)) nothing)]]
as this circuit will always abort, and immediately catch the
@es[exit]. Therefore we want
@centered[@es[(≃^circuit (compile (trap (par (exit 0) pause))) (compile nothing))]]
to hold. However in this equivalence did not hold in the
@citet[esterel02] compiler, specifically in the case where
@es[(= GO ⊥)]. In that case both @es[LEM] and @es[REM] are
@es[⊥], causing @es[K2] to be @es[⊥]. However in the circuit
for @es[nothing], @es[K2] is defined to be @es[0]. The
Esterel v7 compiler handles this case correctly.

The change to the @es[KILL] wire can be seen by a similar
example. We expect
@centered[@es[(≃^esterel (par (exit 2) pause) (exit 2))]] for a similar
reason as before. As before, this means we want
@centered[@es[(≃^circuit (compile (par (exit 2) pause)) (compile(exit 2)))]]
to hold. With the @citet[esterel02] compiler, however, we are free
to let @es[KILL] be @es[0], even when @es[GO] is @es[1]. This means that in the second
instant the @es[pause] is @es[SEL]ected. However there is no @es[pause] in @es[(exit 2)],
therefor its @es[SEL] wire must be @es[0]. The new compiler handles this correctly by
killing the other branch of the @es[par] even if the outer @es[KILL] wire is @es[0].

Note that these two issues both rely on both subcircuits
being simultaneously active at some point to trigger the change in
behavior. As @es[par] is the only case where two
subcircuits can be active simultaneously, this is the only
case that requires this special care.

The compilation of @es[ρ] follows along similar lines to the
compilation of @es[signal]: we take one signal at a time out
of the environment and connect its input wire to it's output
wire (@figure-ref["comp:non-empty-rho"]), with one exception. The wire connection goes
through @es/unchecked[(compile statusr)] which connects the
two wires if @es[(= statusr unknown)]. However if
@es[(= statusr present)] then the connection is cut, and the
input wire is defined to be @es[1].

@circ-fig['non-empty-rho]

Once all signals have been compiled, the @es[A] part is
compiled in a similar manner
(@figure-ref["comp:empty-rho"]). If the @es[A] is @es[WAIT],
the @es[GO] wire is taken from the environment. If @es[A] is
@es[GO], then the @es[GO] wire will be defined to be @es[1].

@circ-fig['empty-rho]

@section[#:tag "just:sound:solver"]{The Circuit Solver, Circuitous}

To reason about circuits in a more automated fashion, I have
implemented a symbolic reasoning engine---a solver---for
concrete circuits. The solver I use is an implementation of
the algorithm for executing constructive circuits given by
@citet[malik-circuit] (and extended by
@citet[shiple-constructive-circuit] to handle registers)
in the language Rosette@~cite[rosette].

Rosette is an domain specific language embedded within
Racket@~cite[plt-tr1], which is designed for defining other
domain specific languages so that the programs written in
those language can be reasoned about using an SMT solver.
Specifically Rosette allows for symbolic execution of
programs such that the result of a program is not a value,
but a symbolic expression which represents the value. This
symbolic value may then be turned into a logic formal that
can be given to an SMT solver.

In this case I have implement an interpreter for circuits.
Two circuits can then be run on symbolic inputs, and the
statement that the outputs are equal for all possible input
assignments is validated by an SMT solver. The source for
this solver may be found at
https://github.com/florence/circuitous/, and the core of the
solver is listed in appendix C.

As an example of how this solver works, take the circuits
for @es[(compile nothing)] and @es[(compile (emit S))]:

@centered[nothing]
@centered[emit-pict]

@[define x
  @[check
    (define nothing
      (compile-esterel (term nothing)))
    (define emit
      (compile-esterel (term (emit S))))]]

This may be defined using the sovler like so:@note{@racket[term] is used to
construct a term in a language, in this Esterel. It comes from the semantics
engineering library Redex@~cite[redex-book].}

@[check
  (define nothing
    (circuit #:inputs (GO) #:outputs (K0)
     (K0 = GO)))
  (define emit
    (circuit #:inputs (GO)
     #:outputs (S^o K0)
     (S^o = GO)
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
lack of an @es[So] wire means that it is interpreted as always beginning @es[0].

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
@racket[pos-a$0] is @racket[#t]).

The last important part of Circuitous for the proofs is its
ability to determine constructiveness:

@[check
  (assert-totally-constructive emit)
  (eval:error
   (assert-totally-constructive
    (circuit #:inputs () #:outputs ()
             (a = a))))]

The function @racket[assert-totally-constructive] verifies
that, assuming all inputs are not @es[⊥], then no internal or output
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


@section[#:tag "just:sound:instants"]{On Instants}

One final caveat: The theorems soundness, consistency, and
adequacy restrict themselves to a single instant of
execution. I postulate, however, that they hold between
instants. The inter-instant translation function
@es[next-instant] is nearly identical to the same function
from @citet[esterel02]@note{Section 8.3, page 89 of the
 current draft} which as been proven correct@note{
 Specifically, it is proven that, up to bisimilarity, a
 program passed through @es[next-instant] under the
 Constructive Semantics remains the same program with respect
 to the state semantics.} by Lionel Rieg in Coq.@note{
 Unfortunately, as of the writing of this dissertation this
 work is unpublished.}, but with extensions to handle
@es[loop^stop] and @es[ρ]. I also provide evidence
that these theorems hold over multiple instants in
@secref["just:sound:testing"].


@section{Agda Codebase}

Some proofs I reference are not given in this document. Instead they are given in a separate Agda code base.
This code base is an old attempt to prove the correctness of a previous version of the calculus@~cite[florence-2019].
While the calculus has since changed, @es[Can] has not. Therefore I re-use some of the proofs from
that work which relate to @es[Can].


@section{Notation}

At times my theorem statements will say something to the
effect of @italic{For all @es[p-pure]}. This is a pun which
is meant to read as @italic{For all terms @es[p-pure] drawn
 from the set of terms @es[p-pure]}. Similarly I will
sometimes say @italic{For all
 @es[(= r-pure (in-hole E-pure p-pure))]}. This is shorthand
for @italic{For all @es[r-pure], @es[E-pure], and
 @es[p-pure] such that
 @es[(= r-pure (in-hole E-pure p-pure))]}.