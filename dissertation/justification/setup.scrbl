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
           synchronizer
           compile-go-pict
           compile-wait-pict
           compile-present-pict
           compile-bot-pict)
          racket/format
          "../lib/proof-extras.rkt"
          (only-in "../proofs/proofs.scrbl")
          (only-in "../notations.scrbl")
          (only-in scribble/manual racket)
          scriblib/figure
          racket/match
          redex/pict
          pict)

@title[#:style paper-title-style #:tag "just:setup"]{Setup for the proofs}

The purpose of this section is to give
the setup needed to understand the statements of the
theorems and their proofs.
To start with, the proofs in this section are only
for the pure loop free portion of Esterel. However
some other proofs in this document are defined on
the full kernel. To distinguish these I use
the superscript @def-t["p"] to denote pure, loop free
terms (e.g @es[p-pure], @es[q-pure]). Similarly contexts over pure, loop free programs
are labeled with the same superscript (e.g. @es[E-pure]). These pure terms also may
only contain the control variable @es[WAIT]. In some cases I will need to discuss
terms which may have the control variable set to @es[GO]. I will write these terms
as @es[p-pure+GO]. @Figure-ref["pure-terms"] gives the grammars for these terms.

@[figure
  "pure-terms"
  "Flavors of loop-free, pure terms"
  [with-paper-rewriters
   [ht-append
    [render-language esterel-eval #:nts '(E-pure-loop)]
    [render-language esterel-eval #:nts '(p-pure-loop q-pure-loop r-pure-loop)]
    [render-language esterel-eval #:nts '(p-pure+GO-loop)]]]]
    


@section[#:tag "just:sound:compiler"]{The compiler}

The proofs of soundness and adequacy are proved with respect
the circuit semantics of Esterel. This semantics is, in
general, the ground truth semantics and
guides the actual implementation of an Esterel compiler.
The core of this semantics is the compilation function
@es[compile]. This function translates Pure Esterel programs
into circuits of the the shape given in
@figure-ref["circ-shape"]. The circuit compiler I describe
here is the same as the one given in @citet[esterel02],
except for two changes in the compilation of @es[par]. These
changes are necessary for soundness, and were derived from
the Esterel v7 compiler. I will describe them more later.


@figure["circ-shape"
        @list{The shape of circuits returned by @es[(compile p-pure)]}
        (esterel-interface @es[(compile p-pure)])]

The circuit compilation function, in essence, expresses the causality graphs described
in @secref["back:esterel:cannot"] as a circuits. The circuits
are more complex, as they handle more of Esterel than the causality diagrams do,
but at their core they have the same execution model.
The four input wires on the left of the diagram in @figure-ref["circ-shape"] (@es[GO], @es[RES], @es[SUSP], @es[KILL])
are control wires which guide the execution of the circuit. The @es[GO] wire is true
when the circuit is supposed to start for the first time---it corresponds
to an coming control edge that connects to the start of the program in the causality graph model.
The @es[RES] wire is true
when the circuit may resume execution in a previous instant (when, say, it has
a register containing an @es[1])---it corresponds to an control edge that
connects start node to a @es[pause]. The @es[SUSP] wire is used by the compilation
of @es[suspend] to suspend a term. The @es[KILL] wire is used by @es[trap]
and @es[exit] to abort the execution of a circuit. Neither @es[SUSP] nor @es[KILL]
are expressed in the causality graph model.

The two wires on the top @es[E_i] and @es[E_o] represent
bundles of wires that are input and output signals of the
term. Any free signal which is tested by an @es[if]
will have a corresponding wire in @es[E_i]. Any free
signal which occurs in an @es[(emit S)] will have a
corresponding wire in @es[E_o].

The bottom output wires on the right (@es[K0] et al.) encode the return codes.
The wire @es[K0] is @es[1] when the term completes, @es[K1] is @es[1] when
the term would @es[pause], @es[K2] is @es[1] when the term would exit to the first
@es[trap], etc. Only one of the @es[Kn] wires may be @es[1] at a given time. In circuit speak,
the @es[Kn] wires are a one-hot encoding of the return code.

The final output wire @es[SEL] is @es[1] if there is any register in the circuit which holds a @es[1].
Such a circuit is said to be selected.
Registers are used to encode whether or not the program @es[pause]d with the term. That is, each @es[pause]
will generate a register, and that register will have an @es[1] when the term should resume from that @es[pause].

A quick note about these circuits: their activation is
completely controlled by @es[GO], @es[RES], and @es[SEL]: if
@es[GO] and either @es[RES] or @es[SEL] are @es[0], then all
of the output signals and return codes will be @es[0] and
the circuit will be constructive. This is proven formally in
@proof-ref["activation-condition"], and follows fairly
easily by induction. In addition the compilation function
assumes that @es[GO] and @es[SEL] are mutually exclusive:
a selected term may not be started for the first time.
This assumption, however, can be removed with a small
change, which is discussed about in @secref["future"].

@[begin
   (define (circ-fig n)
     (match-define (list _ _ pict circ) (assoc n compile-def))
     (figure (~a "comp:" n)
             @list{The compilation of @pict}
             circ))
 ]

The simplest clause of the compiler is @es[(compile nothing)], shown in @figure-ref["comp:nothing"].
Its compilation connects the @es[GO] wire directly to @es[K0], as when @es[nothing] is reached
it immediately terminates. Remember that any wire not draw in the diagram is taken to be @es[0], therefore
this term can never be selected, and can never have a different exit code.
  
@circ-fig['nothing]

The next simplest compilation clause is @es[exit], which just @es[GO] to corresponding return code wire
for that @es[exit] code.

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
Its compilation is in @figure-ref["comp:pause"]. Firstly, the @es[GO] wire is connected
to the @es[K1] wire, as a @es[pause] will pause the first time is reached.
The @es[SEL] wire is similarly straightforward: it is true when the register is true. The @es[K0] wire
just says that a @es[pause] finishes when it is selected and resumed. The complex part
goes into determining if the term will be selected in the next instant.
The register will get a @es[1] if it is not killed, and
if either it is reached for the first time (@es[GO]) or it was already selected and it is being resumed,
in which case it's selection status needs to be maintained.

@circ-fig['pause]

The compilation of @es[signal] (@figure-ref["comp:signal"])
is fairly simple: the inner term is compiled, and the wires
for the given signal are connected to each other, and
removed from the input and output signal sets.

@circ-fig['signal]

The compilation of @es[if] (@figure-ref["comp:present"]) compiles both terms, and broadcasts all inputs except for @es[GO]
to both subcircuits. All outputs are or'ed. The @es[GO] wire of both subcircuits
is given by the overall @es[GO] and value of the conditioned signal. The @es[(compile p-pure)]
subcircuit activates if and only if both @es[GO] and @es[Si] are @es[1]. The @es[(compile p-pure)]
subcircuit activates if and only if @es[GO] is @es[1] and @es[Si] is @es[0]. That is a branch is activated
if and only if the @es[if] is activated and the signal is in the corresponding state.

@circ-fig['present]

The compilation of @es[suspend] (@figure-ref["comp:suspend"]) does nothing special to @es[GO]:
remember @es[suspend]ed terms behave normally on the first instant they are reached. However
the compilation intercepts the @es[RES] wire, and only resumes the subcircuit
if the suspension signal @es[S] is @es[0]. If the signal is @es[1] then the circuit is resumed
instead, and this information is passed to the @es[K1] wire. All of this only occurs, however,
if the subcircuit is selected. If it is not, the @es[RES] and @es[SUSP] wires are suppressed.

@circ-fig['suspend]

The compilation of @es[seq] (@figure-ref["comp:seq"]) wires
the @es[K0] wire of the first subcircuit to the @es[GO] wire
of the second, causing the second subcircuit to start when
the first finishes. The overall @es[K0] wire is thus just
the @es[K0] wire of the second subcircuit, as the @es[seq]
only completes when it does. The remainder of the outputs
are or'ed, and the remainder of the inputs are broadcast to
the subciruits.

@circ-fig['seq]

The compilation of @es[trap] (@figure-ref["comp:trap"])
intercepts the @es[K2] wire (which represents the abortion
of this term) and passes it back to the @es[KILL] wire of
the subcircuit, killing it when this @es[trap] catches its corresponding
@es[exit]. It then shifts the return codes in the same
way as @es[↓].

@circ-fig['trap]

The @es[par] circuit (@figure-ref["comp:par"]) circuit is
the most complex of the compilation clauses, and has two
changes from the compiler given in @citet[esterel02]. To
start with, the inputs part: The @es[GO], @es[RES], @es[SUSP]
and @es[E_i] wires are broadcast to the subcircuits. The @es[SEL] and
@es[E_o] wires are the or'ed from the subcircuits. The complex part
is in handling the return codes and the @es[KILL] wire.

@circ-fig['par]

To start with, the return codes are joined together by a
synchronizer, which is given in @figure-ref["comp:sync"].
The synchronizer implements the @es[max] operation, as is
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
is selected. The reverse holds for @es[REM]. There @es[LEM]
and @es[REM] wires make it look like the dead branch has exit code @es[0],
which, as the lowest return code, causes the synchronizer to output
the other branches return code.

The last part of the synchronizer is the handling of
@es[KILL]. Compilationing @es[par] must account for the scenario where
one branch has an exit code greater than @es[1], which
must abort the other branch. Normally this would be handled
by the compilation of @es[trap], but in this case we would
loose local reasoning if we did that, as we do not know if
the program is in fact, closed, by a @es[trap]. Therefore
both subcircuits are killed if the outer @es[KILL] wire is
@es[1], or if the over all return code is @es[2] or greater.


@figure["comp:sync" "The parallel synchronizer" synchronizer]

The two changes to this from the compiler in @citet[esterel02] are the @es[KILL]
wire including the return codes, and the definition of the @es[LEM] and @es[REM] wires.
These changes are to handle a violation of soundness, and
so are discussed in detail  @secref["just:sound:changes"].


The compilation of @es[ρ] follows along similar lines to the
compilation of @es[signal]: we take one signal at a time out
of the environment and connect its input wire to it's output
wire (@figure-ref["comp:non-empty-rho"]), with one exception. The wire connection goes
through @es/unchecked[(compile statusr)] which connects the
two wires if @es[(= statusr unknown)]. However if
@es[(= statusr present)] then the connection is cut, and the
input wire is defined to be @es[1]. This is shown in @figure-ref["status"].
                    
@circ-fig['non-empty-rho]

@figure["status"
        "Compiling statuses"
        (vl-append
         (hc-append
          (hbl-append (es/unchecked (compile unknown))
                      (es =))
          compile-bot-pict)
         (hc-append
          (hbl-append (es/unchecked (compile present))
                      (es =))
          compile-present-pict))]

Once all signals have been compiled, the @es[A] part is
compiled in a similar manner
(@figure-ref["comp:empty-rho"]). If the @es[A] is @es[WAIT],
the @es[GO] wire is taken from the environment. If @es[A] is
@es[GO], then the @es[GO] wire will be defined to be @es[1].
This is shown in @figure-ref["ctrl"].

@circ-fig['empty-rho]

@figure["ctrl"
        "Compiling control variables"
        (vl-append
         (hc-append
          (hbl-append (es/unchecked (compile WAIT))
                      (es =))
          compile-wait-pict)
         (hc-append
          (hbl-append (es/unchecked (compile GO))
                      (es =))
          compile-go-pict))]

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

Circuitous is capable of evaluating a given circuit on some
inputs, verifying if two circuits are contextually
equivalent, and verifying if a circuit is constructive for
set of inputs which do not contain @es[⊥]. This solver is
combined with a mechanized version of the compiler presented
in @secref["just:sound:compiler"], which is in the codebase
for this dissertation. Using these, the base cases of many of
the proofs in this section simply invoke the circuit solver
to complete the proof.

The source for this solver may be found at
https://github.com/florence/circuitous/, and the core of the
solver is listed in appendix C.


@section[#:tag "just:sound:instants"]{On Instants}

The proofs in this section only look at a single instant of execution.
This is accomplished by each proof having the assumption that the @es[SEL]
wire is @es[0], thus forcing evaluation to occur in the first instant only.
The calculus will be extended to multiple instants in @secref["sec:calc:future"].

@section{Agda Codebase}

Some proofs I reference are not given in this document. Instead they are given in a separate Agda code base.
which was attempt to prove the correctness of a previous version of the calculus@~cite[florence-2019].
While the calculus has since changed, @es[Can] has not. Therefore I re-use some of the proofs from
that work which relate to @es[Can]. This Agda codebase is located in the repository for this dissertation.


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