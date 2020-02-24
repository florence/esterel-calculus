#lang scribble/book

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/cite.rkt"
          "lib/def-extract.rkt"
          (only-in
           "lib/circuit-diagrams.rkt"
           emit-pict nothing)
          "lib/proof-extras.rkt"
          (only-in scribble/manual racket)
          scriblib/figure
          racket/runtime-path
          (only-in racket/port with-output-to-string)
          (only-in racket/system system)
          syntax/parse 
          (for-syntax syntax/parse racket/syntax racket/base)
          racket/format
          scriblib/figure
          syntax/parse/define)


@title[#:style paper-title-style #:tag "ap:solver"]{The circuit sovler, Circuitous}

@[begin
 (define-runtime-module-path circuitous circuitous)
 (define path (resolved-module-path-name circuitous))
 (define commit
   (parameterize ([current-directory (build-path path "..")])
     (substring
      (with-output-to-string
        (lambda () (system "git rev-parse HEAD")))
      0 7)))
 (define-simple-macro (interp-def-fig name)
   @[figure (symbol->string 'name)
     [index*
      (list (symbol->string 'name))
      (list @racket[name])
      @racket[name]]
     [render-def private/interp-unit name]])
 (define-simple-macro (tv-def-fig name)
   @[figure (string-append "tv:" (symbol->string 'name))
     [index*
      (list (symbol->string 'name) "three-valued representation")
      (list @racket[name] "three-valued representation")
      @list{@racket[name] in the @tt{three-valued} representation}]
     [render-def private/three-valued-unit name]])
 (define-simple-macro (pn-def-fig name)
   @[figure (string-append "pn:" (symbol->string 'name))
     [index*
      (list (symbol->string 'name) "pos-neg representation")
      (list @racket[name] "pos-neg representation")
      @list{@racket[name] in the @tt{pos-neg} representation}]
     [render-def private/pos-neg-unit name]])
   
]


This appendix is meant to serve as an explanation of the
core of the circuit solving library Circuitous. Specifically
it describes the interpreter implementation at commit
@tt[commit] of https://github.com/florence/circuitous/,
which is the version used while building this document. Note
that the explanation of this section assumes more
familiarity with @citet[malik-circuit], @citet[constructive-boolean-circuits], and
Racket@~cite[plt-tr1], Rosette@~cite[rosette] than the rest of this dissertation.

The purpose of this appendix is help make this work more
reproducible and to help increase the readers confidence
that the circuit solver is actually correct. As such it
focus on the small (approximately 600 lines) Rosette kernel which directly interprets
and solves circuits and its tests. The library has contains
more: a Racket front-end which compiles to the Rosette model,
and helper procedure for manipulating circuits. However
those will not be described here.

@section{Internal representation of circuits}

Internally, a circuit is represented as an association list,
mapping variable names to Boolean expressions, also
represented as a list. However this definition is a little
misleading, as there are actually two possible ways the
circuit library does this. First, there is a representation
that directly implements the representation in
@citet[malik-circuit], where variable names are either pairs
of either the symbol @es['+] or @es['-], and an arbitrary
symbol. Every wire in the circuit has a @es[+] and a @es[-]
form, corresponding to Malik's @tt{.1} and @tt{.0} forms, respectively.
I will refer to these as the positive and negative variants of the wire.
Correspondingly, values for each of these variables take on the form
of @racket[#t] or @racket[#f], matching @es[1] and @es[0] in Malik's formulation.
I will refer to this as the @tt{pos-neg} representation. Circuits are also
represented by using the values @es[#t], @es[#f], and @es[⊥] directly. In this
case variables are just symbols, and the interpretations of @es[and] and @es[or]
are lifted to operate on @es[⊥]. I will refer to this as the @tt{three-valued}
representation.

@[figure
  "sem-sig"
  "sem-sig.rkt"
  [render-file private/sem-sig]]

To handle this the implementation of the interpreter is
parameterized by the two different representations. This is
accomplished using Racket's @racket[unit]
system@~cite[unit-cite], which is a first-class module
system that supports recursive linking. It is akin to ML's
Functors, in that modules are parameterized by other
modules. As such, a unit which implements one of these representations
follows the following signature in @figure-ref["sem-sig"]. In the
comments which describe the contracts on what the modules provide,
@racket[symbolic-boolean] refers to a Rosette symbolic value which
evaluates to a boolean, @es[state] refers to the library's representation of
@es[cs], @racket[value] refers to whichever set of values that representation
chooses, and @racket[circuit] refers to whichever for of association lists the
representation uses.

The functions behave as follows: @racket[symbolic-variable]
creates a rosette symbolic variable for a variable in the
circuit; @racket[initial-value] gives the value that all
variables in the initial @racket[state] should be
(@racket[#f] for @tt{pos-neg}, and @racket[⊥] for @tt{
 three-valued}); @racket[f-or], @racket[f-and]
@racket[f-not], and @racket[f-implies] are used by the
interpreter to lift expression in the circuit into racket
functions that operate over the current state, so that each
variable is associated with a single function that computes
it's current value; @racket[constraints] generates global
constraints for the representation (such as the @racket[+]
and @racket[-] variables being mutually exclusive in the
@tt{pos-neg} representation); @racket[contructive?] gives a
symbolic expression which will be true if and only if the
circuit's state is constructive (that is does not contain
the representation of @es[⊥]); @racket[initialize-to-false]
and @racket[initialize-to-true] create a state for a
(sub)circuit where all values are the representations of the
@es[0] or @es[1], respectively;
@racket[get-maximal-statespace] computes the totally number
of instants that may be needed to explore all possible
register states given the number of registers in the circuit, a la @citet[constructive-boolean-circuits];
@racket[interp-bound] computes the maximum number of
iterations that may be needed to evaluate a circuit in a
single instant; @racket[outputs=?] is an equality predicate over
states; @racket[constructive-constraints] computes an expression
which will evaluate to true if and only if the circuit is constructive.

@section{The circuit solver}

The actual implementations of the representations are recursively linked
with the interpreter, therefore I will describe the interpreter interface
and implementation before describing the representations' implementations. The signature
for the interpreter unit is given in @figure-ref["interp-sig"].

@[figure "interp-sig" "interp-sig.rkt" [render-file private/interp-sig]]

The primary function of interest is @racket[verify-same],
which is the core implementation of the solver. It takes in
two circuits, a list of which wires in them correspond to
the inputs and outputs of registers, and constraints the
caller wishes to impose, and a list of outputs to observe.
If the list of outputs is @racket[#f], all wires are
considered outputs. If the registers are set to @racket[#f],
no registers are taken an a slightly different code path is
taken that bypasses the multi-instant solver and jumps
straight to the single instant solver. This is only used for
testing and debugging, therefore I will not describe that
code path. This function assumes the circuits have been consistently renamed
such that any two wires in the two circuits that have the same name are part of that
circuits interface, and therefore may be compared when comparing the circuit's for equality.
This renaming is handled at a higher level in the library which is not discussed here.
The full implementation of @racket[verify-same] is given in
@figure-ref["verify-same"]. The implementation logs debug
information then decides if it should take the debug code path
or not. As we are ignoring the debug path, the next function of
interest is @racket[verify-same/multi].
@[interp-def-fig verify-same]

The function @racket[verify-same/multi], shown in
@figure-ref["verify-same/multi"], constructs all the inputs
the solver needs, then gives those to the solver via the
@racket[do-verify] macro. The inputs to @racket[do-verify]
are as follows: @racket[#:=?] is the equality procedure used
to compare the outputs for equality. In this case it is
@racket[result=?/multi] which loops over the result from
each input and uses the @racket[outputs=?] and
@racket[constructive?] from the representation unit to make
sure each instant behaved the same (see
@figure-ref["result=?/multi"] and @figure-ref["result=?"]).
The @racket[#:expr1] and @racket[#:expr2] arguments are the two symbolic
expressions to execute. The @racket[#:given-constraints] arguments
are any constraints given to the solver by the caller (i.e. that @es[GO] implies
@es[(not SEL)]). The @racket[#:gened-constraints] are  constraints necessitated
by the representation (as specified by @racket[constraints]). And finally
@racket[#:outputs] specifies which output wires to observe.

@[interp-def-fig verify-same/multi]

The two expressions are generated by the function @racket[eval/multi*],
which builds the racket representation of a circuit and evaluates it.
The first argument is a list of the inputs for each instant, which in this
case is a list who's length is long enough to explore all register states (computed
by @racket[get-maximal-statespace]), and who's values are all symbolic (generated by
@racket[symbolic-inputs]). The two sets of constraints are build for every instant
by either translating the given constraints into racket function via @racket[build-expression]
and evaluating it on all symbolic instants, or by calling the representations
@racket[constraints] function on the output of each instant of execution (which will exclude any result
states that violate the constraints).

Before describing the symbolic interpreter, I will first
discuss describe the solver. The solver macro
@racket[do-verify], found in @figure-ref["do-verify"], just
surrounds the entire computation in a
@racket[with-asserts*], which captures any rosette asserts
and resets the assertion store after the solver completes.
The real implementation is in @racket[verify/f], found in
@figure-ref["verify/f"].

@[interp-def-fig do-verify]

@[begin
 (define racket-bool-note
   @note{The
  equality check for @racket[#t] is needed because racket
  treats any non-@racket[#f] value as @racket[#t]. If any of
  these procedures returns a boolean value, such as
  @racket['⊥] in the case of the @tt{three-valued}
  representation, we want to treat that as not true.})
 (define unsat-note @note{
  SMT solvers, and therefore Rosette, represent verification
  problems by making sure that the it's negation, when expressed
  as an existential, 
  does not have a satisfying solution. That is the verification of
  @tt{∀ x, P(x)} is proven by showing that @tt{∃ x, ¬P(x)} is
  unsatisfiable.})]

The function @racket[verify/f] begins with a large chunk of
debug logging statements. It then constructs the symbolic
expression @racket[eq], which is true if and only if the
equality predicate @racket[=?] returns @racket[#t].@racket-bool-note
This symbolic expression is then @racket[verify]ed by Rosette
under the assumptions that all of our constraints return true.
If a @racket[sat]isfying result is returned it means the verification failed.@unsat-note
In this case more debugging information is logged, and a result is returned
containing the satisfying core, and the result of evaluating the two symbolic
expressions under that core. Otherwise the @racket[unsat] core is returned, representing
the success of the verification.

@[interp-def-fig verify/f]

Before moving on to the interpreter, the last three solver
functions to explain is @racket[symbolic-inputs], @racket[result=?/multi],
and @racket[result=?]. The first, in @figure-ref["symbolic-inputs"],
generates a symbolic variable for every input the in the
circuit, giving an association list from the variables to
their symbolic representations. This will form the core of
the construction of the initial @racket[state]. The
implementation is in @figure-ref["symbolic-inputs"] which
does not bare much further discussion.

@[interp-def-fig symbolic-inputs]

The two result functions use the @racket[outputs=?] and
@racket[constructive?] functions from the representation to
check if two states, or list of states in the case of
@racket[result=?/multi], are the same. The
@racket[result=?/multi] function
(@figure-ref["result=?/multi"]) demands that the two lists
be the same length, and that every state is
@racket[result=?]. The @racket[result=?]
(@figure-ref["result=?"]) demands that two states have the
same outputs (as determined by @racket[outputs=?] and
@racket[outputs]) and have the same constructivity, as
determined by @racket[constructive?].

@[interp-def-fig result=?/multi]
@[interp-def-fig result=?]

The last part of the solver @racket[totally-constructive?]
(@figure-ref["totally-constructive?"]). This function is a
little bit of a hack, as it just checks if the given
circuit is equal to the empty circuit while checking no
inputs, which devolves to checking that both circuits have
the same constructivity when their inputs are constructive.
Therefore the constraints for the call to @racket[verify-same/multi]
contain the constraints which force all free variables in the circuit
(the inputs) to be constructive.

@[interp-def-fig totally-constructive?]

@section{The circuit interpreter}

The top level function of the circuit interpreter is @racket[eval/multi*]
(@figure-ref["eval/multi*"]), which is responsible for
constructing the interpreters representation of the circuit.
It's first argument is the list of inputs for each instant, it's second is the
circuit equations, and the last are the input/output pairs of wire names for the registers.
@note{Not that the circuit interpreter works on both concrete and symbolic inputs. This is the joy of
using Rosette.} The @racket[eval/multi*] function delegates to the @racket[eval/multi] function,
which operates on the internal circuit representation. It's arguments are
the starting state for each instant, which is the inputs appended to
an initial wire state computed by @racket[build-state];
the internal circuit representation list which maps each wire name to a function of the
current state to a value) is constructed by @racket[build-formala];
the list of wires which are inputs to registers, and a substate that corresponds
to the initial state of the outputs of the registers, which must be in the
same order as the inputs. This initial state has all registers set to false.

@[interp-def-fig eval/multi*]

The @racket[eval/multi] function (@figure-ref["eval/multi"])
uses the single instant evaluator @racket[eval] to evaluate
each instant, threading the inputs of each register to the
outputs in subsequent instants. It will short-circuit if any
instant is not constructive, as the future behavior of such
a circuit is unspecified (that is, non-constructive is an
error state). This function is a recursive loop which keeps
track of the current register states @racket[out-registers],
a backwards list of the outputs of each instant
@racket[seen], and the remaining list of input states to
execute @racket[states]. If the states are empty is return
the @racket[seen] states, which will be reversed. Otherwise
it adds the current register state to the next input state
and @racket[eval]uates that instant. If the result is not
constructive the result is added to the seen list and the
loop is aborted. Otherwise the input values of the registers
are copied to the outputs, and the loop restarts.

@[interp-def-fig eval/multi]

The @racket[eval] (@figure-ref["eval"]) fully evaluates a single instant.
Following the procedure laid out by @citet[malik-circuit], it uses the
@racket[step] function to evaluate all the gates it can. This process must settle
in @racket[interp-bound] steps, as the values of each gate are monotonic.
Note that this loop does not exit early if a fixed pointed is reached. While
this is an optimization in the concrete case, it is actually a pessimization when
solving. This is because, as the state is symbolic, the check that a fixed point is
reached adds extra, recursive, formula to the solver. 


@[interp-def-fig eval]

Next, the @racket[step] function (@figure-ref["step"]) takes
in the current state and list of formula and evaluates each
formula exactly once on the current state to generate a new
state. It does this by iterating over the current state and,
for each value, if it is defined by a wire (rather that
being an input), the function for that wire is evaluated on
the current state. Note that, again, wires which are don't
represent @racket['⊥] don't need to be evaluated, but this
would be a pessimization when solving as it added more
formula.@note{Note that evaluating the wire again also will
 add more formula, but these formula will be added in either
 case as rosette must explore both branches of the
 conditional.}

@[interp-def-fig step]

The next interesting function in the interpreter is
@racket[build-state] (@figure-ref["build-state"]). It builds
a state from the circuit and it's inputs, which in the
symbolic case will have been generated by
@racket[symbolic-inputs]. It simply sets all wires to their initial
value, and adds in the inputs.@note{The inputs argument is unused in the
multi-instant case, as @racket[eval/multi] handles that itself.}

@[interp-def-fig build-state]

The final interesting functions in the interpreter are
@racket[build-formula] (@figure-ref["build-formula"])
and @racket[build-expression] (@figure-ref["build-expression"]),
which convert a the circuit AST into Racket functions.
The recursively walk the AST and invoke the @racket[f-and],
@racket[f-or], and @racket[f-not] functions into ``compile''
the expressions. Constants and variables are handled
manually, rather than by the representations.

@[interp-def-fig build-formula]
@[interp-def-fig build-expression]


@section{Implementing the representations}

Finally on too the representation. First up is the easier of
the two to understand, the @tt{three-valued} representation.

@subsection{The three-value representation}

As the interface to the representations have already been
explained, this explanation will be brief. The
@racket[interp-bound] (@figure-ref["tv:interp-bound"]) is
the number of wires in the circuit, as in each cycle either
a fixed point has been reached or one gate's value will
change. The @racket[initial-value]
(@figure-ref["tv:initial-value"]) is @racket['⊥]. The number
of instants needed for @tt{x} registers
(@figure-ref["tv:get-maximal-statespace"]) is @tt{
 2}@superscript{@tt{x}}, as each register can only take on
the values @racket[#t] or @racket[#f].@note{The value
 @racket['⊥] is forbidden, because that would mean the
 previous instant was non-constructive.}


@[tv-def-fig interp-bound]
@[tv-def-fig initial-value]
@[tv-def-fig get-maximal-statespace]

The ``compiling'' functions @racket[f-and]
(@figure-ref["tv:f-and"]), @racket[f-or]
(@figure-ref["tv:f-or"]), and @racket[f-not]
(@figure-ref["tv:f-not"]) directly implement the
truth-tables found in @secref["back:graph"]. They contain
extra error cases, which should never be triggerable.

@[tv-def-fig f-and]
@[tv-def-fig f-or]
@[tv-def-fig f-not]

The representation gets more interesting with @racket[symbolic-boolean]
(@figure-ref["tv:symbolic-boolean"]). Rosette implements a union
of three values like @racket[#t], @racket[#f], and @racket['⊥]
as a symbolic computation that returns one of these values.
Therefore two symbolic Booleans---@racket[pos] and @racket[neg]---are created@note{In order to create
them dynamically I use Rosette's reflective API, and ensure the
variables are unique using a small amount of state in @racket[next-unique!].}.
If @racket[pos] is @racket[#t], then the overall symbolic Boolean is @racket[#t].
Otherwise if @racket[neg] is @racket[#t], the overall symbolic Boolean is @racket[#f].
If both are @racket[#f], the overall symbolic Boolean is @racket['⊥]. The case where
both are @racket[#t] is excluded by assertion. Not that this means that, at the lowest
level, the @tt{three-valued} and @tt{pos-neg} representation actually use the same representation
of values. The only difference is in the representation of wires: In the @tt{three-valued}
case the two Booleans are bundled into one equation, whereas in the @tt{pos-neg} representation
they will have separate equations. 

@[tv-def-fig symbolic-boolean]

This representation has no external @racket[constraints]
(@figure-ref["tv:constraints"]), and is
@racket[constructive?] (@figure-ref["tv:constructive?"] and
@figure-ref["tv:constructive-constraints"]) if all wires are
@racket[#t] or @racket[#f].

@[tv-def-fig constraints]
@[tv-def-fig constructive?]
@[tv-def-fig constructive-constraints]

Two outputs are @racket[outputs=?]
(@figure-ref["tv:outputs=?"]) when either all of the
specified output wires are the same, or---if no output wire
set is given---every wire which is in both circuits has the
same value. Note when an output set is given, if a circuit
does not have that wire we treat it's value as @racket[#f].

@[tv-def-fig outputs=?]

@subsection{The pos-neg representation}

The @tt{pos-neg} representation is a little more subtle. As
there are two formula for each wire, but the two formula are
mutually exclusive, the @racket[interp-bound]
(@figure-ref["pn:interp-bound"]) is half of the size of
overall number of formula. The @racket[get-maximal-statespace]
(@figure-ref["pn:get-maximal-statespace"]) function also
halves it's inputs to account for the exclusivity of the
positive an negative representations, giving gives @tt{
 2}@superscript{@tt{x/2}}.

@[pn-def-fig interp-bound]
@[pn-def-fig get-maximal-statespace]

Constructivity
checking(@figure-ref["pn:constructive?"] and
@figure-ref["pn:constructive-constraints"]) also changes. When
the positive variant of each wire is found the an expression
is added insisting that either the positive or negative
variant be true. To avoid adding redundant expressions, the negative
variant is skipped.


@[pn-def-fig constructive?]
@[pn-def-fig constructive-constraints]

The @racket[initial-value] is
@racket[#f] (@figure-ref["pn:initial-value"]) as setting
both parts of the representation of the wire to @racket[#f]
sets the overall representation to @racket[#f]. Symbolic
Booleans just represented by a single symbolic variable
(@figure-ref["pn:symbolic-boolean"]).

@[pn-def-fig initial-value]
@[pn-def-fig symbolic-boolean]

However this leads to a non-trival implementation of the global
@racket[constraints] (@figure-ref["pn:constraints"]). It ensures
that for every wire with a positive and negative part, only one
of them may be true in the given state. Therefore for each
positive variant we ensure that at most one
of the positive and negative variants are true.

@[pn-def-fig constraints]


The equality predicate @racket[outputs=?]
(@figure-ref["pn:outputs=?"]) has a more subtle accounting
of the positive and negative variants. Like in the @tt{
 three-valued} case we treat a missing wire as false. However
this means that we treat the positive and negative variants
asymmetrically: if we expect the overall wire to be false we
must treat the negative variant as true. Therefore
@racket[outputs=?] checks which variant it is currently
handling and adjusts accordingly. This is only needed in the
case where outputs are given, as in the other case we only
check wires that we know are in both circuits.

@[pn-def-fig outputs=?]

@section{Trusting the solver}

Of course explaining the code should not be enough to
convince anyone that the code is enough. Thus I offer the
following evidence: test cases and code coverage. The test
cases consist of approximate 116 manual test cases targeting
specific behavior. In addition there are 1000 random tests
which run against compare behavior of the implementation to
a redex model of the circuit semantics presented in
@secref["back:circ:form"].

In addition code coverage of the implementation shows 96%
code coverage, where the 4% correspond to error cases that
should be unreachable, or are in areas of the codebase used
for circuit manipulation and not used in my proofs.