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
   
]


This appendix is meant to serve as an explaination of the
core of the circuit solving library Circuitous. Specifically
it describes the interpreter implemenation at commit
@tt[commit] of https://github.com/florence/circuitous/,
which is the version used while building this document. Note
that the explaination of this section assumes more
familiarity with @citet[malik-circuit], @citet[constructive-boolean-circuits], and
Racket@~cite[plt-tr1], Rosette@~cite[rosette] than the rest of this disseratation.

@section{Internal representation of circuits}

Interally, a circuit is represented as an association list,
mapping variable names to boolean expressions, also
represented as a list. However this definition is a little
missleading, as there are actually two possible ways the
circuit library does this. First, there is a representation
that direclty implements the representation in
@citet[malik-circuit], where variable names are either pairs
of either the symbol @es['+] or @es['-], and an arbitrary
symbol. Every wire in the circuit has a @es[+] and a @es[-]
form, corresponding to Malik's @tt{.1} and @tt{.0} forms, respectively.
Correspondingly, values for each of these variables take on the form
of @racket[#t] or @racket[#f], matching @es[1] and @es[0] in Malik's representation.
I will refer to this as the @tt{pos-neg} representation. Circuits are also
represented by using the values @es[#t], @es[#f], and @es[⊥] directly. In this
case variables are just symbols, and the interpretations of @es[and] and @es[or]
are lifted directly to operate on @es[⊥]. I will refer to this as the @tt{three-valued}
representation.

@[figure
  "sem-sig"
  "sem-sig.rkt"
  [render-file private/sem-sig]]

To handle this the implemenation of the interpreter is
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
@es[cs], @racket[value] refers to whichever set of values that represenation
chooses, and @racket[circuit] refers to whichever for of association lists the
representation uses.

The functions behave as follows: @racket[symbolic-variable]
creates a rosette symbolic variable for a variable in the
circuit; @racket[initial-value] gives the value that all
variabes in the initial @racket[state] should be
(@racket[#f] for @tt{pos-neg}, and @racket[⊥] for @tt{
 three-valued}); @racket[f-or], @racket[f-and]
@racket[f-not], and @racket[f-implies] are used by the
interpereter to lift expression in the circuit into racket
functions that operate over the current state, so that each
variable is associated with a single function that computes
it's current value; @racket[constraints] generates global
contraints for the representation (such as the @racket[+]
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
itterations that may be needed to evaluate a circuit in a
single instant; @racket[outputs=?] is an equality predicate over
states; @racket[constructive-constraints] computes an expression
which will evaluate to true if and only if the circuit is constructive.

@section{The circuit interpreter}

The actual implementations of the representations are recursively linked
with the interperter, therefore I will describe the interpreter interface
and implementation before describing the representations' implementations. The signature
for the interpreter unit is given in @figure-ref["interp-sig"].

@[figure "interp-sig" "interp-sig.rkt" [render-file private/interp-sig]]

The primary function of interest is @racket[verify-same],
which is the core implementation of the solver. It takes in
two circuits, a list of which wires in them correspond to
the inputs and outputs of registers, and contraints the
caller wishes to impose, and a list of outputs to observe.
If the list of outputs is @racket[#f], all wires are
concidered outputs. If the registers are set to @racket[#f],
no registers are taken an a slighlty different code path is
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


@[interp-def-fig verify-same/multi]


The first function, @racket[symbolic-inputs], generates a
symbolic variable for every input the in the circuit, giving
an association list from the variables to their symbolic
representations. This will form the core of the construction of the initial @racket[state]. The implementation is
in @figure-ref["symbolic-inputs"] which does not bare much further discussion.

@[interp-def-fig symbolic-inputs].

The next function, @racket[build-state] builds a state from the circuit and it's inputs,
which in the symbolic case will have been generated by @racket[symbolic-inputs]. Its
definition is in @figure-ref["build-state"].

@[interp-def-fig build-state]

@[interp-def-fig result=?/multi]
@[interp-def-fig result=?]

@section{Implementing the representations}
