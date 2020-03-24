#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          (except-in "../lib/proof-extras.rkt" =)
          "../lib/cite.rkt"
          "../lib/circuit-diagrams.rkt"
          "../lib/misc-figures.rkt"
          scriblib/figure
          redex/pict
          (except-in diagrama nothing) diagrama/circuit pict)

@title[#:style paper-title-style #:tag "background-circuits"]{Circuits}

Pure Esterel compiles to circuits. This section gives the background needed
to understand the circuits Esterel compiles to. Those familiar with
Constructive Synchronous Circuits---particularly @citet[malik-circuit] and
@citet[shiple-constructive-circuit]---may wish to skip to the end of skim this section
for a summary of the exact notation I will be using

@section[#:tag "back:graph"]{Circuits as Graphs}

Circuits can be though of as graphs, where each edge
represents a wire, and each node represents a gate. This
also gives the usual pictorial representation of circuits.
As an example, the left of @figure-ref["circ-overview"] is a
circuit for the XOr of two bits. The right of
@figure-ref["circ-overview"] gives an overview of the
notation I am using, which is fairly standard.

@[figure
  "circ-overview"
  "Circuit Diagram Overview"
  (let ()
    ;; TODO this looks like shit
    (define layer-1-x 6)
    (define layer-2-x 3)

    (define input-1 (tag-location 'input-1 0 0))
    (define input-2 (tag-location 'input-2 0 2))
    (define top-gate
      (after
       (move-down 1) (move-right layer-1-x)
       (and-gate #:out #t
                 #:tag-out 'and-out
                 #:tag-in1 'and-A
                 #:tag-in3 'and-B)))
    (define lower-gate
      (after
       (move-down 5) (move-right layer-1-x)
       (or-gate #:tag-out 'or-out
                #:tag-in1 'or-A
                #:tag-in3 'or-B)))
    (define last-gate
      (after
       (move-down 1) (move-right layer-2-x)
       (and-gate #:tag-in1 'and-in
                 #:tag-in3 'or-in
                 #:tag-out 'result)))
    (define (connect-input input g1 g2 split-point)
      (after
       (move-to-tag input)
       (line-right split-point)
       (split
        (line-to-tag g1)
        (line-to-tag g2 #:h-first #f))))
    (define xor
      (after
       input-1 input-2
       (move-to-tag 'input-1)
       (save top-gate) (save lower-gate)
       (move-to-tag 'and-out) last-gate
       (connect-input 'input-1 'and-A 'or-A 3)
       (connect-input 'input-2 'and-B 'or-B 2)
       (line-between 'and-out 'and-in)
       (line-between 'or-out 'or-in)
       (move-to-tag 'result)
       (line-right 1)))


    (define (lbl p t)
      (vc-append
       p
       (text t)))
    (hc-append
     (lbl xor
          "A 2-bit XOr circuit")
     (vc-append
      (ht-append
       (lbl
        (and-gate #:tag-in3 'x  #:tag-in1 'x #:tag-out 'x)
        "And Gate")
       (lbl
        (or-gate #:tag-in3 'x  #:tag-in1 'x #:tag-out 'x)
        "And Gate")
       (lbl
        (buffer #:tag-in2 'x  #:tag-out 'x)
        "Buffer"))
      (ht-append
       (lbl
        (register #:tag-in2 'x  #:tag-out 'x)
        "Register")
       (lbl
        (after (line-right 1)
               (split
                (after
                 (line-up 1)
                 (line-right 1))
                (after
                 (line-down 1)
                 (line-right 1))))
        "Splitting a wire"))
      (ht-append
       (lbl
        (after (label "1" 'left) (line-right 1))
        "A wire with a constant 1")
       (lbl
        (after (label "0" 'left) (line-right 1))
        "A wire with a constant 0")))))]


Registers save values between cycles in the circuit. The are always initialized to @es[0] in
the first cycle, and then output their input value from the previous cycle afterwards.


@[figure
  "zero-example"
  "An example in which the sub-circuit may be missing wires"
  (hc-append trap-pict nothing)]

A side note on diagrams: Sometime circuit diagrams may refer
to wires in a sub-circuits that are not present. For
example, see @figure-ref["zero-example"], which shows the
compilation rules for two of Esterel's forms. If the second
circuit is substitute in for @es[(compile p)], then the
wires @es[SEL], @es[K1] and @es[K2] will be missing. For
convenience, these missing wires are defined to be @es[0].


@section{Interpreting a circuit}

As an intuition for how to execute a circuit: take each wire an initialize it
to the special value @es[⊥]. Then set each input wire to its initial value.
From here iterate through each gate in the circuit, updating the output of each
gate if the inputs allow it to change. The output of each gate is
given by the truth tables in @figure-ref["extended-truth-tables"],
which have been extended to handle @es[⊥]. These extensions follow the
principle that if a value is enough to determine the output of a
gate one its own (i.e. would ``short circuit'' evaluation),
then that value controls the output when combined with @es[⊥],
otherwise the output is @es[⊥]. This ensures that the output
of gates is monotonic: once its output transitions from @es[⊥]
to @es[0] or @es[1] its output will never change.

@figure["extended-truth-tables"
        @list{Truth tables for each gate, extended with @es[⊥]}
        #:style right-figure-style
        (nested
         @[tabular
           (list
            (list @es[a] @es[and] @es[b]  @es[=] @es[o])
            (list @es[1] @[blank] @es[1] @[blank] @es[1])
            (list @es[1] @[blank] @es[0] @[blank] @es[0])
            (list @es[1] @[blank] @es[⊥] @[blank] @es[⊥])
            (list @es[0] @[blank] @es[1] @[blank] @es[0])
            (list @es[0] @[blank] @es[0] @[blank] @es[0])
            (list @es[0] @[blank] @es[⊥] @[blank] @es[0])
            (list @es[⊥] @[blank] @es[1] @[blank] @es[⊥])
            (list @es[⊥] @[blank] @es[0] @[blank] @es[0])
            (list @es[⊥] @[blank] @es[⊥] @[blank] @es[⊥]))
           #:row-properties '(bottom-border bottom-border bottom-border bottom-border bottom-border bottom-border bottom-border bottom-border bottom-border ())]
         ;; or
         @[tabular
           (list
            (list @es[a] @es[or] @es[b] @es[=] @es[o])
            (list @es[1] @[blank] @es[1] @[blank] @es[1])
            (list @es[1] @[blank] @es[0] @[blank] @es[1])
            (list @es[1] @[blank] @es[⊥] @[blank] @es[1])
            (list @es[0] @[blank] @es[1] @[blank] @es[1])
            (list @es[0] @[blank] @es[0] @[blank] @es[0])
            (list @es[0] @[blank] @es[⊥] @[blank] @es[⊥])
            (list @es[⊥] @[blank] @es[1] @[blank] @es[1])
            (list @es[⊥] @[blank] @es[0] @[blank] @es[⊥])
            (list @es[⊥] @[blank] @es[⊥] @[blank] @es[⊥]))
           #:row-properties '(bottom-border bottom-border bottom-border bottom-border bottom-border bottom-border bottom-border bottom-border bottom-border ())]
         ;; not
         @[tabular
           (list
            (list @es[¬] @es[a] @es[=] @es[o])
            (list @[blank] @es[1] @[blank] @es[0])
            (list @[blank] @es[0] @[blank] @es[1])
            (list @[blank] @es[⊥] @[blank] @es[⊥]))
           #:row-properties '(bottom-border bottom-border bottom-border ())])]
TODO Scott domains?

@section{Cycles & Constructivity}

The circuits generated by the Esterel compiler may contain
cycles. The semantics of cyclic circuits I present here is
based on @citet[malik-circuit],
@citet[shiple-constructive-circuit], 
@citet[constructive-boolean-circuits], and
@citet[esterel02].

A circuit with a cycle may or may not be electrically
stable. Wires which do not stabilize are given the
wires with the value @es[⊥]. Initially, all wires are in this state,
as we do not yet know their value.

A circuit which does not stabilize is called
@index['("non-constructive" "constructive")]{
 non-constructive}. Like constructivity in Esterel, this term
is an allusion to Constructive Logic, a connection which
@~cite[constructive-boolean-circuits] formalize. But to a
first approximation: Using three values for Booleans @es[1],
@es[0], and @es[⊥] is one way of formalizing a logic without
the law of the excluded middle. That is, in circuits
@es[(or X (not X))] may not always produce @es[1], but can
also produce @es[⊥].
  
Any circuit, even ones with a cycle, and be computed in finite time.
On the electrical side of things, this is because, for constructive circuits,
for any delay time in the computation of a gate there exists some clock time
for which the circuit will always stabilize. On the logic side, the
functions which define the gates are monotonic: once a value transitions
from @es[⊥] to @es[0] or @es[1] it can never change. This means that
there is a fixed-point when evaluating that circuit, and it should
take no more than @es[n] iterations to find that fixed-point (where
@es[n] is the size of the circuit).


@section[#:tag "back:circ:form"]{Circuits, more formally}

@[figure "circuit-grammar" "A Grammar for Circuits"  circuit-lang]

Now, on to the formal definition of a circuit. A circuit @es[c] can be defined as a triple
@es[(circ EQ I O)] were @es[I] is a set of names of input wires, @es[O] is a set of names
of output wires, and @es[EQ] is a set of equations @es[(w = wire-value)], which
defines the internal wire named @es[w] by the expression @es[wire-value], which is drawn
from the grammar given in @figure-ref["circuit-grammar"]. Wire names are assumed to be unique.

Circuit evaluation takes place on a circuit state which is,
in essence and environment for the circuit. It takes the
form of a mapping from the wire names of the circuit to the
current state of the circuit. I will denote a circuit state
for a circuit @es[circuit] as @es[cs]. There is a special
circuit state @es[cs_0] for every circuit in which every
internal wire @es[w] which is not equal to a constant @es[0]
or @es[1] is assigned the initial value @es[⊥]. Any wires in
the set @es[I] or @es[O] which do not have a corresponding
internal wire are given the value @es[0]. For example,
the circuit
@centered[@es[(= circuit (circ ((internal = input) {input} {output1 internal})))]]
would have the initial state
@centered[@es[(= cs_0 {{internal ↦ ⊥} {input ↦ 0} {output1 ↦ ⊥}})]].

The circuit can then be evaluated by the reduction relation @es[⟶^c],
which is define in @figure-ref["c-step"].

@figure["c-step"
        "Reduction relation for circuits"
        @with-paper-rewriters[[render-reduction-relation ⟶^c]]]


@figure["e-step"
        "Reduction relation for wire expressions"
        @with-paper-rewriters[[render-judgment-form eval^boolean]]]



symbolic interpretation.
Define EvalC.

@subsection{Contextual Equivalence}
@newline


@definition[#:notation @es[(≃^circuit c_1 c_2)]]{
 @es[(≃^circuit c_1 c_2)] if and only if,
 for all assignments to the inputs, and all
 possible output sets @es[O],
 @es[(= (eval^circuit O c_1) (eval^circuit O c_2))]
 and @es[c_1] and @es[c_2] have the same constructivity.
}

