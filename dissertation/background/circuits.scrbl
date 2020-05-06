#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          (except-in "../lib/proof-extras.rkt" =)
          "../lib/cite.rkt"
          "../lib/circuit-diagrams.rkt"
          "../lib/misc-figures.rkt"
          "../lib/rule-figures.rkt"
          "../lib/jf-figures.rkt"
          "../notations.scrbl"
          scriblib/figure
          redex/pict
          racket/format
          (except-in diagrama nothing) diagrama/circuit pict)

@title[#:style paper-title-style #:tag "background-circuits"]{Circuits}

This section refreshes background needed
to understand the potentially cyclic circuits that Esterel compiles to. It summaries
@cite/title[malik-circuit] and
@cite/title[shiple-constructive-circuit], and Chapter 10 of @cite/title[esterel02].

@section[#:tag "back:graph"]{Circuits as Graphs}

Circuits can be thought of as graphs, where each edge
represents a wire, and each node represents a gate. This
also gives the usual pictorial representation of circuits.
As an example, the left of @figure-ref["circ-overview"] is a
circuit for the XOr of two bits. This is implemented
by taking the nand'ing and or'ing both of the two inputs,
and and'ing the outputs of those two gates. The right of
@figure-ref["circ-overview"] gives an overview of the
notation I am using, which is fairly standard. Buffers here do
not impose a delay, but rather just specify the direction voltage propagates through
the circuit. Registers save values between cycles in the circuit. The are always initialized
to @es[0] in the first cycle, and then output their input value from the previous cycle afterwards.
A small circle on the input or output of a gate represents negating that wire.


@[begin
 (define (make-xor
          #:input1 [input1 #f]
          #:input2 [input2 #f]
          #:nand [nand #f]
          #:or [theor #f]
          #:and [theand #f])
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
      (line-right 1)
      (move-to-tag 'input-1)
      (if input1
          (img [with-paper-rewriters input1] 'lb)
          (img (blank)))
      (move-to-tag 'input-2)
      (if input2
          (img [with-paper-rewriters input2] 'lb)
          (img (blank)))
      (move-to-tag 'and-out)
      (if nand
          (img [with-paper-rewriters nand] 'cb)
          (img (blank)))
      
      (move-to-tag 'or-out)
      (if theor
          (img [with-paper-rewriters theor] 'lc)
          (img (blank)))
      (move-to-tag 'result)
      (if theand
          (img [with-paper-rewriters theand] 'cb)
          (img (blank)))
      ))

   xor)]

@[figure
  "circ-overview"
  "Circuit Diagram Overview"
  (let ()



    (define (lbl p t)
      (vc-append
       p
       (text t)))
    (hc-append
     (lbl (make-xor)
          "A 2-bit XOr circuit")
     (vc-append
      (ht-append
       (lbl
        (and-gate #:tag-in3 'x  #:tag-in1 'x #:tag-out 'x)
        "And Gate")
       
       (lbl
        (or-gate #:tag-in3 'x  #:tag-in1 'x #:tag-out 'x)
        "Or Gate")
       (lbl
        (buffer #:tag-in2 'x  #:tag-out 'x)
        "Buffer"))
      (ht-append
       (lbl
        (and-gate #:tag-in3 'x  #:tag-in1 'x #:tag-out 'x #:out 'yes)
        "Negated Gate")
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
      (ht-append 5
       (lbl
        (after (label "1" 'left) (line-right 1))
        "A wire with a constant 1")
       (lbl
        (after (label "0" 'left) (line-right 1))
        "A wire with a constant 0")))))]



@[figure
  "zero-example"
  "An example in which the sub-circuit may be missing wires"
  (hc-append trap-pict nothing)]

A side note on diagrams: Sometime circuit diagrams may refer
to wires in a sub-circuits that are not present. For
example, see @figure-ref["zero-example"], which shows the
compilation rules for two of Esterel's forms. The first circuit
has five input wires: @(with-paper-rewriters (render-op "E_i")), @es[SEL], @es[RES], @es[SUSP],
and @es[KILL]. It has two named output wires, @es[SEL] and @(with-paper-rewriters (render-op "E_o")),
and some number of output wires labeled @es[K0] through @es[Kn].
It has a subcircuit, which for now we can think of
as being named @es[(compile p-pure)]. This subcircuit has the same interface
as the overall circuit. All input wires are passed to @es[(compile p-pure)] unchanged,
except for @es[KILL]. The @es[KILL] for @es[(compile p-pure)] is given as the Or
of the @es[KILL] of the outer circuit, and the @es[K2] output from @es[(compile p-pure)].
The outputs of the overall circuit shift @es[Kn] to @es[Kn-1], except for @es[K1]
which is just the @es[K1] of @es[(compile p-pure)], and @es[K0] which is the Or
of the @es[K0] from @es[(compile p-pure)] and the @es[K2] of @es[(compile p-pure)].

If we take @es[(compile p-pure)] to be the second circuit in
@figure-ref["zero-example"], then we have missing
wires, as the only input to this circuit is @es[GO], and the
only output is @es[K0]. In this case we may just ignore the
inputs to the inner circuit which are not used. In addition
we take the outputs which the outer circuit expects but that
the input does not define as begin a constant @es[0].
Therefore when the second circuit is inserted into the
first, we get that every output of the outer circuit except
for @es[K1] is a constant @es[0].@note{Using this rule for
 composition we can in fact simplify the combined circuit
 back to the second circuit.}

@section{Interpreting a circuit}

As an intuition for how to execute a circuit: initialize
internal and output wire to the special value @es[⊥] and
each input wire to the input value given by the environment.
This special value @es[⊥] represents that we do not yet know the value
on that wire.
From here iterate through each gate in the circuit, updating
the output of each gate if the inputs allow it to change,
using the truth tables extended with @es[⊥] in
@figure-ref["extended-truth-tables"]. Continue this until a
fixed-point is reached.

The extended truth tables follow the
principle that if a value is enough to determine the output of a
gate one its own (i.e. would ``short circuit'' evaluation),
then that value controls the output when combined with @es[⊥],
otherwise the output is @es[⊥]. This ensures that the output
of gates is monotonic: once its output transitions from @es[⊥]
to @es[0] or @es[1] its output will never change.

@figure["extended-truth-tables"
        @list{Truth tables for each gate, extended with @es[⊥]}
        #:style right-figure-style
        (centered
         @[tabular
           #:row-properties '(top)
           (list
            (list
             (blank 200)
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
             (blank 30)
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
             (blank 30)
             ;; not
             @[tabular
               (list
                (list @es[¬] @es[a] @es[=] @es[o])
                (list @[blank] @es[1] @[blank] @es[0])
                (list @[blank] @es[0] @[blank] @es[1])
                (list @[blank] @es[⊥] @[blank] @es[⊥]))
               #:row-properties '(bottom-border bottom-border bottom-border ())]
             (blank 30)))])]

Once a fixed point has been reached, the input values
will have propagated through the entire circuit, with each gate
settling on its final value. From here the values of
each output wire will we be on those wires.

As and example of this, let us explore the evaluation of the XOr circuit, when run on the
values @es[1] and @es[1]. The initial state looks like:
@[centered
  (make-xor
   #:input1 @es[1]
   #:input2 @es[1]
   #:nand @es[⊥]
   #:or @es[⊥]
   #:and @es[⊥])]
From here we can either evaluate the Nand or the Or gate. If we evaluate the Nand gate
we get:
@[centered
  (make-xor
   #:input1 @es[1]
   #:input2 @es[1]
   #:nand @es[0]
   #:or @es[⊥]
   #:and @es[⊥])]
Next we can evaluate either the Or or the And gate, as @es[0] short
circuits And. If we evaluate the And gate we get:
@[centered
  (make-xor
   #:input1 @es[1]
   #:input2 @es[1]
   #:nand @es[0]
   #:or @es[⊥]
   #:and @es[0])]
Finally we can evaluate the Or gate:
@[centered
  (make-xor
   #:input1 @es[1]
   #:input2 @es[0]
   #:nand @es[0]
   #:or @es[1]
   #:and @es[0])]
From here evaluating any gate gives the same result, therefore
a fixed-point has been reached and the final result is @es[0].
This, however, may make you wonder: Why do a fixed point? Is it
not enough to evaluate the gates in topological order? The answer
to this is that, in general, circuits may contain cycles.

@section{Cycles & Constructivity}

The circuits generated by the Esterel compiler may contain
cycles. The semantics of cyclic circuits I present here is
based on @citet[malik-circuit],
@citet[shiple-constructive-circuit], 
@citet[constructive-boolean-circuits], and
@citet[esterel02].

A circuit with a cycle may or may not be electrically
stable. Wires which do not stabilize will have the value
@es[⊥] when a fixed-point is reached. Initially, all wires
are in this state, as we do not yet know their value.

A circuit which does not stabilize is called
@index['("non-constructive" "constructive")]{
 non-constructive}. Like constructivity in Esterel, this term
is an allusion to Constructive Logic, a connection which
@~cite[constructive-boolean-circuits] formalizes. But to a
first approximation: using three values for Booleans @es[1],
@es[0], and @es[⊥] is one way of formalizing a logic without
the law of the excluded middle. That is, the circuit
@es[(or X (not X))] may not always produce @es[1], but can
also produce @es[⊥].
  
Any circuit, even ones with a cycle, and be computed in finite time.
On the electrical side of things, this is because, for constructive circuits,
for any delay time in the computation of a gate there exists some clock time
for which the circuit will always stabilize. On the logic side, the
functions which define the gates are monotonic: once a value transitions
from @es[⊥] to @es[0] or @es[1] it can never change. This means that
there is always a fixed-point when evaluating that circuit, and it should
take no more iterations through the whole circuit to find that fixed-point than
the number of gates in the circuit.

@section[#:tag "back:circ:form"]{Circuits, more formally}

@[figure "circuit-grammar" "A Grammar for Circuits"  circuit-lang]

Now, on to a formal definition of a circuit. A circuit @es[c] can be defined as a triple
@es[(circ EQ I O)] where @es[I] is a set of names of input wires, @es[O] is a set of names
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
@centered[
 @[with-paper-rewriters
   [hbl-append
    @es[circuit]
    @[def-t " "]
    @es[=]
    @[def-t " ⟨"]
    @es[{(internal = input)}]
    @def-t[", "]
    @es[{input}]
    @def-t[", "]
    @def-t["{"]
    @es[output1]
    @def-t[", "]
    @es[internal]
    @def-t["}⟩"]]]]
would have the initial state
@centered[      
 @[with-paper-rewriters
   [hbl-append
    @es[cs_0]
    [def-t " "]
    @es[=]
    [def-t " "]
                         
    [def-t "{"]
    @es[{internal ↦ ⊥}]
    [def-t ", "]
    @es[{input ↦ 0}]
    [def-t ", "]
    @es[{output1 ↦ ⊥}]
    [def-t "}"]]]]
We would write the XOr circuit from before as:
@centered[
 @[with-paper-rewriters
   [hbl-append
    @es[circuit_xor]
    @[def-t " "]
    @es[=]
    @[def-t " ⟨"]
      
    @def-t["{"]
    @es[(a = (not (parens (and i1 i2))))]
    @def-t[", "]
    @es[(b = (or i1 i2)) ]
    @def-t[", "]
    @es[(out = (and a b))]
    @def-t["}"]
    
    @def-t[", "]
    
    @def-t["{"]
    @es[i1]
    @def-t[", "]
    @es[i2]
    @def-t["}"]
    
    @def-t[", "]
    
    @def-t["{"]
    @es[out]
    @def-t["}⟩"]]]]
And we would write its initial state, when run on @es[1] and @es[1] to be:
@centered[      
 @[with-paper-rewriters
   [hbl-append
    (hbl-append
     (render-op/instructions
      (text "θ" (non-terminal-style) (default-font-size))
      `((superscript ,(es circuit_xor))))
     (render-op/instructions
      (text "" (non-terminal-subscript-style) (default-font-size))
      `((subscript 0))))
    [def-t " "]
    @es[=]
    [def-t " "]              
    [def-t "{"]
    @es[{a ↦ ⊥}]
    [def-t ", "]
    @es[{b ↦ ⊥}]
    [def-t ", "]
    @es[{out ↦ ⊥}]
    [def-t ", "]
    @es[{i1 ↦ 1}]
    [def-t ", "]
    @es[{i2 ↦ 1}]
    [def-t "}"]]]]

I will write @es[(of c w)] for accessing the expression in the circuit
@es[c] for the wire @es[w]. I will write @es[(of cs w)] for accessing
the value of @es[w] in @es[cs]. I will write @es/unchecked[(Ldom cs)]
for the set of all wires defined in @es[cs].

The circuit can then be evaluated by the reduction relation @es[⇀^c],
which is defined in @figure-ref["c-step"]. This reduction relation
has only one rule, which selects one wire in the circuit which currently has
the value @es[⊥], and attempts to evaluate it using the relation @es[(eval^boolean cs e B)].
This relation is adapted from Section 10.3.1 of @cite/title[esterel02]. This relation evaluates
Boolean expressions, giving back a Boolean when the expression is constructive. The relation
does not hold when the truth table in @figure-ref["extended-truth-tables"] would give back @es[⊥].

@figure["c-step"
        "Reduction relation for circuits"
        @circuit-red-pict]


@figure["e-step"
        "Reduction relation for wire expressions"
        @eval^boolean-pict]

The evaluator for circuits @es[eval^circuit] has the
signature:
@centered[@[with-paper-rewriters [render-metafunction eval^circuit #:only-contract? #t]]]
It takes in a set of wires @es[O] we wish to observe and a
circuit, and fully evaluates the circuit by calling @es[⇀^c] until it reaches the fixed-point. The
result a pair of @es[θ] and @es[bool]. The first part is a
map @es[θ] that maps the wires in @es[O] to the values they
have after evaluating the circuit. The second part is a Boolean which is @es[tt]
if and only if the circuit has no wires which are @es[⊥]---that is it
is true when the circuit is constructive. Otherwise it is @es[ff].

@subsection{Registers}

This model can extend to registers by treating each register
as a pair of an input and an output wire. Initially these input
wires is set to @es[0], and on each subsequent cycle (e.g.
each subsequent call to @es[eval^circuit]) these input wires
are given the value of their corresponding output wire in the previous cycle.

@subsection{Contextual Equivalence}
I take the following to be the definition of
contextual equivalence on circuits:@(linebreak)
@definition[#:notation @es[(≃^circuit c_1 c_2)]]{For all
 assignments to the inputs, and all output sets @es[O],
 @es[(= (eval^circuit O c_1) (tup θ B))] if and only if
 @es[(= (eval^circuit O c_2) (tup θ B))]. }
Intuitively, we can understand this to mean that the only
observables of a circuit are the values of its output wires and if
it is constructive, and the only observation a circuit can make about its
context is the state of its input wires.

I base this definition on the procedure given by
@citet[malik-circuit]. This procedure is equivalent to the
reduction relation I give here, which is proved by @citet[mendler-2012] and
@citet[esterel02]. Specifically Lemma 7 of @citet[esterel02]
gives us that this reduction relation is equivalent to what
@citet[mendler-2012] call ternary simulation of the
circuits. Corollary 3 of @citet[mendler-2012] tells us that
this is equivalent to the algorithm given by
@citet[malik-circuit] for evaluating a circuit. Theorems 1,
2, 3, and 5 of @citet[mendler-2012] also give us that
ternary simulation is equivalent to their UN-delay model of
circuits, which is a model of electrical characteristics of
circuit (See definition 6 in that paper). This UN-delay
model is compositional, and thus can be used when analyzing a
circuit without knowing its context.

@subsection{Other definitions}

I write @es[(inputs c)] to access the input set of the circuit, and @es[(outputs c)] for
the output set.

At times the expression of a single wire will be equivalent in a particular
circuit to some other expression. I will describe this with the notation:
@extract-definition["context-eq-wire"]
which equates the wire @es[w] of the circuit @es[c] to the expression @es[wire-value].
For example @es[(≃ (of c_1 w_1) 1)] says that in all
situations the wire @es[w] in the circuit @es[c_1] will have
the value @es[1], and @es[(≃ (of c_2 w_2) (of c_3 w_2))] says
that not matter what, the @es[w_2] wire in both circuits will
always have the same value.


