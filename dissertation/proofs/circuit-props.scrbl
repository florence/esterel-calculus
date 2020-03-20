#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          (except-in "../lib/proof-extras.rkt"  FV FV/e)
          redex/reduction-semantics
          (except-in
           esterel-calculus/redex/test/binding
           closed)
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style]{Circuit Compilation Properties}


This section contains proofs and properties about the
circuit compilation and how it relates to concepts in the
term writing system like term decomposition and free
variables.

@proof[#:label "activation-condition"
       #:title "Activation Condition"
       #:statement @list{for any term @es[p-pure],
        if @es[(= (or (of (compile p-pure) GO) (parens (and (of (compile p-pure) SEL) (of (compile p-pure) RES)))) 0)]
        then all output @es[Kn] and all signals in the output environment are @es[0].}]{
 @cases[#:of p-pure
        #:induction
        #:language esterel/typeset]{
  @#:case[nothing]{The only output is @es[(= (of (compile nothing) K0) (of (compile nothing) GO))],
   which is @es[0] by our premises}
   @#:case[(exit n)]{Analogous to the last case.}
  @#:case[(emit S)]{Analogous to the last case.}
  @#:case[pause]{
   @check[
 (assert-same
  #:constraints '(not (or GO (and --SEL RES)))
  (compile-esterel (term pause))
  (compile-esterel (term nothing)))]
   Thus this follows by the same argument as the @es[nothing] case.}
  @#:case[(signal S p-pure_i)]{
   The compilation here only removes one signal from the interface, therefor
   this holds by induction.
  }
  @#:case[(par p-pure_i q-pure_i)]{
   @es[GO] and @es[RES] are pass in unchanged, and
   @es[(= (of (compile (par p-pure_i q-pure_i)) SEL) (or (of (compile p-pure_i) SEL) (of (compile q-pure_i) SEL)))].
   Therefore our premises must hold on @es[p-pure_i] and @es[q-pure_i].
   Thus, induction, the outputs of @es[(compile p-pure)] and @es[(compile q-pure)] are @es[0].

   The output signals of @es[(compile (par p-pure_i q-pure_i))] are the @es[or] of the inner branches, thus they must be
   @es[0].

   The control outputs of the synchronizer requires at at least some of its inputs be @es[1] to give an output. However
   by our premises and induction they are all @es[0], thus all @es[Kn]s are @es[0].
  }
  @#:case[(seq p-pure_i q-pure_i)]{
   All inputs are passed to @es[(compile p-pure_i)] unchanged,
   thus by induction all of its outputs are @es[0].

   The @es[GO] of @es[(compile q-pure_i)] is given by @es[(of (compile p-pure_i) K0)],
   and the rest of the inputs are broadcast, thus by induction
   all outputs of @es[(compile q-pure_i)] are @es[0]. Therefore all outputs
   of the overall circuit are @es[0].}
  @#:case[(trap p-pure_i)]{
   @es[GO] and @es[RES] are passed to @es[(compile p-pure_i)] unchanged, thus
   by induction the outputs of @es[(compile p-pure_i)] are @es[0].
   Therefore the outputs of the overall circuit are @es[0].
  }
  @#:case[(suspend p-pure_i S)]{
   @es[GO] is passed to @es[(compile p-pure_i)] unchanged. The @es[RES]
   of @es[(compile p-pure_i)] is @es[and]ed with @es[RES], thus it too
   must be @es[0]. Thus
   by induction the outputs of @es[(compile p-pure_i)] are @es[0].
   Therefore the outputs of the overall circuit are @es[0].
  }
  @#:case[(ρ θr WAIT p-pure_i)]{
  In this case @es[GO] and @es[RES] are passed unchanged,
  therefore this follows directly by induction.}
  @#:case[(present S p-pure_i q-pure_i)]{
   The @es[GO] wire of @es[(compile p-pure_i)] and @es[(compile q-pure_i)]
   are @es[and]ed with the overall @es[GO] wire, thus their @es[GO]
   wires must be @es[0]. The @es[RES] wire is broadcast, thus
   it too is @es[0]. Thus by induction the outputs of both branches
   are @es[0]. The outputs are @es[or]ed, therefore the overall
   outputs are all @es[0].}
  @#:case[(loop p) #:ignore]
  @#:case[(loop^stop p q) #:ignore]
   
}}

@proof[#:label "sel-start"
       #:title "Selection Start"
       #:statement @list{for any term @es[p-pure], during the first instant
        @es[(= (of (compile p) SEL) 0)].}]{
 This is easy to see as all registers are initialized to @es[0], and @es[SEL] is
 the @es[or] of all registers.
}

@proof[#:label "activation-constructiveness"
       #:title "Constructive unless Activated"
       #:statement @list{for any term @es[p-pure],
        if @es[(= (or (of (compile p-pure) GO) (parens (and (of (compile p-pure) SEL) (of (compile p-pure) RES)))) 0)]
        then @es[(compile p)] is constructive for any assignments to its inputs.}
       #:interpretation
       @list{The point of this proof is to show that a
        circuit from the compilation of a term can only exhibit
        non-constructive behavior when they are activated,
        justifying that dead code can be erased without effecting the constructivity of
        the overall circuit.}]{
 The inductive arguments of this
 proof are the same as for @proof-ref["activation-condition"],
 thus some details have been elided.
 @cases[#:of p-pure
        #:induction
        #:language esterel/typeset]{
  @#:case[nothing]{
   @check[(assert-totally-constructive
           #:constraints '(not GO)
           (compile-esterel (term nothing)))]}
  @#:case[(emit S)]{
   @check[(assert-totally-constructive
           #:constraints '(not GO)
           (compile-esterel (term (emit S))))]}
  @#:case[(exit n)]{
   @check[(assert-totally-constructive
           #:constraints '(not GO)
           (compile-esterel (term (exit 0))))]
  Note that the actual number on the @es[exit]
  just a label on the wire, therefore this holds for all @es[n].}
  @#:case[pause]{
   @check[(assert-totally-constructive
           #:constraints '(not (or GO (and --SEL RES)))
           (compile-esterel (term pause)))]
  }
  @#:case[(trap p-pure_i)]{This case follows by
   simple induction.}
  @#:case[(suspend p-pure_i S)]{This case follows by
   simple induction.}
  @#:case[(signal S p-pure_i)]{
   By @proof-ref["activation-condition"], the signal outputs
   of @es[(compile p-pure_i)] must be @es[0]. Thus
   the @es[S] wire is @es[0]. By induction
   By induction @es[(compile p-pure_i)] must be constructive.
   Thus all wires are not @es[⊥].
  }
  @#:case[(par p-pure_i q-pure_i)]{
   By @proof-ref["activation-condition"], the control outputs
   of @es[(compile p-pure_i)] and @es[(compile p-pure_i)] must be @es[0].
   
   By induction @es[(compile p-pure_i)] and  @es[(compile q-pure_i)] must be constructive.
   
   As all inputs the the synchronizer are @es[0], one can trace the execution forward to show that it too
   must be constructive.

   Thus all wires are not @es[⊥].
  }
  @#:case[(seq p-pure_i q-pure_i)]{
   By induction @es[(compile p-pure_i)]
   must be constructive. By @proof-ref["activation-condition"],
   all the control outputs @es[(compile p-pure_i)] are @es[0].
   Thus we can perform induction to show that @es[(compile q-pure_i)]
   is constructive. Thus all wires must be constructive.
  }
  @#:case[(present S p-pure_i q-pure_i)]{
   This case follows by induction akin to  the
   same clause in @proof-ref["activation-condition"].}
  @#:case[(ρ θr WAIT p-pure_i)]{
   This case follows by induction akin to  the
   same clause in @proof-ref["activation-condition"].}
  @#:case[(loop p) #:ignore]
  @#:case[(loop^stop p q) #:ignore]

}}

@proof[#:label "S-maintains-across-E"
       #:title "S is maintained across E"
       #:statement
       @list{For all @es[(= p-pure_i (in-hole E q-pure_i))], and
        @es[S],
        if @es[(L∈ Si (inputs (compile p-pure_i)))]
        then
        @es[(≃ (of (compile q-pure_i) Si) (of (compile p-pure_i) Si))]}]{
 @cases[#:induction
        #:of E-pure
        #:language esterel/typeset]{
  @#:case[hole]{Trivial as @es[(= p-pure_i q-pure_i)]}
  @#:case[(trap E-pure)]{As @es[trap] does not change
  touch the signal wires, this follows by induction.}
  @#:case[(suspend E-pure S)]{As @es[suspend] does not change
  touch the signal wires, this follows by induction.}
  @#:case[(par E-pure q-pure_i)]{As @es[par] does not change
  touch the signal wires, this follows by induction.}
  @#:case[(par p-pure_i E-pure)]{As @es[par] does not change
  touch the signal wires, this follows by induction.}
  @#:case[(seq E-pure q-pure_i)]{As @es[par] does not change
  touch the signal wires, this follows by induction.}
  @#:case[(loop^stop E-pure p) #:ignore]
 }
                                   
}

@proof[#:label "GO-maintains-across-E"
       #:title "GO is maintained across E"
       #:statement
       @list{For all @es[(= p-pure (in-hole E q-pure))],
       @es[(≃ (of (compile q-pure) GO) (of (compile p-pure) GO))]}]{
 This proof follows the exact same argument as @proof-ref["S-maintains-across-E"].
}



@proof[#:label "sel-def"
       #:title "Selection Definition"
       #:statement
       @list{For any term @es[(= p-pure (in-hole E q-pure))], There exist some wires such that
        @es[(= (of (compile p-pure) SEL) (or (of (compile q-pure) SEL) w_others ...))]}]{
 This follows trivially from the definition of @es[compile], as @es[SEL] is always
 the @es[or] of the @es[SEL] wires of the inner terms.
}

@proof[#:label "S-output-irrelevant"
       #:title "S output irrelevant"
       #:statement
       @list{For any term @es[(= p-pure (in-hole E q-pure))], for any output wire @es[So] in
        @es[(compile q-pure)] there exists no wire @es[w] that is
        not itself an instance of @es[So] in @es[(compile p-pure)] which
        depends on @es[So]}
       #:interpretation @list{The point of this theorem is to show
        that an @es[(emit S)] cannot be "read" by its context until
        that emit is closed by a @es[signal] or @es[ρ] form.}]{
 This follows from the same argument as @proof-ref["sel-def"].
}

@proof[#:label "FV-equals-IO"
       #:title "Free Variables are Input/Outputs"
       #:statement
       @list{For any @es[p-pure] and @es[S], @es[(L∈ S (FV p-pure))] if any only if  @es[(L∈ S_i (inputs (compile p-pure)))]
        or @es[(L∈ S_o (outputs (compile p-pure)))]}
       #:interpretation @list{This states that the free
        variables of a term capture exactly the input and output
        signal wires. That is then notion ``free variable'' exactly corresponds to the non-control
        part of the circuit interface}]{
                                        
 Note that a signal is free only if it occurs in a
 @es[(present S p-pure q-pure)] or @es[(emit S)] that does not have an
 outer binder. @es[(compile (present S p-pure q-pure))] will generate
 an @es[S_i] wires and @es[(emit S)] will generate an
 @es[S_o] wire. The compilation of all non-binding terms does
 not change the set of input or output signals. The
 compilation of @es[(signal S p-pure)] and @es[(ρ θ A p-pure)] remove
 the @es[S_i] and @es[S_o] wires from the input/output sets
 for the signals they bind. Thus the input/output sets for
 signals exactly match the notion of free variables.
 
}