#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style]{Circuit Compilation Properties}

@proof[#:label "sel-later"
       #:title "Selection Later"
       #:statement @list{for any term @es[p],
        if @es[(= (of (compile p) GO) 0)] in every instant then
        @es[(= (of (compile p) SEL) 0)]}]{
 TODO
}

@proof[#:label "sel-def"
       #:title "Selection Definition"
       #:statement
       @list{For any term @es[(= p (in-hole E q))], There exist some wires such that
        @es[(= (of (compile p) SEL) (or (of (compile q) SEL) w_others ...))]}]{
}

@proof[#:label "activation-condition"
       #:title "Activation Condition"
       #:statement @list{for any term @es[p],
        if @es[(= (or (of (compile p) GO) (parens (and (of (compile p) SEL) (of (compile p) RES)))) 0)]
        then all output @es[Kn] and all signals in the output environment @es[θ_o] are @es[0].}]{
 TODO
}

@proof[#:label "activation-constructiveness"
       #:title "Constructive unless Activated"
       #:statement @list{for any term @es[p],
        if @es[(= (or (of (compile p) GO) (parens (and (of (compile p) SEL) (of (compile p) RES)))) 0)]
        then @es[(compile p)] is constructive for any assignments to its inputs.}
       #:interpretation
       @list{The point of this proof is to show that a
        circuit from the compilation of a term can only exhibit
        non-constructive behavior when they are activated,
        justifying that dead code can be erased without effecting the constructivity of
        the overall circuit.}]{
 TODO
}

@proof[#:label "S-maintains-across-E"
       #:title "S is maintained across E"
       #:statement
       @list{For some term @es[(= p (in-hole E q))] if there is some
        signal wire @es[S_i] then @es[(= (of (compile q) S) (of (compile p) S))]}]{
 TODO
}

@proof[#:label "GO-maintains-across-E"
       #:title "GO is maintained across E"
       #:statement
       @list{For some term @es[(= p (in-hole E q))]
        then @es[(= (of (compile q) GO) (of (compile p) GO))]}]{
 TODO
}

@proof[#:label "context-safety"
       #:title "Context Safety"
       #:type 'theorem
       #:statement
       @list{For any term @es[(= p (in-hole C q))], if @es[(=> (= (of (compile p) SEL) 1) (= (of (compile p) GO) 0))]
        then @es[(=> (= (of (compile q) SEL) 1) (= (of (compile q) GO) 0))]}]{
                                                                              
 Note that this abuses the of notation because of C
 TODO
                                                                              
}

@proof[#:label "S-output-irrelevant"
       #:title "S output irrelevant"
       #:statement
       @list{For any term @es[(= p (in-hole E q))], for any output wire @es[S_o] in
        @es[(compile q)] there exists no wire @es[w] that is
        not itself an instance of @es[S_o] in @es[(compile p)] such that
        depends on @es[S_o]}
       #:interpretation @list{The point of this theorem is to show
        that an @es[(emit S)] cannot be "read" by its context until
        that emit is closed by a @es[signal] or @es[ρ] form.}]{
 TODO
}