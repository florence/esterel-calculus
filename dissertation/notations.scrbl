#lang scribble/base

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/proof-extras.rkt"
          "lib/jf-figures.rkt"
          "lib/misc-figures.rkt"
          "lib/rule-figures.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (except-in scribble-abbrevs/latex definition))

@para[#:style 'pretitle]{@latex-lit["appendices"]}

@title[#:style paper-title-style]{Definitions}

@section[#:tag "sec:defcirc" "Circuits"]

@definition[#:notation @es[(binds (compile p) θ)]
            #:read-as @list{@es[θ] binds @es[(compile p)]}]{
 @es[(binds (compile p) θ)] if and only if
 @es[∀] @es[(L∈ S (Ldom θ))],
 @es[(= (of (compile p) S_o) (of (compile p) S_i))],
 and
 @es[(= (θ-get-S θ S) present)] if and only if @es[(= (of (compile p) S_i) 1)],
 and
 @es[(= (θ-get-S θ S) absent)] if any only if @es[(= (of (compile p) S_i) 0)].

 Note that this would mean that
 @es[(binds (compile p_i) (mtθ+S S absent))] implies that
 @es[(binds (compile p_i) (mtθ+S S unknown))], as
 @es[(mtθ+S S unknown)] places less restrictions on
 @es[(compile p_i)] than @es[(mtθ+S S absent)]. This also
 means that @es[(binds (compile p) ·)] always holds.

}

@definition[#:notation @es[(binds (compile p) A)]
            #:read-as @list{@es[A] binds @es[(compile p)]}]{
 @es[(binds (compile p) A)] if and only if @es[(= A GO)] implies that @es[(= (of (compile p) GO) 1)].
}

@definition[#:notation @es[(= (of c w) wire-value)]]{

 @es[c] is contextually equivalent to a circuit
 in which the definition of the wire @es[w]
 is replace by @es[wire-value].

}

@section[#:tag "sec:defcalc" "Calculus"]

@definition[#:notation @list{@es[p], @es[q]} lang/state]

@definition[#:notation @es[(⇀ p q)]]{
 @reduction-relation-pict
}

@definition[#:notation @es[(blocked-pure θ A E p)]
            #:read-as @list{The term @es[p] cannot reduce (is blocked)
             in the context @es[(ρ θ A (in-hole E p))]}]{
 @pure-blocked-pict
}


@definition[#:notation @es[(Can p θ)]]{
 @Can-pict
}

@definition[#:notation @es[(Can-θ (ρ θ_1 A p) θ_2)]]{
 @Canθ-pict
}

@definition[#:notation @es[(complete-with-respect-to θ done)]]{
 For all @es[(L∈ S (Ldom θ))],
 @es[(= (θ-get-S θ S) present)] or
 @es[(= (θ-get-S θ S) unknown)]
 and @es[(L¬∈ S (->S (Can-θ (ρ θ GO done) ·)))].
}
