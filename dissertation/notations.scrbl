#lang scribble/base

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/proof-extras.rkt"
          "lib/jf-figures.rkt"
          "lib/misc-figures.rkt"
          "lib/rule-figures.rkt"
          "lib/circuit-diagrams.rkt"
          "proofs/adequacy/can-props.rkt"
          (except-in redex/reduction-semantics nothing)
          redex/pict
          (only-in pict hbl-append)
          (except-in scribble-abbrevs/latex definition)
          (except-in racket/list count)
          (except-in scribble/core table)
          racket/match
          pict)

@para[#:style 'pretitle]{@latex-lit["appendices"]}

@title[#:style paper-title-style]{Definitions}

@section[#:tag "sec:defcirc" "Circuits"]


@[begin
 (define (clausef term pict)
   (vl-append
    (hbl-append term (es =))
    (hc-append (blank 10)
               pict)))]
@definition[#:notation (hbl-append (es (compile p)) (es ⟶) (es circuit))
            #:index @es[compile]]{
                                                                          
 @add-between[(for/list ([c1 (in-list compile-def)])
                (match-define (list t c p) c1)
                (index-as (pict+tag c t) (clausef c p)))
              (element 'newline '())]

}

@definition[#:notation @es[(binds (compile p) θ)]
            #:read-as @list{@es[θ] binds @es[(compile p)]}]{
 @es[(binds (compile p) θ)] if and only if
 @es[∀] @es[(L∈ S (Ldom θ))],
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

@definition[#:notation @list{@es[p], @es[q]}
            #:index @es[p]
            lang/state]

@definition[#:notation @es[(⇀ p q)]
            #:index @es[⇀]]{
 @reduction-relation-pict
}

@definition[#:notation @es[(⟶ p q)]
            #:index @es[⟶]]{
 The compatible closure of @es[⇀].
}

@definition[#:notation @es[(≡ p q)]
            #:index @es[≡]]{
 The transitive, reflexive, symmetric, compatible closure of @es[⇀].
}

@definition[
 #:notation @list{@es[(eval^esterel O p)] @es[⟶] @es[(tup θ bool)]}
 #:index @es[eval^esterel]
 #:read-as @list{Evaluate the program @es[p] using the output signals @es[O].}]{

 @with-paper-rewriters[@render-metafunction[eval^esterel]]

}

@definition[
 #:notation @es[(restrict θ O p)]
 #:read-as @list{Restrict @es[θ] to signals in @es[O], given a program @es[p].}]{

 @es[(= (restrict θ O p) (restrict-defintion θ O p))]
 @(linebreak) where
 @(linebreak) @with-paper-rewriters[@render-metafunction[DR #:contract? #t]]

}

@definition[#:notation @es[(blocked-pure θ A E p)]
            #:index @es[blocked-pure]
            #:read-as @list{The term @es[p] cannot reduce (is blocked)
             in the context @es[(ρ θ A (in-hole E p))]}]{
 @pure-blocked-pict
}


@definition[#:notation @es[(Can p θ)]
            #:index @es[Can]]{
 @Can-pict
}

@definition[#:notation @es[(Can-θ (ρ θ_1 A p) θ_2)]
            #:index @es[Can-θ]]{
 @Canθ-pict
}

@definition[#:notation @es[(complete-with-respect-to θr done)]]{
 For all @es[(L∈ S (Ldom θr))],
 @es[(= (θ-get-S θr S) present)] or
 @es[(= (θ-get-S θr S) unknown)]
 and @es[(L¬∈ S (->S (Can-θ (ρ θr GO done) ·)))].
}


@definition[
 #:notation @list{@es[(count p)]}
 #:index @es[count]
 #:read-as @list{An upper bound in the number of @es[⟶^r]
  steps @es[p] may take. (The name is a very bad pun on the
  physics concept of an Action Principle.)}]{

 @with-paper-rewriters[@render-metafunction[count #:contract? #t]]

}


@section[#:tag "sec:defaux" "Auxiliary"]

@definition[#:notation @es[(all-bot p-pure θ cs)]
            #:index @es[all-bot]]{
 @[with-paper-rewriters @[render-judgment-form all-bot]]
}

@definition[#:notation @es[(all-bot-S p-pure θ cs)]
            #:index @es[all-bot-S]]{
 @[with-paper-rewriters @[render-judgment-form all-bot-S]]
}

@definition[#:notation @es[(all-bot-n p-pure θ cs)]
            #:index @es[all-bot-n]]{
 @[with-paper-rewriters @[render-judgment-form all-bot-n]]
}

@definition[#:notation @es[(all-bot-rec p-pure θ cs)]
            #:index @es[all-bot-rec]]{
 @all-bot-rec-pict
}