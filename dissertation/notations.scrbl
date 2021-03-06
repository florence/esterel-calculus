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
          esterel-calculus/redex/model/reduction
          (except-in redex/reduction-semantics nothing)
          redex/pict
          (only-in pict hbl-append)
          (except-in scribble-abbrevs/latex definition)
          (except-in racket/list count)
          (except-in scribble/core table)
          racket/match
          pict)

@para[#:style 'pretitle]{@latex-lit["appendices"]}

@title[#:tag "sec:def" #:style paper-title-style]{Definitions}
@para[#:style 'pretitle]{@latex-lit["appendix"]}
@section[#:tag "sec:defcirc" "Circuits"]


@[begin
 (define (clausef term pict)
   (vl-append
    (hbl-append term (es =))
    (hc-append (blank 10)
               pict)))]
@definition[#:notation (es (compile p-pure))
            #:index @es[compile]
            #:tag "compile"
            #:center? #f]{
 @(linebreak)
 @add-between[(for/list ([c1 (in-list compile-def)])
                (match-define (list _ t c p) c1)
                (index-as (pict+tag c t) (clausef c p)))
              (linebreak)]
}

@definition[#:notation @es[(binds (compile p-pure) θ)]
            #:read-as @list{@es[θ] binds @es[(compile p-pure)]}
            #:tag "binds"]{
 @es[(binds (compile p-pure) θ)] if and only if
 @es[∀] @es[(L∈ S (Ldom θ))],
 @es[(= (θ-get-S θ S) present)] ⇔ @es[(≃ (of (compile p-pure) Si) 1)],
 and
 @es[(= (θ-get-S θ S) absent)] ⇔ @es[(≃ (of (compile p-pure) Si) 0)].
 @;{
  Note that this would mean that
  @es[(binds (compile p-pure) (mtθ+S S absent))] implies that
  @es[(binds (compile p-pure) (mtθ+S S unknown))], as
  @es[(mtθ+S S unknown)] places less restrictions on
  @es[(compile p-pure)] than @es[(mtθ+S S absent)]. This also
  means that @es[(binds (compile p-pure) ·)] always holds.
 }
}

@definition[#:notation @es[(binds (compile p-pure) A)]
            #:read-as @list{@es[A] binds @es[(compile p-pure)]}]{
 @es[(binds (compile p-pure) A)] if and only if @es[(= A GO)] implies that @es[(= (of (compile p-pure) GO) 1)].
}

@definition[#:notation @es[(≃ (of c w) wire-value)]
            #:index (list @es[≃] @es[≃])
            #:tag "context-eq-wire"]{

 @es[c] is contextually equivalent to a circuit
 in which the definition of the wire @es[w]
 is replace by @es[wire-value].

}

@section[#:tag "sec:defcalc" "Calculus"]

@definition[#:notation @list{@es[p], @es[q]}
            #:index @es[p]
            lang/state]


@definition[#:notation @list{@es[p-pure], @es[q-pure]}
            #:index @es[p-pure]
            lang/pure]
@(element "newpage" '())
@definition[#:notation @es[(⇀ p q)]
            #:index @es[⇀]]{
 @reduction-relation-pict
}
@(element "newpage" '())
@definition[#:notation @es[(⟶ p q)]
            #:index @es[⟶]]{
 The compatible closure of @es[⇀].
}

@definition[#:notation @es[(≡ p q)]
            #:index @es[≡]]{
 The transitive, reflexive, symmetric, compatible closure of @es[⇀].
}

@definition[
 #:notation @list{@es/unchecked[(eval^esterel O p)]}
 #:index @es[eval^esterel]]{

 @with-paper-rewriters[@render-metafunction[eval^esterel #:contract? #t]]

}

@definition[
 #:notation @es[(restrict θ O p)]
 #:index @es[restrict]
 #:tag "restrict"
 #:read-as @list{Restrict @es[θ] to signals in @es[O], given their values
  as determined by the program @es[p].}]{
 @(let ()
    (define b (with-paper-rewriters (text "{" (default-style) (default-font-size))))
    (define x @es[(restrict-defintion θ O p)])
    (define b2 (scale (scale-to-fit (scale b 5) (pict-width b) (pict-height b)) 2))
    @[hc-append
      [hbl-append [es (θ-get-S (restrict θ O p) S)] @es[=]]
      b2
      x])}
@(element "newpage" '())
@definition[#:notation @es[(blocked-pure θr A E-pure p-pure)]
            #:index @es[blocked-pure]]{
 @pure-blocked-pict
}
@(element "newpage" '())

@definition[#:notation @es[(Can p θ)]
            #:index @es[Can]]{
 @Can-all-pict
}

@definition[#:notation @es[(Can-θ (ρ θ_1 A p) θ_2)]
            #:index (list @es[Can] @es[Can-θ])]{
 @Canθ-pict
}

@definition[#:notation @es[(complete-with-respect-to θr done)]
            #:index @es[complete-with-respect-to]
            #:tag "complete-wrt"]{
 For all @es[(L∈ S (Ldom θr))], either
 @es[(= (θ-get-S θr S) present)] or
 @es[(= (θ-get-S θr S) unknown)]
 and @es[(L¬∈ S (->S (Can-θ (ρ θr GO done) ·)))].
}


@section[#:tag "sec:defaux" "Auxiliary"]

@definition[
 #:notation @es[(next-instant complete*)]
 #:index @es[next-instant]
 #:tag "next-instant"
 ]{
 @with-paper-rewriters[@render-metafunction[next-instant #:contract? #t]]
}

@definition[
 #:notation @list{@es[(count p)]}
 #:index @es[count]
 #:read-as @list{An upper bound in the number of @es[⟶^r]
  steps @es[p] may take. (The name is a very bad pun on the
  physics notation for an Action.)}]{

 @with-paper-rewriters[@render-metafunction[count #:contract? #t]]

}


@definition[#:notation @es[(closed p-pure+GO)]
            #:tag "closed"
            #:index @es[closed]]{
 @with-paper-rewriters[@render-judgment-form[closed]]
}

@definition[#:notation @es[(all-bot p-pure θ cs)]
            #:index @es[all-bot]
            #:tag "nc"]{
 @[with-paper-rewriters @[render-judgment-form all-bot]]
}

@definition[#:notation @es[(all-bot-S p-pure θ cs)]
            #:index @es[all-bot-S]
            #:tag "nc-S"]{
 @[with-paper-rewriters @[render-judgment-form all-bot-S]]
}


@definition[#:notation @es[(all-bot-n p-pure θ cs)]
            #:index @es[all-bot-n]
            #:tag "nc-κ"]{
 @[with-paper-rewriters @[render-judgment-form all-bot-n]]
}


@definition[#:notation @es[(sub p-pure q-pure cs)]
            #:index @es[sub]]{

 When @es[c] is the compilation of @es[p-pure], get the substate of @es[cs]
 corresponding to the subterm @es[q-pure].
 
}

@(element "newpage" '())
@definition[#:notation @es[(all-bot-rec p-pure θ cs)]
            #:index @es[all-bot-rec]
            #:tag "nc-r"]{
 @all-bot-rec-pict
}

@definition[#:notation @es[(CB p)]
            CB-pict]

@section[#:tag "eval-and-testing" "Reduction Strategy"]

@definition[#:notation @es[⇁]]{
 @strat-pict
}

@definition[#:notation @es[(leftmost θr A p E)]]{
 @leftmost-pict
}

@definition[#:notation @es[(leftmost* θr A p E_1 E_2)]]{
 @leftmost*-pict
}