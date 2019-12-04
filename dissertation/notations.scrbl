#lang scribble/base

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/proof-extras.rkt"
          "lib/jf-figures.rkt"
          "lib/misc-figures.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (except-in scribble-abbrevs/latex definition))

@para[#:style 'pretitle]{@latex-lit["appendices"]}

@title[#:style paper-title-style]{Definitions}

@definition[#:notation @es[(binds (compile p) θ)]
            #:read-as @list{@es[θ] binds @es[(compile p)]}]{
 @es[(binds (compile p) θ)] if and only if
 @es[∀] @es[(L∈ S (Ldom θ))],
 @es[(= (θ-get-S θ S) present)] if and only if @es[(= (of (compile p) S_i) 1)]
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

@definition[#:notation @es[(= (of (compile p) w) wire-value)]]{

 TODO formalize better
 
 @es[(= (of (compile p) w) wire-value)] if and only if,
 given our current assumptions, we can prove that that wire @es[w] in the interface
 of @es[(compile p)] is equivalent to @es[wire-value].

 For example: @es[(= (of (compile p) S_o) 1)] would mean that
 @es[(compile p)] is guaranteed to emit @es[S].
 @es[(= (of (compile (emit S)) S_o) (of (compile (emit S)) GO))]
 means that @es[(compile (emit S))] will emit @es[S] exactly when it's
 @es[GO] wire is @es[1]. Note that if we prove @es[(= (of (compile (emit S)) GO) 1)]
 Then we can also state that @es[(= (of (compile (emit S)) S_o) 1)].

 I will, at times, write this in terms of subterms of a given term. For example
 @es[(= (of (compile (signal S p_i)) SEL) (of (compile p_i) SEL))], which means
 that the @es[SEL] wire of compiling @es[(signal S p_i)] is given by the @es[SEL] wire
 of compiling @es[p_i]. In this case the notation is clean and unambiguous as @es[(compile p_i)]
 only shows up once in the compilation of @es[(signal S p_i)].

 In in case where the subterm is within a @es[loop] the
 notation would be ambiguous however. For example saying
 @es[(= (of (compile (loop p_i)) SEL) (of (compile p_i) SEL))]
 is meaningless as @es[(compile p_i)] shows up twice in the
 @es[(compile (loop p_i))], thus its ambiguous which @es[SEL]
 wire we are referring to. In these cases
 @es[(of (compile p) w)] will never appear on the right hand
 side of @es/unchecked[=]. If it
 shows up on the left hand side it is be interpreted as
 all instances of the given wire, e.g. in the given example
 @es[(= (of (compile p_i) S_o) 0)] means that the @es[S_o]
 wire of both instances of @es[(compile p_i)] will be zero.
 When these cases occur I will explicitly point out this
 subtly.

}

@definition[#:notation @es[(complete-with-respect-to θ done)]]{
 For all @es[(L∈ S (Ldom θ))],
 @es[(= (θ-get-S θ S) present)] or
 @es[(= (θ-get-S θ S) unknown)]
 and @es[(L¬∈ S (->S (Can-θ (ρ θ GO done) ·)))].
}

@definition[#:notation @es[(blocked-pure θ A E p)]
            #:read-as @list{The term @es[p] cannot reduce (is blocked)
             in the context @es[(ρ θ A (in-hole E p))]}]{
 @pure-blocked-pict
}


@definition[#:notation @es[(Can p θ)]]{
 @Can-pict
}

@definition[#:notation @es[(Canθ p θ)]]{
 @Canθ-pict
}