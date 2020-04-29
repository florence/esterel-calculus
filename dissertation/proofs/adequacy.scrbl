#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          (except-in "../lib/proof-extras.rkt"
                     FV FV/e θ-get-S)
          redex/reduction-semantics
          redex/pict
          pict
          esterel-calculus/redex/model/calculus
          (only-in esterel-calculus/redex/model/reduction
                   blocked-pure)
          (except-in scribble-abbrevs/latex definition))


@title[#:style paper-title-style]{Adequacy}

This section contains the various lemma's needed for proving Adequacy of @es[eval^esterel].


@proof[#:title "Strongly Canonicalizing"
       #:label "strongly-cannibalizing"
       #:statement
       @list{For all @es[p-pure+GO], @es[q-pure+GO],
        if @es[(⟶^r p-pure+GO q-pure+GO)],
        then @es[(> (count p-pure+GO) (count q-pure+GO))].}
       #:interpretation
       @list{As @es[count] only returns
        natural numbers, by this we can conclude that
        eventually all terms will reach a state
        where there can only reduce by @es[⟶^s].}]{
 @cases[#:of/count ⟶^r 2
        #:induction
        #:language esterel/typeset
        #:simple-cases]{
                                    
  @#:case[(⇀^r p-pure+GO p-pure+GO)]{
   This case is given by @proof-ref["cannibalize-compatible-closure"]. }
  @#:case[(⟶^r (in-hole C-pure+GO p-pure+GO_i) (in-hole C-pure+GO q-pure+GO_i))]{
                  
   In this case we have @es[(⟶^r p-pure+GO_i q-pure+GO_i)]. By induction @es[(> (count p-pure+GO_i) (count q-pure+GO_i))].
   Thus by  @proof-ref["cannibalize-compatible-closure"]
   we can conclude that
   @es[(> (count (in-hole C-pure+GO p-pure+GO_i)) (count (in-hole C-pure+GO q-pure+GO_i)))].
                        
  }
 }
}

@proof[#:title "Strongly Canonicalizing on Compatible Closure"
       #:label "cannibalize-compatible-closure"
       #:statement @list{For all @es[C-pure+GO], @es[p-pure+GO], @es[q-pure+GO],
        if @es[(> (count p-pure+GO) (count q-pure+GO))] then
        @es[(> (count (in-hole C-pure+GO p-pure+GO)) (count (in-hole C-pure+GO q-pure+GO)))]}]{
                                                               
 This follows by a trivial induction over @es[C-pure+GO], as
 each case of @es[(count p-pure+GO)] only addes constants to the
 @es[count] of the subterms.
  
}

@proof[#:title "Strongly Canonicalizing on single step"
       #:label "cannibalize-step"
       #:statement @list{For all @es[p-pure+GO], @es[q-pure+GO],
        if @es[(⇀^r p-pure+GO q-pure+GO)]
        then @es[(> (count p-pure+GO) (count q-pure+GO))].}]{

 @cases[#:of/reduction-relation (⇀^r p-pure+GO q-pure+GO)
        #:drawn-from ⇀
        #:language esterel-eval]{
  @#:case[(⇀ (par nothing done) done par-nothing)]{
   This case follows immediately from the definition of @es[count].
  }
  @#:case[(⇀ (par (exit n) paused) (exit n) par-1exit)]{
   This case follows immediately from the definition of @es[count].}
  @#:case[(⇀ (par (exit n_1) (exit n_2)) (exit (max-mf n_1 n_2)) par-2exit)]{
   This case follows immediately from the definition of @es[count].}
  
  @#:case[(⇀ (ρ θr A (in-hole E (present S p-pure+GO q-pure+GO))) (ρ θr A (in-hole E p-pure+GO))
             (judgment-holds (θ-ref-S θr S present))
             is-present)]{
   By @proof-ref["cannibalize-compatible-closure"],
   we can establish our result if @es[(> (count (present S p-pure+GO q-pure+GO)) p-pure+GO)].
   This is trivially true.}

  @#:case[(⇀ (ρ θr A (in-hole E (present S p-pure+GO q-pure+GO))) (ρ θr A (in-hole E q-pure+GO))
             (judgment-holds (L∈ S (Ldom θr)))
             (judgment-holds (θ-ref-S θr S unknown))
             (judgment-holds (L¬∈ S (->S (Can-θ (ρ θr A (in-hole E (present S p-pure+GO q-pure+GO))) ·))))
             is-absent)]{
   This case follows by an analgous argument to the previous case.
  }

  @#:case[(⇀ (seq nothing q-pure+GO) q-pure+GO
             seq-done)]{
   This case follows immediately from the definition of @es[count].
  }

  @#:case[(⇀ (seq (exit n) q-pure+GO) (exit n)
             seq-exit)]{
   This case follows immediately from the definition of @es[count].
  }
  
  @#:case[(⇀ (suspend stopped S) stopped
             suspend)]{This case follows immediately from the definition of @es[count].}

  @#:case[(⇀ (trap stopped) (harp stopped)
             trap)]{
   This case follows immediately from the definition of @es[count].}

  @#:case[(⇀ (signal S p-pure+GO) (ρ (mtθ+S S unknown) WAIT p-pure+GO)
             signal)]{
   This case follows immediately from the definition of @es[count].}

  @#:case[(⇀ (ρ θr_1 A_1 (in-hole E-pure+GO (ρ θr_2 A_2 p-pure+GO))) (ρ (parens (<- θr_1 θr_2)) A_1 (in-hole E-pure+GO p-pure+GO))
             (side-condition (term (A->= A_1 A_2))) 
             merge)]{
   @sequenced{
    @#:step[inner]{@es[(> (count (ρ θr_2 A_2 p-pure+GO)) (count p-pure+GO))], by the definition of @es[count].}
    @#:step[outer]{for any @es[r].
     @es[(= (count (ρ θr_1 A_1 (in-hole E-pure+GO r))) (count (ρ (parens (<- θr_1 θr_2)) A_1 (in-hole E-pure+GO r-pure+GO))))], by the definition of @es[count].}
    @#:step[eq]{By @outer on @es[p], @es[(= (count (ρ θr_1 A_1 (in-hole E p-pure+GO))) (count (ρ (parens (<- θr_1 θr_2)) A_1 (in-hole E p-pure+GO))))].}
    @#:step[_]{By @eq, @inner, and @proof-ref["cannibalize-compatible-closure"],@(linebreak)
     @es[(> (count (ρ θr_1 A_1 (in-hole E-pure+GO (ρ θr_2 A_2 p-pure+GO)))) (ρ (parens (<- θr_1 θr_2)) A_1 (in-hole E-pure+GO p-pure+GO)))]
  }}}

  @#:case[(⇀ (ρ θr GO (in-hole E-pure+GO (emit S))) (ρ (parens (<- θr (mtθ+S S present))) GO (in-hole E-pure+GO nothing))
             (judgment-holds (L∈ S (Ldom θr)))
             emit)]{
   @sequenced{
    @#:step[eq]{For all @es[r], @es[(= (count (ρ θr GO (in-hole E r-pure+GO))) (count (ρ (parens (<- θr (mtθ+S S present))) GO (in-hole E r-pure+GO))))],
     By the definition of @es[count].
    }
    @#:step[lt]{@es[(> (count (emit S)) (count nothing))], by the definition of @es[count].}
    @#:step[_]{@es[(> (count (ρ θr GO (in-hole E (emit S)))) (count (ρ (parens (<- θr (mtθ+S S present))) GO (in-hole E nothing))))]
     by @eq, @lt, and @@proof-ref["cannibalize-compatible-closure"].}}}
  @;ignoring loop rules for now
  @#:case[(⇀ (loop p) (loop^stop p p)
             loop)
          #:ignore]
  @#:case[(⇀ (loop^stop (exit n) q) (exit n)
             loop^stop-exit)
          #:ignore]
  @;ignore par swap
  @#:case[(⇀ (par p q) (par q p) par-swap) #:ignore]
  @;ingore the state rules
  @#:case[(⇀
           (ρ θr A (in-hole E (shared s := e p)))
           (ρ θr A (in-hole E (ρ (mtθ+s s ev old) WAIT p)))
           (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
           (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (shared s := e p)))))
           (where ev (δ e θr))
           shared) #:ignore]
  @#:case[(⇀
           (ρ θr A (in-hole E (var x := e p)))
           (ρ θr A (in-hole E (ρ (mtθ+x x (δ e θr)) WAIT p)))
           (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
           (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (var x := e p)))))
           var) #:ignore]
  @#:case[(⇀
           (ρ θr A (in-hole E (:= x e)))
           (ρ (id-but-typeset-some-parens (<- θr (mtθ+x x (δ e θr)))) A (in-hole E nothing))
           (judgment-holds (L∈ x (Ldom θr)))
           (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
           (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (:= x e)))))
           set-var) #:ignore]
   
   
  @#:case[(⇀ (ρ θr A (in-hole E (if x p q)))
             (ρ θr A (in-hole E q))
             (judgment-holds (θ-ref-x θr x 0))
             if-false) #:ignore]
  @#:case[(⇀ (ρ θr A (in-hole E (if x p q)))
             (ρ θr A (in-hole E p))
             (judgment-holds (L∈ x (Ldom θr)))
             (judgment-holds (¬θ-ref-x θr x 0))
             if-true) #:ignore]




        

  @#:case[(⇀
           (ρ θr GO (in-hole E (<= s e)))
           (ρ (id-but-typeset-some-parens (<- θr (mtθ+s s (δ e θr) new))) GO (in-hole E nothing))
           (judgment-holds (θ-ref-s θr s _ old))
           (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
           (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (<= s e)))))
           set-old) #:ignore]

  @#:case[(⇀
           (ρ θr GO (in-hole E (<= s e)))
           (ρ (id-but-typeset-some-parens (<- θr (mtθ+s s (Σ ev (δ e θr)) new))) GO (in-hole E nothing))
           (judgment-holds (L⊂ (LFV/e e) (Ldom θr)))
           (judgment-holds (θ-ref-s θr s _ new))
           (side-condition (term (all-ready? (LFV/e e) θr (in-hole E (<= s e)))))
           (where ev (δ e θr))
           set-new) #:ignore]
  
 }
}

@include-section["adequacy/positive.scrbl"]
@include-section["adequacy/negative.scrbl"]