#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/model/calculus
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style]{Core Theorems}

This section contains the core proofs to justify soundness of the calculus
with respect to the compilation function. The core theorem @proof-ref["Soundness"],
however the most informative theorem is @proof-ref["Soundness-step"].

@proof[#:label "Soundness"
       #:title "Soundness"
       #:statement
       @list{For all @es[p-pure] and @es[q-pure],
        if @es[(CB p-pure)],
        @es[(≡ p-pure q-pure)],
        @es[(= (of (compile p-pure) SEL) 0)], and
        @es[(= (of (compile q-pure) SEL) 0)]
        then
        @es[(≃^circuit (compile p) (compile q))]}
       #:interpretation @list{This theorem says that, at least for the
       first instant/cycle @es[≡] agrees with @es[≃^circuit].}
       #:type 'theorem]{
 @cases[#:of/count ≡ 5
        #:language esterel/typeset
        #:simple-cases]{
  @#:case[sym]{
   In this case we have @es[(≡ p-pure q-pure)]
   because @es[(≡ q-pure p-pure)]. This
   case follows by induction and by @proof-ref["circ-sym"].}
  @#:case[trans]{
   In this case we have @es[(≡ p-pure q-pure)] there exists
   some @es[r-pure] where @es[(≡ p-pure r-pure)] and
   @es[(≡ r-pure q-pure)]. This case
   case follows induction and by @proof-ref["circ-trans"].}
  @#:case[refl]{
   In this case we have @es[(≡ p-pure q-pure)] because
   @es[(= p-pure q-pure)]. This
   case follows by @proof-ref["circ-refl"].
  }
  @#:case[ctx]{
   @es[(≡ p-pure q-pure)] because
   @es[(= p-pure (in-hole C-pure p-pure_i))],
   @es[(= q-pure (in-hole C-pure q-pure_i))], and
   @es[(≡ p-pure_i q-pure_)].
   TODO}
  @#:case[step]{
   In this case we have
   @es[(≡ p-pure q-pure)] because @es[(⇀ p-pure q-pure)].
   This case is given by @proof-ref["Soundness-step"].}}
}


@proof[#:label "Soundness-step"
       #:title "Soundness of Step"
       #:statement
       @list{For all @es[p-pure] and @es[q-pure],
        if @es[(CB p-pure)], @es[(⇀ p-pure q-pure)],
        @es[(= (of (compile p-pure) SEL) 0)], and
        @es[(= (of (compile q-pure) SEL) 0)]
        then
        @es[(≃^circuit (compile p-pure) (compile q-pure))]}
       #:interpretation @list{This theorem says that, at least for the
        first instant/cycle @es[⇀] agrees with @es[≃^circuit].}
       #:type 'theorem]{
 @cases[#:of/reduction-relation (⇀ p-pure q-pure)
        #:drawn-from ⇀
        #:language esterel-eval]{
                                 
  @;ignore par swap
  @#:case[(⇀ (par p q) (par q p) par-swap)]{This is given by @proof-ref["par-swap"].}
  @#:case[(⇀ (par nothing done) done par-nothing)]{This is given by @proof-ref["par-nothing"].}
  @#:case[(⇀ (par (exit n) paused) (exit n) par-1exit)]{This is given by @proof-ref["par1-exit"].}
  @#:case[(⇀ (par (exit n_1) (exit n_2)) (exit (max-mf n_1 n_2)) par-2exit)]{This is given by @proof-ref["par2-exit"].}
  
  @#:case[(⇀ (ρ θr A (in-hole E-pure (present S p-pure q-pure))) (ρ θr A (in-hole E-pure p-pure))
             (judgment-holds (θ-ref-S θr S present))
             is-present)]{This is given by @proof-ref["is-present"].}

  @#:case[(⇀ (ρ θr A (in-hole E-pure (present S p-pure q-pure))) (ρ θr A (in-hole E-pure q-pure))
             (judgment-holds (L∈ S (Ldom θr)))
             (judgment-holds (θ-ref-S θr S unknown))
             (judgment-holds (L¬∈ S (->S (Can-θ (ρ θr A (in-hole E-pure (present S p-pure q-pure))) ·))))
             is-absent)]{This is given by @proof-ref["is-absent"].}

  @#:case[(⇀ (seq nothing q-pure) q-pure
             seq-done)]{This is given by @proof-ref["seq-done"].}

  @#:case[(⇀ (seq (exit n) q-pure) (exit n)
             seq-exit)]{This is given by @proof-ref["seq-exit"].}
  
  @#:case[(⇀ (suspend stopped S) stopped
             suspend)]{This is given by @proof-ref["suspend"].}

  @#:case[(⇀ (trap stopped) (harp stopped)
             trap)]{This is given by @proof-ref["trap"].}

  @#:case[(⇀ (signal S p-pure) (ρ (mtθ+S S unknown) WAIT p-pure)
             signal)]{This is given by @proof-ref["signal"].}

  @#:case[(⇀ (ρ θr_1 A_1 (in-hole E-pure (ρ θr_2 A_2 p-pure))) (ρ (parens (<- θr_1 θr_2)) A_1 (in-hole E-pure p-pure))
             (side-condition (term (A->= A_1 A_2))) 
             merge)]{This is given by @proof-ref["merge"].}

  @#:case[(⇀ (ρ θr GO (in-hole E-pure (emit S))) (ρ (parens (<- θr (mtθ+S S present))) GO (in-hole E-pure nothing))
             (judgment-holds (L∈ S (Ldom θr)))
             emit)]{This is given by @proof-ref["emit"].}
  @;ignoring loop rules for now
  @#:case[(⇀ (loop p) (loop^stop p p)
             loop)
          #:ignore]
  @#:case[(⇀ (loop^stop (exit n) q) (exit n)
             loop^stop-exit)
          #:ignore]
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


@proof[#:title "Symmetry of circuit contextual equality"
       #:label "circ-sym"
       #:statement @list{For all @es[circuit_1], @es[circuit_2],
        if @es[(≃^circuit circuit_1 circuit_2)] then
        @es[(≃^circuit  circuit_2 circuit_1)]}]{
                                                
 As @es[≃^circuit] is defined, at its core, on equality of
 sequences of booleans, and that equality is symmetric, @es[≃^circuit] must be as well.
}
@proof[#:title "Transitivity of  circuit contextual equality"
       #:label "circ-trans"
       
       #:statement @list{For all @es[circuit_1], @es[circuit_2], @es[circuit_3]
        if @es[(≃^circuit circuit_1 circuit_2)] and @es[(≃^circuit circuit_2 circuit_3)] then
        @es[(≃^circuit circuit_1 circuit_3)]}]{
 As @es[≃^circuit] is defined, at its core, on equality of
 sequences of Booleans, and that equality is transitive, @es[≃^circuit] must be as well.}
@proof[#:title "Reflexivity of circuit contextual equality"
       #:label "circ-refl"
       #:statement @list{For all @es[circuit], @es[(≃^circuit circuit circuit)] }]{
 This follows directly from the definition of @es[≃^circuit], which relies on running the
 two circuits. As, in this case, the two circuits are the same then they will behave the same on
 all inputs.
}