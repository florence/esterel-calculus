#lang scribble/acmart @acmsmall

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/test/generator
          scribble-abbrevs/latex)

@title[#:style paper-title-style]{Proofs}
@appendix

@proof[#:label "FullyAbstract"
       #:title "Fully Abstract Compilation"
       #:statement
       @list{For all @es[p] and @es[q], @es[(≡ p q)] implies that
        @es[(≃ (compile p) (compile q))]}
       #:interpretation "is it really?"
       #:type 'proof]{
 TODO
}


@proof[#:label "FullStep"
       #:title "Fully Abstract Compilation of Step"
       #:statement
       @list{For all @es[p] and @es[q], @es[(⇀ p q)] implies that
        @es[(≃ (compile p) (compile q))]}
       #:interpretation "is it really?"
       #:type 'lemma]{
 next we do
 @cases[#:of/unchecked @list{derivation of @es[(⇀ p q)]}
        #:language esterel-check]
}

@proof[#:label "par-swap"
       #:title "par-swap is sound"
       #:statement
       @list{as @es[(⇀ (par p q) (par q p))], show that @es[(≃ (compile (par p q)) (compile (par q p)))]}]{
 This can be seen trivally, as the graphs of @es[(compile (par p q))]
 and @es[(compile (par q p))] are symmetric.
}

@proof[#:label "par-nothing"
       #:title "par-nothing is sound"
       #:statement
       @list{as @es[(⇀ (par nothing done) done)], show that @es[(≃ (compile (par nothing done)) (compile done))]}]{
 This proof is given in the notebook [par-done], which actually shows the more general
 @es[(≃ (compile (par nothing p)) (compile p))].
}

@proof[#:label "trap"
       #:title "trap is sound"
       #:statement
       @list{as @es[(⇀ (trap stopped) (harp stopped))], show that
        @es[(≃ (compile (trap stopped)) (compile (harp stopped)))]}]{
 @cases[#:of stopped
        #:language esterel-eval
        @#:case[nothing]{
          Note that @es[(= (harp nothing) nothing)].
          TODO Draw pictures, which are the same}
        @#:case[(exit 0)]{
          Note that @es[(= (harp (exit 0)) nothing)].
          TODO draw pictures, which are the same.
         }
        @#:case[(exit n)]{
          Where @es[(> n 0)].

          Note that @es[(= (harp (exit n)) (exit (sub1 n)))].
          TODO draw pictures, which are the same.
          ]}
        ]}

@proof[#:label "suspend"
       #:title "suspend is sound"
       #:statement
       @list{as @es[(⇀ (suspend done S) done)], show that
        @es[(≃ (compile (suspend done S)) (compile done))]}]{
 This is proved in the [suspend] notebook.
}

@proof[#:label "seq-done"
       #:title "seq-done is sound"
       #:statement
       @list{as @es[(⇀ (seq nothing q) q)], show that
        @es[(≃ (compile (seq nothing q)) (compile q))]}]{
 TODO draw graphs.
}

@proof[#:label "par2-exit"
       #:title "par2-exit is sound"
       #:statement
       @list{as @es[(⇀ (par (exit n_1) (exit n_2)) (exit (max-mf n_1 n_2)))], show that
        @es[(≃ (compile (par (exit n_1) (exit n_2))) (compile (exit (max-mf n_1 n_2))))]}]{
 @cases[#:of/unchecked
 @list{@es[(= n_1 n_2)], @es[(> n_1 n_2)], and @es[(< n_1 n_2)]}
 @#:case[@es[(= n_1 n_2)]]{
   @cases[#:of nat_1
          #:induction
          #:checks 20
          @#:case[0]{See [par-2exit] notebook}
          @#:case[(Suc mat)]{
              Note that in this case the @es[lem-n] wire in the
              the synchronizer will be equal to @es[lem],
              as all other exit codes will be @es[0],
              and therefore @es[(= lem-n (or lem 0 ...))]. The
              same will hold for @es[rem-n]. We now can see
              that we have a synchronizer of the same shape as
              in the previous subcase. Thus the remainder of this
              proof proceeds in the same way.}]}
 @#:case[@es[(> n_1 n_2)]]{
   @cases[#:of nat_2
          #:induction
          #:checks 20
          @#:case[0]{ Note that all @es[ln] up to
              @es[l2+n_1] must be @es[0]. Therefore all @es[kn] up to that
              point must be @es[0]. The notebook [par-2exit] shows
              that the remainder of the synchronizer behaves as @es[(compile (exit n_1))].
             }
          @#:case[(Suc mat)]{ All @es[kn] up to @es[kn_2]
              must be zero as there are no corresponding @es[ln] or
              @es[rn] wires. From this point
              we can use analogous reasoning to the previous subcase.}]}
 @#:case[@es[(< n_1 n_2)]]{ This case analogous to the
   previous case, as the synchronizer (and @es[par]) are
   symmetric.}]
}

@proof[#:label "par1-exit"
       #:title "par1-exit is sound"
       #:statement @list{as @es[(⇀ (par (exit n) paused) (exit n))], show that
        @es[(≃ (compile (par (exit n) paused)) (compile (exit n)))]}]{
 The proof of this is given in the [par1-exit] notebook.
}

@proof[#:label "seq-exit"
       #:title "seq-exit is sound"
       #:statement @list{as @es[(⇀ (seq (exit n) q) (exit n))], show that
        @es[(≃ (compile (seq (exit n) q)) (compile (exit n)))]}]{
 Note that @es[(= (of (compile q) GO) 0)]. Thus by @proof-ref["sel-later"],
           @es[(= (of (compile q) SEL) 0)]. Thus by @proof-ref["activation-condition"]
           all output wires of @es[(compile q)] are @es[0].
           Thus the only wire which can be true is @es[K2+n], which in this case will
           be equal to @es[(of (compile (exit n)) K2+n)]. Thus the two circuits are equal.

           TODO constructivity?
}

@proof[#:label "signal"
       #:title "signal is sound"
       #:statement @list{as @es[(⇀ (signal S p) (ρ (mtθ+S S unknown) WAIT p))], show that
                            
                            @es[(≃ (compile (signal S p)) (compile (ρ (mtθ+S S unknown) WAIT p)))]}]{
 TODO draw graphs.
}

@proof[#:label "emit"
       #:title "emit is sound"
       #:statement @list{as
        @es[(⇀ (ρ θ GO (in-hole E (emit S))) (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S present))) GO (in-hole E nothing)))]

        when @es[(θ-ref-S-∈ θ S (L2set present unknown))], show that
        
        @es[(≃ (compile (ρ θ GO (in-hole E (emit S)))) (compile (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S present))) GO (in-hole E nothing))))]}]{
 @cases[#:of E
        #:language esterel-eval
        #:induction
        @#:case[hole]{
          TODO draw picture}
        @#:case[(in-hole E1 E)]{ Note that the right hand
          side of the reduction forces @es[(compile (of θ S))] to
          compile as @es[(compile present)] and it replaces
          @es[(compile (emit S))] a circuit that sets
          @es[(= (of (compile (emit S)) S_o) 0)]. Nothing else is
          changed. By @proof-ref["S-output-irrelevant"] any @es[S_o]
          is only read by its corresponding binder, which in this case
          is @es[θ] by @proof-ref["S-maintained-across-E"]. Finally
          we know that the @es[(= (of (compile (emit S)) S_o) (of (compile p) GO))]
          by @proof-ref["GO-maintained-across-E"]. Therefore we change the value
          of no wires, so the circuits are the same.

          TODO constructivity of other s' wires?
          TODO discuss value on wire given by θ
          }]
}

@proof[#:label "is-present"
       #:title "is-present is sound"
       #:statement
       @list{as @es[(⇀ (ρ θ A (in-hole E (present S p q))) (ρ θ A (in-hole E p)))]

        when @es[(θ-ref-S θ S present)], show that
        @es[(≃ (compile (ρ θ A (in-hole E (present S p q)))) (compile (ρ θ A (in-hole E p))))]}]{
 As @es[(compile θ)] will force the @es[S] wire to be @es[1],
 by @proof-ref["S-is-consistent-across-E"] we know that
 @es[(= (of (compile (present S p q)) S) 1)]. Thus it
 suffices to show that
 @es[(≃ (compile (present S p q)) (compile p))] under this
 condition. This proof is given in the [is-present] notebook.
}

@proof[#:label "is-absent"
       #:title "is-absent is sound"
       #:statement
       @list{as @es[(⇀ (ρ θ A (in-hole E (present S p q))) (ρ θ A (in-hole E q)))]

        when @es[(θ-ref-S θ S unknown)] and @es[(L¬∈ S (->S (Can-θ (ρ θ A (in-hole E (present S p q))) ·)))], show that

        @es[(≃ (compile (ρ θ A (in-hole E (present S p q)))) (compile (ρ θ A (in-hole E q))))]}]{

 Let @es[p_outer] be @es[(ρ θ A (in-hole E (present S p q)))], the left hand side of the reduction.
 This can be proved by the following steps:
 
 @itemlist[
 #:style 'ordered
 @item{By @proof-ref["context-safety"]
   @es[(= (of (compile p_outer) SEL) 1)] implies
   @es[(= (of (compile p_outer) GO) 0)]}
 @item{By @proof-ref["S-maintains-across-E"] and
   @proof-ref["GO-maintains-across-E"] we know that
   @es[(= (of (compile p_outer) S) (of (compile (present S p q)) S))]
   and
   
   @es[(= (of (compile p_outer) GO) (of (compile (present S p q)) GO))]
  }
 @item{By @es["Can-S-is-sound"], we know that
   @es[(= (of (compile p_outer) SEL) 0)] implies @es[(= (of (compile p_outer) S) 0)].}
 @item{by 2 & 3, @es[(= (of (compile p_outer) SEL) 0)] implies
   @es[(= (of (compile (present S p q) S)) 0)].}
 @item{By @proof-ref["sel-def"],
   @es[(= (of (compile p_outer) SEL) (or (of (compile p) SEL) (of (compile q) SEL) others ...))]}
 @item{By 4 & 5,
   @es[(= (or (of (compile p) SEL) (of (compile q) SEL) others ...) (of (compile (present S p q)) SEL))]}
 @item{By 1, 2, & 5,
   @es[(= (or (of (compile p) SEL) (of (compile q) SEL) others ...) 1)]
   implies
   @es[(= (of (compile (present S p q)) SEL) 0)]}
 @item{Under 6, 7, 8, and @proof-ref["activation-condition"]
   we can show that @es[(≃ (compile (present S p q)) (compile q))].
   This is done in the [is-absent] notebook.}
 ]
                                                                                                 

}

@proof[#:label "sel-later"
       #:title "Selection Laster"
       #:statement @list{for any term @es[p],
        if @es[(= (of (compile p) GO) 0)] in every instant then
        @es[(= (of (compile p) SEL) 0)]}]{
 TODO
}

@proof[#:label "activation-condition"
       #:title "Activation Condition"
       #:statement @list{for any term @es[p],
        if @es[(= (or (of (compile p) GO) (and (of (compile p) SEL) (of (compile p) RES))) 0)]
        then all output @es[Kn] and all signals in the output environment @es[θ_o] are @es[0].}]{
 TODO
}