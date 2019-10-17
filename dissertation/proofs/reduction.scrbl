#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          (except-in esterel-calculus/redex/model/shared FV FV/e)
          esterel-calculus/redex/test/binding
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (except-in scribble-abbrevs/latex definition))


@title[#:style paper-title-style]{Reduction Relation Properties}

This section contains lemmas and proofs that justify that
the reduction relation @es/unchecked[⇀] is sound with
respect to the compilation function.

@proof[#:label "par-swap"
       #:title "par-swap is sound"
       #:interpretation @list{Justify that @rule["par-swap"] is an η-rule}
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
        @es[(≃ (compile (trap stopped)) (compile (harp stopped)))]}
       #:interpretation @list{Justify that @rule["trap"] is an η-rule}]{
 @cases[#:of stopped
        #:language esterel/typeset
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
        @es[(≃ (compile (seq nothing q)) (compile q))]}
       #:interpretation @list{Justify that @rule["seq-done"] is an η-rule}]{
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
              and therefore @es/unchecked[(= lem-n (or lem 0 ...))]. The
              same will hold for @es[rem-n]. We now can see
              that we have a synchronizer of the same shape as
              in the previous subcase. Thus the remainder of this
              proof proceeds in the same way.}]}
 @#:case[@es[(> n_1 n_2)]]{
   @cases[#:of nat_2
          #:induction
          #:checks 20
          @#:case[0]{ Note that all @es[ln] up to
              @es/unchecked[l2+n_1] must be @es[0]. Therefore all @es[kn] up to that
              point must be @es[0]. The notebook [par-2exit] shows
              that the remainder of the synchronizer behaves as @es[(compile (exit n_1))].
             }
          @#:case[(Suc mat)]{ All @es[kn] up to @es/unchecked[kn_2]
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
 be equal to @es[(of (compile (exit n)) K2+n)]. In addition by @proof-ref["activation-constructiveness"]
 @es[(compile q)] never exhibits non-constructive behavior, thus this circuit is always constructive.
 Thus the two circuits are equal.
}

@proof[#:label "signal"
       #:title "signal is sound"
       #:interpretation @list{Justify that @rule["signal"] is an η-rule}
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
        #:language esterel/typeset
        #:induction
        @#:case[hole]{
          TODO draw picture}
        @#:case[(in-hole E1 E_i)]{ Note that the right hand
          side of the reduction forces @es[(compile (θ-get-S θ S))] to
          compile as @es[(compile present)] and it replaces
          @es[(compile (emit S))] a circuit that sets
          @es[(= (of (compile (emit S)) S_o) 0)]. Nothing else is
          changed. By @proof-ref["S-output-irrelevant"] any @es[S_o]
          is only read by its corresponding binder, which in this case
          is @es[θ] by @proof-ref["S-maintains-across-E"]. Finally
          we know that the @es[(= (of (compile (emit S)) S_o) (of (compile p) GO))]
          by @proof-ref["GO-maintains-across-E"]. Therefore we change the value
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
 by @proof-ref["S-maintains-across-E"] we know that
 
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
 @item{By @proof-ref["Can-S-is-sound"], we know that
   @es[(= (of (compile p_outer) SEL) 0)] implies @es[(= (of (compile p_outer) S) 0)].}
 @item{by 2 & 3, @es[(= (of (compile p_outer) SEL) 0)] implies
   @es[(= (of (compile (present S p q)) S) 0)].}
 @item{By @proof-ref["sel-def"],
   @es[(= (of (compile p_outer) SEL) (or (of (compile p) SEL) (of (compile q) SEL) w_others ...))]}
 @item{By 4 & 5,
   @es[(= (or (of (compile p) SEL) (of (compile q) SEL) w_others ...) (of (compile (present S p q)) SEL))]}
 @item{By 1, 2, & 5,
   @es[(= (or (of (compile p) SEL) (of (compile q) SEL) w_others ...) 1)]
   implies
   @es[(= (of (compile (present S p q)) SEL) 0)]}
 @item{Under 6, 7, 8, and @proof-ref["activation-condition"]
   we can show that @es[(≃ (compile (present S p q)) (compile q))].
   This is done in the [is-absent] notebook.}
 ]
                                                                                                 

}


@proof[#:label "merge"
       #:title "merge is sound"
       #:statement
       @list{as @es[(⇀ (ρ θ_1 A_1 (in-hole E (ρ θ_2 A_2 p))) (ρ (<- θ_1 θ_2) A_1 (in-hole E p)))],]
                when @es[(A->= A_1 A_2)], show that
        if @es[(CB (ρ θ_1 A_1 (in-hole E (ρ θ_2 A_2 p))))] then
                
        @es[(≃ (compile (ρ θ_1 A_1 (in-hole E (ρ θ_2 A_2 p)))) (compile (ρ (<- θ_1 θ_2) A_1 (in-hole E p))))]}]{
 This is a direct consequence of @proof-ref["can-lift"] and @proof-ref["immediate-merge"]. TODO explain more.
}

@proof[#:label "immediate-merge"
       #:title "Merge Adjacent Environments"
       #:statement
       @list{For all @es[p], @es[θ_1], @es[θ_2], @es[A_1] and @es[A_2],
        if @es[(A->= A_1 A_2)] then
        @es[(≃ (compile (ρ θ_1 A_1 (ρ θ_2 A_2 p))) (compile (ρ (<- θ_1 θ_2) A_1 p)))]}]{
 Note that compilation of @es[ρ] only changes the outputs of its inner circuit in
 that it closes some of the signal wires, and that it only changes input values of some signals
 and the GO wire. Thus, we can argue that that equivalence base on three
 facts. First, that @es[(<- θ_1 θ_2)] closes the same signals as the two nested environments.
 Second that these signals are closed in the same way: that is they input part of the signal will receive
 the same value. Third, that the value of the @es[GO] wire does not change.

 First, by the definition of @es/unchecked[<-], @es[(= (Ldom (<- θ_1 θ_2)) (= (LU (Ldom θ_1) (Ldom θ_2))))].
 As the compilation of @es[ρ] closes only the wires in its @es[θ]'s domain, we can see that
 the same wires are closed both expressions.

 Second, the compilation of @es[(ρ θ_2 A_2 hole)] will prevent the compilation of @es[(ρ θ_1 A_1 hole)]
 form modifying any signals in the domain of @es[θ_2], meaning those signals will get values
 as specified by the compilation of @es[θ_2]. In addition @es[(<- θ_1 θ_2)] keep the value of any signal
 in @es[θ_2], therefore those signals will compile the same way. Thus the value of no input signal is changed.

                          
 Finally, as @es[(A->= A_1 A_2)] we know that either
 both are @es[GO], both are @es[WAIT], or @es[(= A_1 GO)] and @es[(= A_2 WAIT)]. In each case we
 can see that the actual value on @es[(of (compile p) GO)] remains the same.
}

@proof[#:label "can-lift"
       #:title "Can Lift Environments"
       #:statement
       @list{For all @es[p], @es[E], @es[θ], and @es[A],
        if either @es[(= A WAIT)] or
        @es[(= A GO)]
        and
        @es[(= (of (compile (in-hole E (ρ θ A p))) GO) 1)],
        and @es[(CB (in-hole E (ρ θ A p)))], then
        
        @es[(≃ (compile (in-hole E (ρ θ A p))) (compile (ρ θ A (in-hole E p))))]}]{
 This proof proceeds in two parts. First, by
 @proof-ref["GO-maintains-across-E"], we know that lifting
 @es[A] across won't change the value of the @es[GO] wire of
 any subcircuit because either @es[(= A WAIT)], in which case
 its compilation does not change the @es[GO] wire at all, or
 @es[(= A GO)], in which case it will force the @es[GO] wire
 to be @es[1]. But in this second case our hypothesis states
 that the @es[GO] wire was already @es[1], so nothing has changed.

 Second, by @es[(CB (in-hole E (ρ θ A p)))] we know that the
 free variables of @es[E] and the bound variables of
 @es[(ρ θ A p)] are distinct. Thus lifting @es[θ] will not
 capture any new variables, therefore by
 @proof-ref["FV-equals-IO"], the compilation of @es[θ] will
 connect the exact same wires resulting in a circuit that is
 structurally the same after the lift. Thus lifting the
 signal environment also changes nothing.

}

