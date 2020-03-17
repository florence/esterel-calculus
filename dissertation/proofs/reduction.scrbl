#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          (except-in "../lib/proof-extras.rkt"  FV FV/e)
          redex/reduction-semantics
          (except-in esterel-calculus/redex/test/binding closed)
          (except-in scribble-abbrevs/latex definition))


@title[#:style paper-title-style #:tag "proof:reduction"]{Reduction Relation Properties}

This section contains lemmas and proofs that justify that
the reduction relation @es/unchecked[⇀] is sound with
respect to the compilation function.

@proof[#:label "par-swap"
       #:title "par-swap is sound"
       #:statement
       @list{As @es[(⇀ (par p-pure q-pure) (par q-pure p-pure))], show that @es[(≃^circuit (compile (par p-pure q-pure)) (compile (par q-pure p-pure)))]}]{
 This can be seen trivally, as the graphs of @es[(compile (par p-pure q-pure))]
 and @es[(compile (par q-pure p-pure))] are symmetric.
}

@proof[#:label "par-nothing"
       #:title "par-nothing is sound"
       #:statement
       @list{as @es[(⇀ (par nothing done) done)], show that @es[(≃^circuit (compile (par nothing done)) (compile done))]}]{
 This proof is given in the notebook [par-done], which actually shows the more general
 
 @es[(≃^circuit (compile (par nothing p-pure)) (compile p-pure))].
}

@proof[#:label "trap"
       #:title "trap is sound"
       #:statement
       @list{For all @es[stopped], as @es[(⇀ (trap stopped) (harp stopped))], it must be that
        @es[(≃^circuit (compile (trap stopped)) (compile (harp stopped)))]}]{
 @cases[#:of stopped
        #:language esterel/typeset
        @#:case[nothing]{
          @check[(assert-same
                  (compile-esterel (term (trap nothing)))
                  (compile-esterel (term (harp nothing))))].}
        @#:case[(exit 0)]{
          @check[(assert-same
                  (compile-esterel (term (trap (exit 0))))
                  (compile-esterel (term (harp (exit 0)))))].
         }
        @#:case[(exit n)]{
          Where @es[(> n 0)].

          In this case, @es[(= (harp (exit n)) (exit (sub1 n)))].

          If we draw the circuit for @es[(compile (exit n))] and
          @es[(compile (exit (sub1 n)))], we see that they give us the
          same graph. }]}

@proof[#:label "suspend"
       #:title "suspend is sound"
       #:statement
       @list{as @es[(⇀ (suspend done S) done)], show that
        @es[(≃^circuit (compile (suspend done S)) (compile done))]}]{
 This is proved in the [suspend] notebook.
}

@proof[#:label "seq-done"
       #:title "seq-done is sound"
       #:statement
       @list{as @es[(⇀ (seq nothing q-pure) q-pure)], show that
        @es[(≃^circuit (compile (seq nothing q-pure)) (compile q-pure))]}]{
 @es[(compile (seq nothing q-pure))] just connections
 the @es[GO] wire to @es[(of (compile q-pure) GO)],
 which is exactly @es[(compile q-pure)]. Thus the
 two circuits are identical.
}

@proof[#:label "par2-exit"
       #:title "par2-exit is sound"
       #:statement
       @list{as @es[(⇀ (par (exit n_1) (exit n_2)) (exit (max-mf n_1 n_2)))], show that
                
        @es[(≃^circuit (compile (par (exit n_1) (exit n_2))) (compile (exit (max-mf n_1 n_2))))]}]{
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
        @es[(≃^circuit (compile (par (exit n) paused)) (compile (exit n)))]}]{
 The proof of this is given in the [par1-exit] notebook.
}

@proof[#:label "seq-exit"
       #:title "seq-exit is sound"
       #:statement @list{as @es[(⇀ (seq (exit n) q-pure) (exit n))],
        if @es[(= (of (compile (seq (exit n) q-pure)) SEL) 0)] then
        @es[(≃^circuit (compile (seq (exit n) q-pure)) (compile (exit n)))]}]{
 By @es[(≃ (of (compile (seq (exit n) q-pure)) SEL) 0)], it must be that
 @es[(≃ (of (compile q-pure) SEL) 0)]. Thus by @proof-ref["activation-condition"]
 all output wires of @es[(compile q-pure)] are @es[0].
 Thus the only wire which can be true is @es[K2+n], which in this case will
 be equal to @es[(of (compile (exit n)) K2+n)]. In addition by @proof-ref["activation-constructiveness"]
 @es[(compile q-pure)] never exhibits non-constructive behavior, thus this circuit is always constructive.
 Thus the two circuits are equal.
}

@proof[#:label "signal"
       #:title "signal is sound"
       #:statement @list{as @es[(⇀ (signal S p-pure) (ρ (mtθ+S S unknown) WAIT p-pure))], show that
                            
        @es[(≃^circuit (compile (signal S p-pure)) (compile (ρ (mtθ+S S unknown) WAIT p-pure)))]}]{
 @es[(compile (signal S p-pure))] connects the input and output @es[S] wires to each other,
 and passes @es[GO] along unchanged. @es[(compile (ρ (mtθ+S S unknown) WAIT p-pure))] does the
 same, therefore the two circuits are identical.
}

@proof[#:label "emit"
       #:title "Emit is sound"
       #:statement @list{For all @es[(= r-pure (ρ θr GO (in-hole E-pure (emit S))))], as@(linebreak)
        @es[(⇀ (ρ θr GO (in-hole E-pure (emit S))) (ρ (parens (<- θr (mtθ+S S present))) GO (in-hole E-pure nothing)))]
        it must be that@(linebreak)
        @es[(≃^circuit (compile (ρ θr GO (in-hole E-pure (emit S)))) (compile (ρ (parens (<- θr (mtθ+S S present))) GO (in-hole E-pure nothing))))]}]{
 @cases[#:of E-pure
        #:language esterel/typeset
        #:induction
        @#:case[hole]{This follows trivially, as an empty context connects
         @es[GO] directly so the signal, which is forced to be @es[1] by
         our environment.}
        @#:case[(in-hole E1-pure E-pure_i)]{ Note that the right hand
          side of the reduction forces @es[(compile (θ-get-S θr S))] to
          compile as @es[(compile present)] and it replaces
          @es[(compile (emit S))] a circuit that sets
          @es[(= (of (compile (emit S)) S_o) 0)]. Nothing else is
          changed. By @proof-ref["S-output-irrelevant"] any @es[S_o]
          is only read by its corresponding binder, which in this case
          is @es[θ] by @proof-ref["S-maintains-across-E"]. Finally
          we know that the @es[(≃ (of (compile (emit S)) S_o) (of (compile p-pure) GO))]
          by @proof-ref["GO-maintains-across-E"]. Therefore we change the value
          of no wires, so the circuits are the same.

          TODO constructivity of other s' wires?
          TODO discuss value on wire given by θ
          }]
}

@proof[#:label "is-present"
       #:title "is-present is sound"
       #:statement
       @list{as @es[(⇀ (ρ θ A (in-hole E-pure (present S p-pure q-pure))) (ρ θ A (in-hole E-pure p-pure)))]
        if @es[(≃ (of (compile (ρ θ A (in-hole E-pure (present S p-pure q-pure)))) SEL) 0)]
        and @es[(θ-ref-S θ S present)], show that
        @es[(≃^circuit (compile (ρ θ A (in-hole E-pure (present S p-pure q-pure)))) (compile (ρ θ A (in-hole E-pure p-pure))))]}]{
 As @es[(compile θ)] will force the @es[Si] wire to be @es[1],
 by @proof-ref["S-maintains-across-E"] we know that
 
 @es[(≃ (of (compile (present S p-pure q-pure)) Si) 1)]. Thus it
 suffices to show that
 @es[(≃^circuit (compile (present S p-pure q-pure)) (compile p-pure))] under this
 condition. This proof is given in the [is-present] notebook.
}

@proof[#:label "is-absent"
       #:title "is-absent is sound"
       #:statement
       @list{
        For all @es[(= r-pure (ρ θ A (in-hole E-pure (present S p-pure q-pure))))],@(linebreak)
        as @es[(⇀ (ρ θ A (in-hole E-pure (present S p-pure q-pure))) (ρ θ A (in-hole E-pure q-pure)))]@(linebreak)
        when @es[(θ-ref-S θ S unknown)]@(linebreak)
        and @es[(L¬∈ S (->S (Can-θ (ρ θ A (in-hole E-pure (present S p-pure q-pure))) ·)))],@(linebreak)
        if @es[(≃ (of (compile (ρ θ A (in-hole E-pure (present S p-pure q-pure)))) SEL) 0)],@(linebreak)
        then@(linebreak)
        @es[(≃^circuit (compile (ρ θ A (in-hole E-pure (present S p-pure q-pure)))) (compile (ρ θ A (in-hole E-pure q-pure))))]}]{

 Let @es[p_outer] be @es[(ρ θ A (in-hole E-pure (present S p-pure q-pure)))], the left hand side of the reduction.
 This can be proved by the following steps:

 @sequenced{
  @#:step[maintain]{By @proof-ref["S-maintains-across-E"] and
   @proof-ref["GO-maintains-across-E"] we know that
   @es[(≃ (of (compile p-pure_outer) Si) (of (compile (present S p-pure q-pure)) Si))]
   and
   @es[(≃ (of (compile p-pure_outer) GO) (of (compile (present S p-pure q-pure)) GO))]
  }
  @#:step[sound]{By @proof-ref["Can-S-is-sound"] and our premise that @es[(≃ (of (compile p-pure_outer) SEL) 0)],
   we know that @es[(≃ (of (compile p-pure_outer) So) 0)].}
  @#:step[eq]{By the definition of @es[compile] on @es[ρ], we know
   that @es[(≃ (of (compile (present S p-pure q-pure)) Si) (of (compile (present S p-pure q-pure)) So))]}
  @#:step[is-zero]{By @maintain, @sound & @eq, we know that @es[(≃ (of (compile (present S p-pure q-pure)) Si) 0)].}
  @#:step[def]{By @proof-ref["sel-def"],
   @es[(≃ (of (compile p-pure_outer) SEL) (or (of (compile p-pure) SEL) (of (compile q-pure) SEL) w_others ...))]}
  @#:step[imp]{By @def and our premise that @es[(≃ (of (compile p-pure_outer) SEL) 0)], we know that
   @es[(≃ (of (compile (present S p-pure q-pure)) SEL) 0)]}
  @#:step[_]{Under @imp and @proof-ref["activation-condition"]
   we can show that @es[(≃^circuit (compile (present S p-pure q-pure)) (compile q-pure))].
   This is done in the [is-absent] notebook.}}
                                                                                                 

}


@proof[#:label "merge"
       #:title "merge is sound"
       #:statement
       @list{as @es[(⇀ (ρ θr_1 A_1 (in-hole E-pure (ρ θr_2 A_2 p-pure))) (ρ (<- θr_1 θr_2) A_1 (in-hole E-pure p-pure)))],]
                when @es[(A->= A_1 A_2)], show that
        if @es[(CB (ρ θr_1 A_1 (in-hole E-pure (ρ θr_2 A_2 p-pure))))] then
                
        @es[(≃^circuit (compile (ρ θr_1 A_1 (in-hole E-pure (ρ θr_2 A_2 p-pure)))) (compile (ρ (<- θr_1 θr_2) A_1 (in-hole E-pure p-pure))))]}]{
 This is a direct consequence of @proof-ref["can-lift"] and @proof-ref["immediate-merge"].
}

@proof[#:label "immediate-merge"
       #:title "Merge Adjacent Environments"
       #:statement
       @list{For all @es[p-pure], @es[θr_1], @es[θr_2], @es[A_1] and @es[A_2],
        if @es[(A->= A_1 A_2)] then
        @es[(≃^circuit (compile (ρ θr_1 A_1 (ρ θr_2 A_2 p-pure))) (compile (ρ (<- θr_1 θr_2) A_1 p-pure)))]}]{

 Sketch: The compilation of @es[ρ] only changes the outputs of
 its inner circuit in that it closes some of the signal
 wires, and that it only changes input values of some signals
 and the GO wire. Thus, we can argue that that equivalence
 base on three facts. First, that @es[(<- θr_1 θr_2)] closes
 the same signals as the two nested environments. Second that
 these signals are closed in the same way: that is they input
 part of the signal will receive the same value. Third, that
 the value of the @es[GO] wire does not change. In a sense, this means
 that the only effect of this rule is to move wires from one "spot" in the circuit
 to another, without changing their connections.
 
 @sequenced{

  @#:step[<--closing]{
                      
   By the definition of @es/unchecked[<-],
   @es[(= (Ldom (<- θr_1 θr_2)) (LU (Ldom θr_1) (Ldom θr_2)))].

  }
   
  @#:step[ρ-closed]{
                    
   by the definition of @es/unchecked[(compile dot)],
   compiling a @es[ρ] closes only the wires in its @es[θr]'s
   domain, we can see that the same wires are closed both
   expressions.

  }

  @#:step[totally-closed]{
  By @<--closing and @ρ-closed,
  @es[(= (inputs (compile (ρ θr_1 A_1 (ρ θr_2 A_2 p-pure)))) (inputs (compile (ρ (<- θr_1 θr_2) A_1 p-pure))))]
  and@(linebreak)
  @es[(= (outputs (compile (ρ θr_1 A_1 (ρ θr_2 A_2 p-pure)))) (outputs (compile (ρ (<- θr_1 θr_2) A_1 p-pure))))]}

  @#:step[clomp-block]{

   The compilation of @es[(ρ θr_2 A_2 hole)] will
   prevent the compilation of @es[(ρ θr_1 A_1 hole)] from
   modifying any signals in the domain of @es[θ_2], meaning
   those signals will get values as specified by the
   compilation of @es[θr_2]. In addition @es[(<- θr_1 θr_2)] keep
   the value of any signal in @es[θr_2], therefore those signals
   will compile the same way. Thus the value of no input signal
   is changed.

  }

  @#:step[inputs/outputs-same]{
   By @totally-closed and @clomp-block, we know that
   for all @es[(L∈ S (inputs (compile p-pure)))],
   in @es[(compile (ρ θr_1 A_1 (ρ θr_2 A_2 p-pure)))]
   @es[(binds (compile p-pure) (<- θr_1 θr_2))], and in
   @es[(compile (ρ (<- θr_1 θr_2) A_1 p-pure))],
   @es[(binds (compile p-pure) (<- θr_1 θr_2))].
  }

  @#:step[lt-block]{

   As @es[(A->= A_1 A_2)] we know that either both
   are @es[GO], both are @es[WAIT], or @es[(= A_1 GO)] and
   @es[(= A_2 WAIT)]. In each case we can see that the actual
   value on @es[(of (compile p-pure) GO)] remains the same. That is, in both
   cases, @es[(binds (compile p-pure) A_1)].

  }
  @#:step[other-control]{The compilation of @es[ρ] does not change
   the other control inputs and outputs of @es[(compile p-pure)].}
  @#:step[final]{By @inputs/outputs-same, @lt-block, and @other-control, the inputs
   and outputs of @es[(compile p-pure)] are not changed, thus
   the behavior of the circuit is not changed.}

 }



                          

}

@proof[#:label "can-lift"
       #:title "Can Lift Environments"
       #:statement
       @list{For all @es[p], @es[E], @es[θ], and @es[A],
        if either @es[(= A WAIT)] or
        @es[(= A GO)]
        and
        @es[(= (of (compile (in-hole E-pure (ρ θ A p-pure))) GO) 1)],
        and @es[(CB (in-hole E-pure (ρ θ A p-pure)))], then
        
        @es[(≃^circuit (compile (in-hole E-pure (ρ θ A p-pure))) (compile (ρ θ A (in-hole E-pure p-pure))))]}]{
 TODO more formal (ug).
 This proof proceeds in two parts. First, by
 @proof-ref["GO-maintains-across-E"], we know that lifting
 @es[A] across won't change the value of the @es[GO] wire of
 any subcircuit because either @es[(= A WAIT)], in which case
 its compilation does not change the @es[GO] wire at all, or
 @es[(= A GO)], in which case it will force the @es[GO] wire
 to be @es[1]. But in this second case our hypothesis states
 that the @es[GO] wire was already @es[1], so nothing has changed.

 Second, by @es[(CB (in-hole E-pure (ρ θ A p-pure)))] we know that the
 free variables of @es[E] and the bound variables of
 @es[(ρ θ A p-pure)] are distinct. Thus lifting @es[θ] will not
 capture any new variables, therefore by
 @proof-ref["FV-equals-IO"], the compilation of @es[θ] will
 connect the exact same wires resulting in a circuit that is
 structurally the same after the lift. Thus lifting the
 signal environment also changes nothing.

}

