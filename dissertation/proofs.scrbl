#lang scribble/base

@(require "lib/redex-rewrite.rkt"
          "lib/util.rkt"
          "lib/proofs.rkt"
          "lib/proof-extras.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style]{Proofs}

@proof[#:label "FullyAbstract"
       #:title "Fully Abstract Compilation"
       #:statement
       @list{For all @es[p] and @es[q], @es[(≡ p q)] implies that
        @es[(≃ (compile p) (compile q))]}
       #:interpretation "is it really?"
       #:type 'theorem]{
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
        #:language esterel/typeset
        @#:case["TODO"]{TODO}]
}

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

@(define emit-not-equal-case
   @cases[#:of/count @es[(L∈ S_2 (->S (Can p_i (<- θ (mtθ+S S_2 unknown)))))] 2
          #:language esterel/typeset
          @#:case[@es[(L∈ S_2 (->S (Can p_i (<- θ (mtθ+S S_2 unknown)))))]]{
           In this case
           @es[(= (->S (Can (signal S_2 p_i) θ)) (Lset-sub (->S (Can p_i (<- θ (mtθ+S S_2 unknown)))) (L1set S)))].
           As @es[(not-= S S_2)], from this we can conclude that
           @es[(L¬∈ S (->S (Can p_i (<- θ (mtθ+S S_2 unknown)))))]. In
           addition we can conclude that
           @es[(binds (compile p_i) (<- θ (mtθ+S S_2 unknown)))],
           as all the introduction of @es[(mtθ+S S_2 unknown)] does is link @es[S_2o] to @es[S_2i],
           which is exactly what the compilation of @es[(signal S_2 p_i)] does.
           As @es[(compile (signal S_2 p_i))] leaves @es[SEL] and all other outputs unchanged
           from @es[(compile p_i)], 
           we can use our Induction Hypothesis to conclude that
           @es[(= (of (compile p_i) S_o) 0)].
           Again, as  @es[(compile (signal S_2 p_i))] leaves all non-@es[S_2] outputs
           unchanged, we can conclude that 
           @es[(= (of (compile p_i) S_o) (of (compile (signal S_2 p_i)) S_o) 0)].}
          @#:case[@es[(L¬∈ S_2 (->S (Can p_i (<- θ (mtθ+S S_2 unknown)))))]]{
           In this case
           @es[(= (->S (Can (signal S_2 p_i) θ)) (Lset-sub (->S (Can p_i (<- θ (mtθ+S S_2 absent)))) (L1set S)))].
           The argument for this case follows exactly along the same
           lines as the previous case, but we must instead show that
           @es[(binds (compile p_i) (<- θ (mtθ+S S_2 absent)))] rather
           than @es[(binds (compile p_i) (<- θ (mtθ+S S_2 unknown)))].
           To show this we first argue that
           @es[(binds (compile p_i) (<- θ (mtθ+S S_2 unknown)))] still
           holds, as it replaces no restrictions on the value of
           @es[S_2]. From this we can apply induction using
           @es[(L¬∈ S_2 (->S (Can p_i (<- θ (mtθ+S S_2 unknown)))))] to
           argue that @es[(= (of (compile p_i) S_2) 0)]. Since this is
           the interpretation of @es[(mtθ+S S_2 absent)], we can safely
           conclude that
           @es[(binds (compile p_i) (<- θ (mtθ+S S_2 absent)))]. Thus
           we can apply the reasoning from the previous case to
           conclude that @es[(= (of (compile (signal S_2 p_i)) S_o) 0)].
           
           }])

@proof[#:label "Can-S-is-sound"
       #:title "Can S is sound"
       #:statement
       @list{For any term and environment @es[p] and @es[θ] and any signal @es[S], where @es[(binds (compile p) θ)],
        @es[(L¬∈ S (->S (Can p θ)))] implies that,
        
        @es[(=> (= (of (compile p) SEL) 0) (L∈ S (outputs (compile p))) (= (of (compile p) S_o) 0))]}

       #:interpretation
       @list{This theorem states that @es/unchecked[Can] accurately predicts when signal output wires
        will be set to @es[0].}]{
 @cases[#:of p-pure
        #:language esterel/typeset
        @#:case[nothing]{
          @es[(L¬∈ S (outputs (compile nothing)))], which violates our hypothesis.
         }
        @#:case[pause]{
          Same as previous case.
         }
        @#:case[(exit n)]{
          Same as previous case.
         }
        @#:case[(emit S_2)]{
          @cases[#:of/count @es[(= S S_2)] 2
                 #:language esterel/typeset
                 @#:case[@es[(= S S_2)]]{
                            In this case @es[(L∈ S (->S (Can p θ)))], which violates
                            our hypothesis.
                           }
                 @#:case[@es[(not-= S S_2)] ]{
                            In this case @es[(compile (emit S_2))]
                            does define an @es[S_2] wire, therefore
                            @es[(L¬∈ S (outputs (compile (emit S_2))))],
                            which violates our hypothesis.
                            }]
         }
        @#:case[(signal S_2 p_i)]{
          @cases[#:of/count @es[(= S S_2)] 2
                 @#:case[@es[(= S S_2)]]{
                            In this case the compilation of signal removes @es[S]
                            from the set of output signals, which means
                            @es[(L¬∈ S (outputs (compile p)))] which violates our hypothesis.
                           }
                 @#:case[@es[(not-= S S_2)]]{
                            In this case we can see that there are two cases for @es/unchecked[Can]:
                                                                                 
                            @emit-not-equal-case
                            }]
         }
        @#:case[(par p_i q_i)]{
                               
          In this case
          @es[(= (->S (Can (par p_i q_i) θ)) (LU (->S (Can p_i θ)) (->S (Can q_i θ))))].
          This we can conclude that @es[(L¬∈ S (->S (Can p_i θ)))] and
          @es[(L¬∈ S (->S (Can q_i θ)))]. We also know that
          @es[(= (of (compile (par p_i q_i)) SEL) (or (of (compile p_i) SEL) (of (compile q_i) SEL)))],
          which implies that @es[(= (of (compile p_i) SEL) 0)] and
          @es[(= (of (compile q_i) SEL) 0)].

          Therefore, by induction, we can conclude that
          @es[(=> (L∈ S_o (outputs (compile p_i))) (= (of (compile p_i) S_o) 0))]
          and

          @es[(=> (L∈ S_o (outputs (compile q_i))) (= (of (compile q_i) S_o) 0))].

          We also know that @es[(L∈ S_o (outputs (compile (par p_i q_i))))] means that
          @es[S_o] must be in at least one of the outputs of @es[(compile p_i)] and @es[(compile q_i)].
          @cases[#:of/count @list{@es[(L∈ S_o (outputs (compile p_i)))] and @es[(L∈ S_o (outputs (compile q_i)))]}
                 3
                 @#:case[@list{@es[(L∈ S_o (outputs (compile p_i)))] and @es[(L¬∈ S_o (outputs (compile q_i)))]}]{
                            In this case @es[(= (of (compile (par p_i q_i)) S_o) (or (of (compile p_i) S_o) 0) (of (compile p_i) S_o))]
                            which, as in this case we have @es[(L∈ S_o (outputs (compile p_i)))], lets us conclude
                            @es[(= (of (compile (par p_i q_i)) S_o) 0)]
                           }
                 @#:case[@list{@es[(L∈ S_o (outputs (compile p_i)))] and @es[(L¬∈ S_o (outputs (compile q_i)))]}]{
                            This case is analogous to the previous one.
                           }
                 @#:case[@list{@es[(L∈ S_o (outputs (compile p_i)))] and @es[(L∈ S_o (outputs (compile q_i)))]}]{
                            In this case we have @es[(= (of (compile (par p_i q_i)) S_o) (or (of (compile p_i) S_o) (of (compile q_i) S_o)))]
                            As in this case we know that @es[(L∈ S_o (outputs (compile p_i)))] and @es[(L∈ S_o (outputs (compile q_i)))]
                            we can conclude that @es[(= (of (compile (par p_i q_i)) S_o) (or 0 0) 0)]
                            }]
         }
        @#:case[(present S_2 p q)]{ We know that
          @es[(= (of (compile (present S_2 p_i q_i)) SEL) (or (of (compile p_i) SEL) (of (compile q_i) SEL)) 0)].
          Therefore @es[(= (of (compile p_i) SEL) 0)] and
          @es[(= (of (compile q_i) SEL) 0)]. We also know that
          @es[(= (of (compile (present S_2 p_i q_i)) S_o) (or (of (compile p_i) S_o) (of (compile q_i) S_o)))].
          @cases[#:of/count @es[(θ-get-S θ S_2)] 3
                 @#:case[@es[(= (θ-get-S θ S_2) present)]]{
                            In this case we know that
                            @es[(= (->S (Can (present S_2 p_i q_i) θ)) (->S (Can p_i θ)))].
                            In addition not that @es[(= (θ-get-S θ S_2) present)] means
                            that @es[(= (of (compile (present S_2 p_i q_i)) S_2i) 1)],
                            therefore
                            
                            @es[(= (of (compile q_i) GO) (and (of (compile (present S_2 p_i q_i)) GO) (not (of (compile (present S_2 p_i q_i)) S_2i))) 0)].
                            Therefore by @proof-ref["activation-condition"] we know that
                            @es[(=> (L∈ S (outputs (compile q_i))) (= (of (compile q_i) S_o) 0))].
                            @cases[#:of/count @es[(L∈ S (outputs (compile p_i)))] 2
                                   @#:case[@es[(L¬∈ S (outputs (compile p_i)))]]{
                                                                This implies that @es[(L∈ S (outputs (compile q_i)))] as we
                                                                know that
                                                                @es[(L∈ S (outputs (compile (present S_2 p_i q_i))))]. Thus
                                                                we know that @es[(= (of (compile q_i) S_o) 0)] This lets us
                                                                conclude that
                                                                @es[(= (of (compile (present S_2 p_i q_i)) S_o) (or 0 (of (compile q_i) S_o)) (or 0 0) 0)].}
                                   @#:case[@es[(L∈ S (outputs (compile p_i)))]]{
                                                                In this case we can invoke our induction hypothesis to show
                                                                that @es[(= (of (compile p_i) S_o) 0)]. Thus we can use a
                                                                similar chain of reasoning to the previous case to argue
                                                                that @es[(= (of (compile (present S_2 p_i q_i)) S_o) 0)].
                                                                }]}
                 @#:case[@es[(= (θ-get-S θ S_2) absent)]]{
                            This case is analogous to the previous one, that we are
                            looking at the else clause, and know that
                            @es[(= (of (compile (present S_2 p_i q_i)) S_2i) 0)],
                            suppressing the activation of @es[(compile p_i)].
                           }
                 @#:case[@es[(= (θ-get-S θ S_2) unknown)]]{
                            In this case we know that
                            @es[(= (->S (Can (present S_2 p_i q_i) θ)) (LU (->S (Can p_i θ)) (->S (Can q_i θ))))].
                            Thus we can conclude that @es[(L¬∈ S (->S (Can p_i θ)))] and @es[(L¬∈ S (->S (Can q_i θ)))].
                            As previously we know that @es[S_o] must be in the outputs of @es[(compile p_i)] or
                            @es[(compile q_i)]. Thus, by induction, we have that either
                            @es[(L¬∈ S_o (outputs (compile p_i)))] or @es[(= (of (compile p_i) S_o) 0)]
                            and that either @es[(L¬∈ S_o (outputs (compile q_i)))] or @es[(= (of (compile q_i) S_o) 0)].

                            From this and analogous reasoning to the previous two cases,
                            as @es[S_o] is either no in the outputs or @es[0]
                            in either subcircuit, we can conclude
                            that @es[(= (of (compile (present S_2 p_i q_i)) S_o) 0)].
                                     
                            }]
         }
        @#:case[(suspend p_i S_2)]{
          In this case we know that @es[(= (->S (Can (suspend p_i S_2) θ)) (->S (Can p_i θ)))].
          We also know that
          
          @es[(= (of (compile (suspend p_i S_2)) SEL) (of (compile p_i) SEL))].
          and as @es[(L∈ S (outputs (compile (suspend p_i S_2))))], @es[(L∈ S (outputs (compile p_i)))].
          Therefor by induction @es[(= (of (compile p_i) S_o) 0)]. Finally the compilation of @es[suspend] does
          not change output signals so we can conclude that @es[(= (of (compile (suspend p_i S_2)) S_o) 0)].
         }
        @#:case[(trap p_i)]{ 
          This case follows identically to the previous one, as the
          compilation of @es[trap] neither modifies @es[SEL] nor
          signals form its inner term.
         }
        @#:case[(seq p_i q_i)]{
          Note that @es[(= (of (compile (seq p_i q_i)) SEL) (or (of (compile p_i) SEL) (of (compile q_i) SEL)))].
          Therefore @es[(= (of (compile p_i) SEL) (of (compile q_i) SEL) 0)].
          In addition as before @es[S_o] must be in the outputs of either @es[(compile p_i)]
          or @es[(compile q_i)].
          From the definition of @es/unchecked[Can] we have two cases:
          @cases[#:of/count @es[(L∈ 0 (->K (Can p_i θ)))] 2
                 @#:case[@es[(L¬∈ 0 (->K (Can p_i θ)))]]{
                            In this case we have @es[(= (->S (Can (seq p_i q_i) θ)) (->S (Can p_i θ)))].
                            By induction we can conclude that either @es[(L¬∈ S_o (outputs (compile p_i)))] or @es[(= (of (compile p_i) S_o) 0)].
                            In addition by @proof-ref["Can-K-is-sound"] we can conclude that either
                            @es[(L¬∈ K0 (outputs (compile p_i)))] or @es[(= (of (compile p_i) K0) 0)]. Either
                            way this tells us that @es[(= (of (compile q_i) GO) 0)]. Thus, by @proof-ref["activation-condition"],
                            we can conclude that either @es[(L¬∈ S_o (outputs (compile q_i)))] or @es[(= (of (compile q_i) S_o) 0)].
                            As @es[S_o] is either no in the outputs or @es[0] in either subcircuit, we can conclude
                            that @es[(= (of (compile (seq p_i q_i)) S_o) 0)].
                           }
                 @#:case[@es[(L∈ 0 (->K (Can p_i θ)))]]{
                            In this case we have @es[(= (->S (Can (seq p_i q_i) θ)) (LU (->S (Can p_i θ)) (->S (Can q_i θ))))].
                            From this we know that

                            @es[(L¬∈ S (->S (Can p_i θ)))] and @es[(L¬∈ S (->S (Can q_i θ)))].
                            Thus, by induction we have that either @es[(L¬∈ S_o (outputs (compile p_i)))] or @es[(= (of (compile p_i) S_o) 0)]
                            and that either @es[(L¬∈ S_o (outputs (compile q_i)))] or @es[(= (of (compile q_i) S_o) 0)].
                            As @es[S_o] is either no in the outputs or @es[0] in either subcircuit, we can conclude
                            that @es[(= (of (compile (seq p_i q_i)) S_o) 0)].}]
         }
        @#:case[(ρ θ A p_i)]{This case is shown by @proof-ref["Can-rho-S-is-sound"]}
        @#:case[(loop p_i)]{TODO}
        @#:case[(loop^stop p_i q_i)]{TODO}]
}


@proof[#:label "Can-K-is-sound"
       #:title "Can K is sound"
       #:statement
       @list{For any term and environment @es[p] and @es[θ] and any return code @es[κ], where @es[(binds (compile p) θ)],
        @es[(L¬∈ κ (->K (Can p θ)))] implies that,
        
        @es[(=> (= (of (compile p) SEL) 0) (L∈ Kκ (outputs (compile p))) (= (of (compile p) Kκ) 0))]}
       #:interpretation
       @list{This theorem states that @es/unchecked[Can] accurately predicts when control wires
        will be set to @es[0].}]{
 TODO
}

@proof[#:label "Can-rho-S-is-sound"
       #:title "Can rho S is sound"
       #:statement
       @list{For any term and environment @es[p] and @es[θ] and @es[A], and signal @es[S]
        @es[(L¬∈ S (->S (Can-θ (ρ θ A p) ·)))] implies that,
        
        @es[(=> (= (of (compile (ρ θ A p)) SEL) 0) (L∈ S_o (outputs (compile (ρ θ A p)))) (= (of (compile (ρ θ A p)) S_o) 0))]}
       #:interpretation
       @list{This theorem states that @es/unchecked[Can-θ] accurately predicts when signal output wires
        will be set to @es[0].}]{
 @es/unchecked[Can-θ] is essentially repeated applications of
 the @es[signal] case in @es/unchecked[Can]. This holds by the same line of argument there used in that case
 of @proof-ref["Can-S-is-sound"].
}


@proof[#:label "Can-rho-K-is-sound"
       #:title "Can rho K is sound"
       #:statement
       @list{For any term and environment @es[p] and @es[θ] and @es[A], and return code @es[κ]
        @es[(L¬∈ κ (->K (Can-θ (ρ θ A p) ·)))] implies that,
        
        @es[(=> (= (of (compile (ρ θ A p)) SEL) 0) (L∈ Kκ (outputs (compile (ρ θ A p)))) (= (of (compile (ρ θ A p)) Kκ) 0))]}
       #:interpretation
       @list{This theorem states that @es/unchecked[Can-θ] accurately predicts when control wires
        will be set to @es[0].}]{
 @es/unchecked[Can-θ] is essentially repeated applications of
 the @es[signal] case in @es/unchecked[Can]. This holds by the same line of argument there used in that case
 of @proof-ref["Can-K-is-sound"].
}

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