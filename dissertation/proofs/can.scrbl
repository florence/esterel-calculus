#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style]{Can Properties}

This section contains lemmas and proofs about @es/unchecked[Can] and its
relation to the circuit translation. The core theorem here is @proof-ref["Can-S-is-sound"].

@(define emit-not-equal-case
   @cases[#:language esterel/typeset
          #:of/count (L∈ S_2 (->S (Can p-pure_i (<- θ (mtθ+S S_2 unknown))))) 2
          #:simple-cases
          @#:case[(L∈ S_2 (->S (Can p-pure_i (<- θ (mtθ+S S_2 unknown)))))]{

           @sequenced{
            @#:step[eq]{
             By the definition of @es[Can],
             @es[(= (->S (Can (signal S_2 p-pure_i) θ)) (Lset-sub (->S (Can p-pure_i (<- θ (mtθ+S S_2 unknown)))) (L1set S)))].}
            @#:step[not-in]{By @es[(not-= S S_2)], @eq, and the
             premise that @es[(L¬∈ S (->S (Can p-pure θ)))], we may conclude
             that @es[(L¬∈ S (->S (Can p-pure_i (<- θ (mtθ+S S_2 unknown)))))].}
            @#:step[binds]{By the definition of @es[compile], the compilation of @es[signal]
             will link @es[So_2] to @es[Si_2]. Therefore we can conclude that
             @es[(binds (compile p-pure_i) (<- θ (mtθ+S S_2 unknown)))], as the binding of
             the other signals does not change, and @es[(binds p-pure (mtθ+S S_2 unknown))] will
             always hold.}
            @#:step[zero]{As the compilation of @es[signal] does not change @es[SEL],
             we may use @not-in and @binds to invoke our induction hypothesis
             to conclude that @es[(= (of (compile p-pure_i) So) 0)]}
            @#:step[final]{By @es[(not-= S S_2)] and definition of the compilation of @es[signal],
             we know that the @es[So] wire will remain unchanged. Therefore
             we can conclude that
             @es[(= (of (compile p-pure_i) S_o) (of (compile (signal S_2 p-pure_i)) S_o) 0)].}
          }}
          @#:case[(L¬∈ S_2 (->S (Can p-pure_i (<- θ (mtθ+S S_2 unknown)))))]{
           In this case
           @es[(= (->S (Can (signal S_2 p_i) θ)) (Lset-sub (->S (Can p-pure_i (<- θ (mtθ+S S_2 absent)))) (L1set S)))].
           The argument for this case follows exactly along the same
           lines as the previous case, but we must instead show that
           @es[(binds (compile p-pure_i) (<- θ (mtθ+S S_2 absent)))] rather
           than @es[(binds (compile p-pure_i) (<- θ (mtθ+S S_2 unknown)))].
           To show this we first argue that
           @es[(binds (compile p-pure_i) (<- θ (mtθ+S S_2 unknown)))] still
           holds, as it replaces no restrictions on the value of
           @es[S_2]. From this we can apply induction using
           @es[(L¬∈ S_2 (->S (Can p-pure_i (<- θ (mtθ+S S_2 unknown)))))] to
           argue that @es[(= (of (compile p-pure_i) S_2) 0)]. Since this is
           the interpretation of @es[(mtθ+S S_2 absent)], we can safely
           conclude that
           @es[(binds (compile p-pure_i) (<- θ (mtθ+S S_2 absent)))]. Thus
           we can apply the reasoning from the previous case to
           conclude that @es[(= (of (compile (signal S_2 p-pure_i)) S_o) 0)].
           
           }])

@proof[#:label "Can-S-is-sound"
       #:title "Can S is sound"
       #:type 'lemma
       #:statement
       @list{For any term and environment @es[p-pure] and @es[θ] and any signal @es[S],
        if @es[(binds (compile p-pure) θ)],
        @es[(L¬∈ S (->S (Can p-pure θ)))], and
        @es[(≃ (of (compile p-pure) SEL) 0)], 
        then @es[(≃ (of (compile p-pure) So) 0)]}

       #:interpretation
       @list{This theorem states that @es/unchecked[Can] accurately predicts when signal output wires
        will be set to @es[0].}]{
 @cases[#:of p-pure
        #:language esterel/typeset
        #:induction
        @#:case[nothing]{
          There is no @es[So] wire, thus is it by definition @es[0].
         }
        @#:case[pause]{
          Same as previous case.
         }
        @#:case[(exit n)]{
          Same as previous case.
         }
        @#:case[(emit S_2)]{
          @cases[#:of/count (= S S_2) 2
                 #:language esterel/typeset
                 #:simple-cases
                 @#:case[(= S S_2)]{
                            In this case @es[(L∈ S (->S (Can p-pure θ)))], which violates
                            our hypothesis.
                           }
                 @#:case[(not-= S S_2)]{
                            In this case @es[(compile (emit S_2))]
                            does define an @es[S_2] wire, therefore
                            @es[(L¬∈ S (outputs (compile (emit S_2))))],
                            Therefore, by definition,
                            @es[(of (compile (emit S_2)) S)] is @es[0].
                            }]
         }
        @#:case[(signal S_2 p-pure_i)]{
          @cases[#:of/count (= S S_2) 2
                 #:language esterel/typeset
                 #:simple-cases
                 @#:case[(= S S_2)]{
                            In this case the compilation of signal removes @es[S]
                            from the set of output signals, which means
                            
                            @es[(L¬∈ So (outputs (compile p-pure)))], and therefore once
                            again it must be @es[0].
                           }
                 @#:case[(not-= S S_2)]{
                            In this case we can see that there are two cases for @es/unchecked[Can]:
                                                                                 
                            @emit-not-equal-case
                            }]
         }
        @#:case[(par p-pure_i q-pure_i)]{
                               
          In this case
          @es[(=/checked (->S (Can (par p-pure_i q-pure_i) θ)) (LU (->S (Can p-pure_i θ)) (->S (Can q-pure_i θ))))].
          This we can conclude that @es[(L¬∈ S (->S (Can p-pure_i θ)))] and
          @es[(L¬∈ S (->S (Can q-pure_i θ)))]. We also know that
          @es[(= (of (compile (par p-pure_i q-pure_i)) SEL) (or (of (compile p-pure_i) SEL) (of (compile q-pure_i) SEL)))],
          which implies that @es[(≃ (of (compile p-pure_i) SEL) 0)] and
          @es[(≃ (of (compile q-pure_i) SEL) 0)].

          Therefore, by induction, we can conclude that
          @es[(≃ (of (compile p-pure_i) S_o) 0)]
          and @es[(≃ (of (compile q-pure_i) S_o) 0)].

          As both the overall output of @es[S_o] of both subcircuits is @es[0], and
          by definition @es[(= (of (compile (par p-pure_i q-pure_o)) S_o) (or (of (compile p_i) S_o) (of (compile q_i) S_o)))],
          it must be that @es[(≃ (of (compile (par p-pure_i q-pure_o)) S_o) 0)].}
        @#:case[(present S_2 p-pure_i q-pure_i)]{ We know that
          @es[(= (of (compile (present S_2 p-pure_i q-pure_i)) SEL) (or (of (compile p-pure_i) SEL) (of (compile q-pure_i) SEL)) 0)].
          Therefore

          @es[(≃ (of (compile p-pure_i) SEL) 0)] and
          @es[(≃ (of (compile q-pure_i) SEL) 0)]. We also know that
          @es[(= (of (compile (present S_2 p-pure_i q-pure_i)) S_o) (or (of (compile p-pure_i) S_o) (of (compile q-pure_i) S_o)))].
          
          @cases[#:of/count (θ-get-S θ S_2) 3
                 #:language esterel/typeset
                 @#:case[present]{
                            In this case we know that
                            @es[(= (->S (Can (present S_2 p-pure_i q-pure_i) θ)) (->S (Can p-pure_i θ)))].
                            In addition not that @es[(= (θ-get-S θ S_2) present)] means
                            that @es[(≃ (of (compile (present S_2 p-pure_i q-pure_i)) Si_2) 1)],
                            therefore
                            
                            @es[(≃ (of (compile q-pure_i) GO) (and (of (compile (present S_2 p-pure_i q-pure_i)) GO) (not (of (compile (present S_2 p-pure_i q-pure_i)) Si_2))))],
                            which must be @es[0].
                            Therefore by @proof-ref["activation-condition"] we know that
                            @es[(≃ (of (compile q-pure_i) So) 0)].

                            
                            Then we may invoke our induction hypothesis to show
                            that @es[(≃ (of (compile p-pure_i) So) 0)]. Thus we can use a
                            similar chain of reasoning to the previous case to argue
                            that @es[(≃ (of (compile (present S_2 p-pure_i q-pure_i)) So) 0)].}
                 @#:case[absent]{
                            This case is analogous to the previous one, except
                            that the branches switch roles.
                           }
                 @#:case[unknown]{
                            In this case we know that
                            @es[(= (->S (Can (present S_2 p-pure_i q-pure_i) θ)) (LU (->S (Can p-pure_i θ)) (->S (Can q-pure_i θ))))].
                            Thus we can conclude that @es[(L¬∈ S (->S (Can p-pure_i θ)))] and @es[(L¬∈ S (->S (Can q-pure_i θ)))].
                            As previously we know that @es[So] must be in the outputs of @es[(compile p-pure_i)] or
                            @es[(compile q-pure_i)]. Thus, by induction, @es[(≃ (of (compile p_i) So) 0)]
                            and @es[(≃ (of (compile q_i) So) 0)].

                            From this we may conclude that @es[(≃ (of (compile (present S_2 p-pure_i q-pure_i)) So) 0)].
                                     
                            }]
         }
        @#:case[(suspend p-pure_i S_2)]{
          In this case we know that @es[(= (->S (Can (suspend p-pure_i S_2) θ)) (->S (Can p-pure_i θ)))].
          We also know that
          
          @es[(= (of (compile (suspend p-pure_i S_2)) SEL) (of (compile p-pure_i) SEL))].
          Therefor by induction @es[(≃ (of (compile p_i) So) 0)]. Finally the compilation of @es[suspend] does
          not change output signals so we can conclude that @es[(≃ (of (compile (suspend p_i S_2)) So) 0)].
         }
        @#:case[(trap p-pure_i)]{ 
          This case follows identically to the previous one, as the
          compilation of @es[trap] neither modifies @es[SEL] nor
          signals form its inner term.
         }
        @#:case[(seq p-pure_i q-pure_i)]{
          Note that @es[(= (of (compile (seq p-pure_i q-pure_i)) SEL) (or (of (compile p-pure_i) SEL) (of (compile q-pure_i) SEL)))].
          Therefore @es[(= (of (compile p-pure_i) SEL) (of (compile q-pure_i) SEL) 0)].
          From the definition of @es/unchecked[Can] we have two cases:
          @cases[#:of/count (L∈ 0 (->K (Can p-pure_i θ))) 2
                 #:language esterel/typeset
                 @#:case[(L¬∈ 0 (->K (Can p-pure_i θ)))]{
                            In this case we have @es[(= (->S (Can (seq p-pure_i q-pure_i) θ)) (->S (Can p-pure_i θ)))].
                            By induction we can conclude @es[(≃ (of (compile p-pure_i) So) 0)].
                            In addition by @proof-ref["Can-K-is-sound"] we can conclude that @es[(≃ (of (compile p-pure_i) K0) 0)].
                            This tells us that @es[(≃ (of (compile q-pure_i) GO) 0)]. Thus, by @proof-ref["activation-condition"],
                            we can conclude that @es[(≃ (of (compile q-pure_i) So) 0)].
                            As @es[S_o] is either no in the outputs or @es[0] in either subcircuit, we can conclude
                            that @es[(≃ (of (compile (seq p-pure_i q-pure_i)) So) 0)].
                           }
                 @#:case[(L∈ 0 (->K (Can p-pure_i θ)))]{
                            In this case we have @es[(= (->S (Can (seq p-pure_i q-pure_i) θ)) (LU (->S (Can p-pure_i θ)) (->S (Can q-pure_i θ))))].
                            From this we know that

                            @es[(L¬∈ S (->S (Can p-pure_i θ)))] and @es[(L¬∈ S (->S (Can q-pure_i θ)))].
                            Thus, by induction we have that @es[(≃ (of (compile p-pure_i) So) 0)]
                            and that @es[(≃ (of (compile q-pure_i) S_o) 0)].
                            As @es[So] is @es[0] in both subcircuits, we can conclude
                            that @es[(≃ (of (compile (seq p-pure_i q-pure_i)) So) 0)].}]
         }
        @#:case[(ρ θr A p_i)]{This case is shown by @proof-ref["Can-rho-S-is-sound"].}
        @#:case[(loop p_i) #:ignore]{TODO}
        @#:case[(loop^stop p_i q_i) #:ignore]{TODO}]
}


@proof[#:label "Can-K-is-sound"
       #:title "Can K is sound"
       #:statement
       @list{For any term and environment @es[p-pure] and @es[θ] and any return code @es[κ],
        if @es[(binds (compile p-pure) θ)],
        @es[(L¬∈ κ (->K (Can p-pure θ)))], and@(linebreak)
        @es[(≃ (of (compile p-pure) SEL) 0)],
        then
        @es[(≃ (of (compile p-pure) (K κ)) 0)]}
       #:interpretation
       @list{This theorem states that @es/unchecked[Can] accurately predicts when control wires
        will be set to @es[0].}]{
 @cases[#:of p-pure
        #:language esterel/typeset
        #:induction
        @#:case[nothing]{
          Note that in this case @es[(= (->K (Can nothing θ)) (L1set 0))].
          @cases[#:of/count @es[(= κ 0)] 2
                 #:simple-cases
                 @#:case[(= κ 0)]{
                            In this case @es[(L∈ κ (->K (Can p θ)))] which violates our hypothesis.
                           }
                 @#:case[(not-= κ 0)]{
                            There is no @es[Kκ] wire in this case, thus it is by definition @es[0].
                           }
                 ]}
        @#:case[(emit S)]{This is the same as the previous case.}
        @#:case[(exit n)]{This is the same as the previous
          two cases, but with @es[n] substituted for @es[0].}
        @#:case[pause]{ Note that
          @es[(= (->K (Can pause θ)) (L1set 1))]. In the only @es[K]
          other wire in @es[(compile pause)] is @es[K0], so we need
          only concern ourselves with that.
          @es[(= (of (compile pause) K0) (and (of (compile pause) SEL) (of (compile pause) RES)))],
          so as @es[(≃ (of (compile p) SEL) 0)], @es[(≃ (of (compile pause) K0) 0)].}
        @#:case[(signal S p-pure_i)]{
          @sequenced{

           @#:step[=]{By the definition of @es[Can],
            @es[(= (->K (Can (signal S p-pure_i) θ)) (->K (Can p-pure_i θ)))].}

           @#:step[sel]{By the definition of @es[compile],
            @es[(= (of (compile (signal S p-pure_i)) SEL) (of (compile p-pure_i) SEL))].}
           @#:step[_]{By @= and @sel, this case follows by induction.}
                    
         }}
        @#:case[(seq p-pure_i q-pure_i)]{
          @[sequenced
            @#:step[SEL]{By the definition of @es[compile]
                       and the premise that @es[(≃ (of (compile p-pure) SEL) 0)],
                       we can conclude that @es[(≃ (of (compile p-pure_i) SEL) 0)]
                       and @es[(≃ (of (compile q-pure_i) SEL) 0)].}
            @#:step[k0]{By the definition of @es[compile],
                       @es[(≃ (of (compile p-pure) K0) (of (compile q-pure_i) K0))]}
            @#:step[kn]{By the definition of @es[compile], for all @es[(> κ 0)]
                       @es[(≃ (of (compile p-pure) Kκ) (or (of (compile p-pure_i) Kκ) (of (compile q-pure_i) Kκ)))]}
            @[#:step _
              @[cases
 #:of/count (L∈ 0 (->K (Can p-pure_i θ))) 2
 #:language esterel/typeset
 #:simple-cases
 @#:case[(L¬∈ 0 (->K (Can p-pure_i θ)))
         @[sequenced
           @#:step[kin]{By the definition of @es[Can], we know that @es[(= (Can p-pure θ) (Can p-pure_i θ))]}
           @#:step[in]{By @kin we know that @es[(L∉ n (->K (Can p-pure_i θ)))]}
           @#:step[qin]{By @in, @SEL, and induction, we know that @es[(≃ (of (compile p-pure_i) K0) 0)]}
           @#:step[q0]{By @qin and the definition of compile we know that @es[(≃ (of (compile q-pure_i) GO) 0)]}
           @#:step[qnot]{by @q0 and @SEL, and @proof-ref["activation-condition"], we know that
                                                          all outputs of @es[q-pure_i] are @es[0].}
           @#:step[ind]{By @kin and @SEL, and induction, we know that @es[(≃ (of (compile p-pure_i) Kn) 0)]}
           @#:step[_]{By @qnot, @ind, and both @k0 or @kn, may conclude that
                                                          @es[(≃ (of (compile p-pure) Kn) 0)].}
           ]]
 @#:case[(L∈ 0 (->K (Can p-pure_i θ)))
         @[sequenced
           @#:step[eq]{By the definition of @es[Can], we know that
                                                          @es[(= (->K (Can p-pure θ)) (LU (->K (Can p-pure_i θ)) (->K (Can q-pure_i θ))))]}
           @#:step[zero]{By @eq and our premise, we know that @es[(L∉ n (->K (Can p-pure_i θ)))]
                                                          and @es[(L∉ n (->K (Can q-pure_i θ)))]}
           @#:step[ind]{By @zero and @SEL, we may induct on @es[p-pure_i] and @es[q-pure_i]
                                                          to conclude that
                                                          @es[(≃ (of (compile p-pure_i) Kn) 0)]
                                                          and
                                                          @es[(≃ (of (compile q-pure_i) Kn) 0)]}
           @#:step[_]{By @ind and @kn, we may conclude that
                                                          @es[(≃ (of (compile p-pure) Kn) 0)].}
           ]]]]]}
        @[#:case (present S p-pure_i q-pure_i)
          (sequenced
           @#:step[SEL]{By the definition of @es[compile]
                    and the premise that @es[(≃ (of (compile p-pure) SEL) 0)],
                    we can conclude that @es[(≃ (of (compile p-pure_i) SEL) 0)]
                    and @es[(≃ (of (compile q-pure_i) SEL) 0)].}
           @#:step[kn]{By the definition of @es[compile], for all @es[κ]
                    @es[(≃ (of (compile p-pure) Kκ) (or (of (compile p-pure_i) Kκ) (of (compile q-pure_i) Kκ)))]}
           @[#:step _
             [cases
 #:of/count (θ-get-S θ S) 3
 #:language esterel/typeset
 @[#:case present
   [sequenced
    @#:step[in]{By the definition of @es[Can], we know that @es[(L∉ n (->K (Can p-pure_i θ)))].}
    @#:step[induct]{By @in, @SEL, and induction we can conclude
                                         that @es[(≃ (of (compile q-pure_i) Kn) 0)].}
    @#:step[go0]{by @es[(binds (compile p-pure) θ)], and the definition
                                         of @es[compile],
                                         we can conclude that
                                         @es[(≃ (of (compile q-pure_i) GO) 0)].}
    @#:step[_]{By @induct, @go0, and @kn we can conclude that @es[(≃ (of (compile p-pure) Kn) 0)].}]]
 @#:case[absent]{This case is analogous to the previous case.}
 @#:case[unknown]{This follows directly by induction on both branches.}
 ]])]
        @[#:case(par p-pure_i q-pure_i)
          @[sequenced
            [#:step def
 @list{By the definition of @es[Can], @es[(= (->K (Can (par p-pure_i q-pure_i) θ)) (Lmax* (->K (Can p-pure_i θ)) (->K (Can q-pure_i θ))))]}]
            [#:step in
             @list{By @def and the premise that @es[(L¬∈ κ (->K (Can p-pure θ)))], we have three cases:
                                             @[itemlist
                                               [item
                                                @list{@es[(L¬∈ κ (->K (Can p-pure_i θ)))] and @es[(L¬∈ κ (->K (Can q-pure_i θ)))]}]
                                               [item
                                                @list{@es[(L∈ κ (->K (Can p-pure_i θ)))] but for all @es[(L∈ κ_2 (->K (Can q-pure_i θ)))], @es[(> k_2 κ)]}]
                                               [item
                                                @list{@es[(L∈ κ (->K (Can q-pure_i θ)))] but for all @es[(L∈ κ_2 (->K (Can p-pure_i θ)))], @es[(> k_2 κ)]}]]}]
            [#:step _
             [cases #:of/count (in) 3
              #:litteral
              #:tuplize
              #:language esterel/typeset
              @#:case[((L¬∈ κ (->K (Can p-pure_i θ))) (L¬∈ κ (->K (Can q-pure_i θ))))
                      [sequenced
                       @#:step[a]{It is clear from the definition of the synchronizer that an output wire @es[Kn] can only
                                                                                                        be @es[1] if at least
                                                                                                        one of the subcircuits has its @es[Kn] equal to @es[1]}
                       @#:step[b]{By induction we may conclude that @es[(≃ (of (compile p-pure_i) Kκ) 0)] and @es[(≃ (of (compile q-pure_i) Kκ) 0)].}
                       @#:step[_]{By @a and @b, we can conclude that @es[(≃ (of (compile (par p-pure_i q-pure_i)) Kκ) 0)]}]]
                                                          
                
              @[#:case((L∈ κ (->K (Can p-pure_i θ))))
                [sequenced
                 @#:step[lem]{As @es[(≃ (of (compile p-pure) SEL) 0)], and by the definition of @es[compile], we know that both
                                                                                            the @es[LEM] and @es[REM] wires are @es[0].}
                 @#:step[out]{By the definition of the parallel synchronizer, @lem means that a @es[Kn] wire can be @es[1]
                                                                                            only if there is a @es[Ln_1] and a @es[Rn_2] wire which are @es[1],
                                                                                            where @es[(<== n_1 n)] and @es[(<== n_2 n)]}
                 @#:step[ind]{By induction on each @es[Kκ_3] wire less @es[κ] in @es[q-pure_i], which in this clause must not be in the result of @es[Can],
                                                                                            all @es[Rn_2] wires less than @es[Kκ] must be @es[0].}
                 @#:step[_]{By @ind and @out, @es[(≃ (of (compile (par p-pure_i q-pure_i)) Kκ) 0)].}]]
                @#:case[((L∈ κ (->K (Can q-pure_i θ))))]{This case is analogous to the previous one.}]]]]
        @#:case[(suspend p-pure_i S)]{This case follows fairly directly by induction.}
        @#:case[(trap p-pure_i)]{This case follows fairly directly by induction.}
        @#:case[(ρ θr A p_i)]{This case is given  by @proof-ref["Can-rho-K-is-sound"].}
        @#:case[(loop p_i) #:ignore]
        @#:case[(loop^stop p_i q_i) #:ignore]]
}

@proof[#:label "Can-rho-S-is-sound"
       #:title "Can rho S is sound"
       #:statement
       @list{For all @es[p-pure], @es[θ], @es[A], @es[S],
        if @es[(L¬∈ S (->S (Can-θ (ρ θr A p-pure) ·)))]
        and @es[(≃ (of (compile (ρ θr A p-pure)) SEL) 0)]
        then
        @es[(≃ (of (compile (ρ θr A p-pure)) So) 0)]}
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
       @list{For any term and environment @es[p-pure] and @es[θ] and @es[A], and return code @es[κ]
        if
        @es[(L¬∈ κ (->K (Can-θ (ρ θr A p-pure) ·)))],@(linebreak)
        and @es[(≃ (of (compile (ρ θr A p-pure)) SEL) 0)], then
        @es[(≃ (of (compile (ρ θr A p-pure)) (K κ)) 0)]}
       #:interpretation
       @list{This theorem states that @es/unchecked[Can-θ] accurately predicts when control wires
        will be set to @es[0].}]{
 @es/unchecked[Can-θ] is essentially repeated applications of
 the @es[signal] case in @es/unchecked[Can]. This holds by the same line of argument there used in that case
 of @proof-ref["Can-K-is-sound"].
}

@proof[#:label "paused-is-k1"
       #:title "Can K on paused is {1}"
       #:statement
       @list{For all @es[paused], @es[θ], @es[(=/checked (->K (Can paused θ)) (L1set 1))]}]{
 @cases[#:of paused_o
        #:language esterel/typeset
        #:induction]{
  @#:case[pause]{Follows by the definition of @es[Can].}
  @#:case[(suspend paused S)]{
   By the definition of @es[Can],
   @es[(=/checked (->K (Can (suspend p S) θ)) (->K (Can p θ)))], thus this follows by induction.}
  @#:case[(seq paused q)]{
   By induction we know that @es[(=/checked (->K (Can paused θ)) (L1set 1))].
   By the definition of @es[Can], this means @es[(=/checked (->K (Can (seq paused q) θ)) (->K (Can paused θ)))].
   Therefore, @es[(=/checked (->K (Can (seq paused q) θ)) (L1set 1))]. }
  @#:case[(par paused_1 paused_2)]{By induction
   @es[(=/checked (->K (Can paused_1 θ)) (->K (Can paused_2 θ)) (L1set 1))].
   Thus, by the definition of @es[Can],
   @es[(=/checked (->K (Can (par paused_1 paused_2) θ)) (L1set 1))].}
  @#:case[(trap paused)]{
   By induction @es[(=/checked (->K (Can paused θ)) (L1set 1))].
   By the definition of @es[↓] and @es[Can],@(linebreak)
   @es[(=/checked (->K (Can (trap paused) θ)) (Lharp... (->K (Can paused θ))) (Lharp... (L1set 1)) (L1set 1))].} 
  @#:case[(loop^stop paused q) #:ignore]
}}                    