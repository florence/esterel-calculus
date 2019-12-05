#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style]{Can Properties}

This section contains lemmas and proofs about @es/unchecked[Can] and its
relation to the circuit translation. The core theorem here is @proof-ref["Can-S-is-sound"].

@(define emit-not-equal-case
   @cases[#:language esterel/typeset
          #:of/count @es[(L∈ S_2 (->S (Can p_i (<- θ (mtθ+S S_2 unknown)))))] 2
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
       #:type 'theorem
       #:statement
       @list{For any term and environment @es[p] and @es[θ] and any signal @es[S], where @es[(binds (compile p) θ)],
        @es[(L¬∈ S (->S (Can p θ)))] implies that,
        
        @es[(=> (= (of (compile p) SEL) 0) (L∈ S (outputs (compile p))) (= (of (compile p) S_o) 0))]}

       #:interpretation
       @list{This theorem states that @es/unchecked[Can] accurately predicts when signal output wires
        will be set to @es[0].}]{
 @cases[#:of p-pure
        #:language esterel/typeset
        #:induction
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
          @es[(=/checked (->S (Can (par p_i q_i) θ)) (LU (->S (Can p_i θ)) (->S (Can q_i θ))))].
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
          Therefore

          @es[(= (of (compile p_i) SEL) 0)] and
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
        @#:case[(ρ θ A p_i)]{This case is shown by @proof-ref["Can-rho-S-is-sound"].}
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
 @cases[#:of p-pure
        #:language esterel/typeset
        #:induction
        @#:case[nothing]{
          Note that in this case @es[(= (->K (Can nothing θ)) (L1set 0))].
          @cases[#:of/count @es[(= κ 0)] 2
                 @#:case[@es[(= κ 0)]]{
                            In this case @es[(L∈ κ (->K (Can p θ)))] which violates our hypothesis.
                           }
                 @#:case[@es[(not-= κ 0)]]{
                            There is no @es[Kκ] wire in this case, which violates our induction hypothesis.
                           }
                 ]}
        @#:case[(emit S)]{This is the same as the previous case.}
        @#:case[(exit n)]{This is the same as the previous
          two cases, but with @es[n] substituted for @es[0].}
        @#:case[pause]{ Note that
          @es[(= (->K (Can pause θ)) (L1set 1))]. In the only @es[K]
          other wire in @es[(compile pause)] is @es[K0], so we need
          only concern ourself with that. @es[(= (of (compile pause) K0) (and (of (compile pause) SEL) (of (compile pause) RES)))],
          so as @es[(= (of (compile p) SEL) 0)], @es[(= (of (compile pause) K0) 0)].}
        @#:case[(signal S p_i)]{}
        @#:case[(present S p_i q_i)]{}
        @#:case[(seq p_i q_i)]{}
        @#:case[(par p_i q_i)]{}
        @#:case[(suspend p S)]{}
        @#:case[(trap p)]{}
        @#:case[(ρ θ A p_i)]{This case is shown by @proof-ref["Can-rho-K-is-sound"].}
        @#:case[(loop p_i)]{ TODO }
        @#:case[(loop^stop p_i q_i)]{ TODO }]
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

@proof[#:label "done-is-k1"
       #:title "Can K on Done is {1}"
       #:statement
       @list{For all @es[done], @es[θ], @es[(= (->K (Can done θ)) (L1set 1))]}]{
 TODO.
}

@proof[#:label "can-rho-idempotent"
       #:title "Can Rho is idempotent"
       #:statement
       @list{For all @es[θ_1], @es[θ_2], @es[p], @es[A], @es[S],
       if
        @es[(= (θ-get-S θ_1 S) ⊥)] and
        @es[(L¬∈ S (->S (Can-θ (ρ θ_1 A p) θ_2)))]
       then @es[(= (->S (Can-θ (ρ θ_1 A p) θ_2))
                   (->S (Can-θ (ρ (<- θ_1 (mtθ+S S absent)) A p) θ_2)))]}]{
 TODO
 Sketch: as @es[Can-θ] takes signal of that form an sets it to absent, nothing changes.
}