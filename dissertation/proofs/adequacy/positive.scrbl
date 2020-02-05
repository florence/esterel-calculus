#lang scribble/base

@(require "../../lib/redex-rewrite.rkt"
          "../../lib/util.rkt"
          "../../lib/proofs.rkt"
          "../../lib/proof-extras.rkt"
          redex/reduction-semantics
          redex/pict
          pict
          (except-in esterel-calculus/redex/model/shared FV FV/e θ-get-S)
          esterel-calculus/redex/test/binding
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (only-in esterel-calculus/redex/model/reduction
                   blocked-pure)
          (except-in scribble-abbrevs/latex definition))

@title[#:style paper-title-style "Positive"]


@proof[#:label "e-v-is-c-v"
       #:title "Esterel Value is Circuit Value"
       #:statement
       @list{Forall @es[(ρ θ GO done)],
        if @es[(complete-with-respect-to θ done)],
        @es[(ρ θ GO done)] is closed, and

        
        @es[(= (of (compile (ρ θ GO done)) RES) (of (compile (ρ θ GO done)) SUSP) (of (compile (ρ θ GO done)) KILL) 0)],
        and @es[(= (of (compile (ρ θ GO done)) GO) 1)].
        
        then 
        @es[(compile (ρ θ GO done))] is constructive.}]{
                                                        
 To do this we must show that all wires in by
 @es[(ρ θ GO done)] settle to a given value. First, we turn to the inputs.
 By the hypothesis of this lemma @es[SUSP], @es[RES], @es[KILL], and @es[GO]
 have all settled.

 For all signal wires in @es[θ], by our hypothesis they are set to @es[1] by the defintion compilation of
 @es[θ], or they are @es[0] by @es["sel-start"] and @proof-ref["Can-S-is-sound"].

 For the remaining wires, they all settle by @proof-ref["done-is-constructive"].
 
}

@proof[#:label "done-is-constructive"
       #:title "Done is Constructive"
       #:statement
       @list{For all @es[done] and @es[θ], if forall @es[(L∈ w (inputs (compile done)))],
        @es[(not-= (of (compile done) w) ⊥)],
        
        @es[(= (of (compile done) GO) 1)],
        
        @es[(= (of (compile done) RES) (of (compile done) SUSP) (of (compile done) KILL) 0)],
        
        and @es[(binds (compile done) θ)]
        then @es[(compile done)] is construtive}]{
 @cases[#:of done
        #:language esterel/typeset
        #:induction
        @#:case[nothing]{@check[(assert-totally-constructive (compile-esterel (term nothing)))]}
        @#:case[(exit n)]{@check[(assert-totally-constructive (compile-esterel (term (exit 5))))]}
        @#:case[pause]{@check[(assert-totally-constructive (compile-esterel (term pause)))]}
        @#:case[(seq paused q)]{
          @sequenced{
           @#:step[induction]{
            The compilation of seq passes all of its inputs to @es[paused]
            unchanged, therefor we can invoke our induction hypothesis
            to show that all wires in @es[pause] are defined.}
          
           @#:step[k0]{
            by @proof-ref["paused-is-k1"] we know that, for any possible
            binding environment @es[θ], @es[(L¬∈ 0 (->K (Can paused θ)))].
           }

           @#:step[is-zero]{
            By @k0 and @proof-ref["sel-start"] and @proof-ref["Can-K-is-sound"]
            we know that either @es[(L¬∈ K0 (inputs (compile done)))] or
            @es[(= (of (compile done) K0) 0)].
           }
           @#:step[qcon]{
            By @is-zero 
            and @proof-ref["activation-constructiveness"], @es[(compile q)] is constructive.
           }
           @#:step[_]{
            By @induction and @qcon, the entire circuit is constructive.
           }
          }
         }
        @#:case[(trap paused)]{
          The compilation of @es[trap] passes all of its inputs to @es[paused]
          unchanged, therefor we can invoke our induction hypothesis
          to show that all wires in @es[pause] are defined. Therefore
          the entire circuit is constructive.
         }
        @#:case[(par paused_1 paused_2)]{ The compilation of
          @es[par] passes all of its inputs to @es[paused_1] and
          @es[paused_2] unchanged, therefore by induction both are
          constructive. Note that the synchronizer is acyclic,
          therefore as all of its inputs are defined it too is
          constructive. Therefore the entire circuit is constructive.
         }
        @#:case[(suspend paused S)]{
          @sequenced{

           @#:step[go-1]{
                         
            By the definition of @es/unchecked[(compile dot)],
            @es[(= (of (compile paused) GO) (of (compile (suspend paused S)) GO) 1)].
                                 
           }

           @#:step[kill-0]{
                           
            By the definition of @es/unchecked[(compile dot)],
            @es[(= (of (compile paused) KILL) (of (compile (suspend paused S)) KILL) 0)].

           }

           @#:step[susp-0]{

                           
            let @es[(= c (compile (suspend paused S)))],
                
            By the definition of @es/unchecked[(compile dot)],
            @es[(= (of (compile paused) SUSP) (or (of c SUSP) (parens (and (of c S) (of c RES) (of c SEL)))))].
            which by our premises is:            
            @es[(= (of (compile paused) SUSP) (or 0 (parens (and (of c S) 0 (of c SEL)))) 0)].

           }

           @#:step[res-0]{

                           
            let @es[(= c (compile (suspend paused S)))],
                
            By the definition of @es/unchecked[(compile dot)],
            @es[(= (of (compile paused) RES) (and (of c RES) (of c SEL) (not (of c S))))].

            
            which by our premises is:            
            @es[(= (of (compile paused) RES) (and 0 1 (not (of c S))) 0)].

           }

           @#:step[θ-binds]{
                            
            By the definition of @es/unchecked[(compile dot)],
            the input environment is passed in unchanged,
            therefore @es[(binds (compile paused) θ)].
                                 
           }

           @#:step[paused-constructive]{

            By @go-1, @kill-0, @susp-0, @res-0, and @θ-binds,
            we an invoke our inductive hypothesis
            to conclude that @es[(compile paused)] is constructive.
           }

           @#:step[k1-constructive]{
            let @es[(= c (compile (suspend paused S)))].

                
            By the definition of @es/unchecked[(compile dot)], the outputs
            of @es[c] are the same as the outputs of @es[paused], except
            for the @es[(= (of c K1) (or (of (compile paused) K1) (parens (and (of c S) (of c RES) (of (compile paused) SEL)))))].

            By our premises, this is:
            
            @es[(= (of c K1) (or (of (compile paused) K1) (parens (and (of c S) 0 (of (compile paused) SEL)))) (or (of (compile paused) K1) 0) (of (compile paused) K1))].
                                    
           }

           @#:step[final]{

            By @paused-constructive and @k1-constructive we can
            conclude that a wires are defined, and therefore
            @es[(compile (suspend paused S))] is constructive.

           }
                      
          }
         }
        @#:case[(loop^stop paused q) #:ignore]{}
        ]}


@proof[#:label "blocked-implies-can-rho"
       #:title "blocked implies can-rho"
       #:statement
       @list{For all @es[p], @es[θ_1], @es[θ_2], @es[A],
        if
        @es[(blocked-pure (parens (<- θ_1 θ_2)) A hole p)]
        and
        @es[(distinct (Ldom θ_1) (Ldom θ_2))]
        then there exits some @es[S] such that
        @es[(L∈ S (->S (Can-θ (ρ θ_1 A p) θ_2)))]}]{
 @cases[#:of/count (Ldom θ_1) 2
        #:language esterel/typeset]{
                       
  @#:case[(L0set)]{
   This puts us in the last clause of @es[Can-θ], which just
   calls @es[Can]. Thus 
   this case is given by @proof-ref["blocked-implies-can"],
   where @es[(= E hole)] and @es[(= p p)].
  }
  @#:case[(LU (L1set S_1) L-S)]{
   @cases[#:of/count ((θ-ref-S θ S_1 ⊥) (L¬∈ S_1 (->S (Can-θ (ρ (Lwithoutdom θ S) A p) (<- θ_2 (mtθ+S S unknown))))))
          2
          #:language esterel/typeset
          #:tuplize
          #:simple-cases]{

    @#:case[(tt tt)]{

     This puts us in the first case of @es[Can-θ].@sequenced{
      @#:step[blocked]{
       By @proof-ref["blocked-respects-can"] we know that
       @es[(blocked-pure (<- (<- θ_1 θ_2) (mtθ+S S_1 absent)) A hole p)].}
      @#:step[eq]{
       As the domains of @es[θ_1] and @es[θ_2] are distinct we can also
       conclude that @newline @es[(= (<- (<- θ_1 θ_2) (mtθ+S S_1 absent)) (<- (<- (Lwithoutdom θ_1 S_1) θ_2) (mtθ+S S_1 absent)))].}
      @#:step[_]{
       By @blocked and @eq, this case follows by induction.}}}
    @#:case[(_ _)]{ This puts us in the second case of @es[Can-θ].
     This case just copies the value of @es[S_1] from @es[θ_1] to @es[θ_2].
     As the two maps are the same this leaves @es[(<- θ_1 θ_2)] unchanged.
     Thus this case follows by induction.}}}}}

@proof[#:label "blocked-implies-can"
       #:title "blocked implies can"
       #:statement
       @list{For all @es[p], @es[θ], @es[E],
        @es[(blocked-pure θ GO E p)]
        implies that
        there exits some @es[S] such that
        @es[(L∈ S (->S (Can (in-hole E p) θ)))]}]{
 @cases[#:language esterel/typeset
        #:of (blocked-pure θ A E p)
        #:induction
        @#:case[if]{This follows from @es[Canθₛ⊆Canₛ].}
        @#:case[emit-wait]{
          This follows from @es[canₛ-capture-emit-signal].}
        @#:case[parl]{In this case
          We have @es[(= p (par p_1 done))].
          The premise of the judgment gives us
          @es[(blocked-pure θ A (in-hole E (par hole done)) p_1)].
          Thus we can invoke our induction hypothesis on this premise, giving us that
          @es[S] such that @es[(L∈ S (->S (Can (in-hole (in-hole E (par hole done)) p) θ)))].
          As @es[(= (in-hole (in-hole E (par hole done)) p_1) (in-hole E (par p_1 done)) (in-hole E p))]
          this is the conclusion we need.
                    
          
         }
        @#:case[parr]{This case proceeds analogously to the previous case.}
        @#:case[seq]{This case proceeds analogously to the previous case.}
        @#:case[suspend]{This case proceeds analogously to the previous case.}
        @#:case[trap]{This case proceeds analogously to the previous case.}
        @#:case[par-both]{There are two branches of the
          @es[par] we may induct on here, but as we only need to show the existence of some
          @es[S] we can select either one. As I am right handed I'll pick the right branch.
          The remainder of this case proceeds analogously to the previous case.}
        @#:case[loop^stop #:ignore]{TODO}]
}

@proof[#:label "blocked-rho-gives-bot"
       #:title "blocked and can-rho give non-constructiveness"
       #:statement
       @list{For all @es[θ_1], @es[θ_2], @es[p], @es[E], @es[S]
                     
        if @es[(blocked-pure (parens (<- θ_1 θ_2)) GO hole (in-hole E p))],
        @es[(distinct (Ldom θ_1) (Ldom θ_2))],
        @es[(binds (compile (in-hole E p)) (parens (<- θ_1 θ_2)))],
        @es[(L∈ S (->S (Can-θ (ρ θ_1 GO (in-hole E p)) θ_2)))],
        
        then @es[(= (of (compile (in-hole E p)) S_o) ⊥)]}]{
 @cases[#:language esterel/typeset
        #:of/count (Ldom θ_1) 2
        #:induction
        @#:case[(L0set)]{
          This case is given by @proof-ref["blocked-can-gives-bot"].}
        @#:case[(LU (L1set S_1) L-S)]{
          @cases[#:language esterel/typeset
                 #:of/count (= S S_1) 2
                 #:simple-cases]{
           @#:case[(not-= S S_1)]{
            @cases[#:language esterel/typeset
                   #:of/count (L∈ S (->S (Can-θ (ρ (Lwithoutdom θ S) A p) (<- θ_2 (mtθ+S S unknown))))) 2
                   #:simple-cases]{
             @#:case[(L¬∈ S (->S (Can-θ (ρ (Lwithoutdom θ S) A p) (<- θ_2 (mtθ+S S unknown)))))]{
              Let @es[(= θ_3 (Lwithoutdom θ_1 S))] and @es/unchecked[(= θ_4 (<- θ_2 (mtθ+S S absent)))].
              @sequenced{
               @#:step[eql]{
                @es[(= (<- θ_3 θ_4) (<- θ_1 θ_4) (<- (parens (<- θ_1 θ_2)) (mtθ+S S absent)))]}
               @#:step[bound1]{By the same argument as @proof-ref["Can-rho-S-is-sound"],
                                                       
                we can conclude that
                @es[(binds (compile (in-hole E p)) (<- (parens (<- θ_1 θ_2)) (mtθ+S S absent)))].}
               @#:step[bound]{By @eql and @bound we can conclude that @es[(binds (compile (in-hole E p)) (parens (<- θ_3 θ_4)))].}
               @#:step[distinct]{
                As we have removed an element from one map and added it to the other
                we can conclude that @es[(distinct (Ldom θ_3) (Ldom θ_4))].}
             }}
             @#:case[(L∈ S (->S (Can-θ (ρ (Lwithoutdom θ S) A p) (<- θ_2 (mtθ+S S unknown)))))]{
              Let @es[(= θ_3 (Lwithoutdom θ_1 S))] and @es/unchecked[(= θ_4 (<- θ_2 (mtθ+S S (θ-get-S θ_1 S))))].
              @sequenced{
               @#:step[same]{Note that 
                @es[(= (<- θ_1 θ_2) (<- θ_3 θ_4))]
                as the domains of the two are distinct, thus all have have done is copied
                an element from one map to the other, leaving its value in the overall result unchanged.}
               @#:step[distinct]{
                As we have removed an element from one map and added it to the other
                we can conclude that @es[(distinct (Ldom θ_3) (Ldom θ_4))].}
               @#:step[binds]{By @same we can conclude that @es[(binds (compile (in-hole E p)) (parens (<- θ_3 θ_4)))].}
               @#:step[blocked]{By @same we can conclude that @es[(blocked-pure (parens (<- θ_3 θ_4)) GO hole (in-hole E p))].}
               @#:step[can-unchanged]{By the definition of
                @es[Can-θ] we can conclude that
                @es/unchecked[(= (Can-θ (ρ θ_1 GO (in-hole E p)) θ_2) (Can-θ (ρ θ_3 GO (in-hole E p)) θ_4))].}
               @#:step[induction]{By @distinct through @can-unchanged we can invoke our induction
                hypothesis on @es[θ_3] and @es[θ_4]
                to conclude that @es[(= (of (compile (in-hole E p)) S_o) ⊥)].}
           }}}}
           @#:case[(= S S_1)]{
            This case is imposible by the monotonicity of @es[Can-θ]
            given by @text["canθₛ-set-sig-monotonic-absence-lemma" 'modern],
            as our premise states that @es[(L∈ S (->S (Can-θ (ρ θ_1 GO (in-hole E p)) θ_2)))],
            but this condition requires that
            @es[(L¬∈ S (->S (Can-θ (ρ θ_1 GO (in-hole E p)) θ_2)))].
            }}}]}
       



@proof[#:label "blocked-separable"
       #:title "blocked is separable"
       #:statement
       @list{for all @es[p], @es[θ], @es[A], @es[E_1], and @es[E_2]
        @es[(blocked-pure θ A E_1 (in-hole E_2 p))]
        implies
        @es[(blocked-pure θ A (in-hole E_1 E_2) p)].}]{

 @cases[#:of E_2
        #:induction
        #:language esterel/typeset
        @#:case[hole]{Trivial, as @es[(= (in-hole hole p) p)]
          and @es[(= (in-hole E_1 hole) E_1)].}
        @#:case[(suspend E_3 S)]{
          Try by induction on the premise
          of this clause of @es[blocked].}
        @#:case[(trap E_3)]{Same as above.}
        @#:case[(seq E_3 q)]{Same as above.}
        @#:case[(par E_3 q)]{Same as above.}
        @#:case[(par p E_3)]{Same as above.}
        @#:case[(loop^stop E_3 q) #:ignore]{TODO}
        ]

}




@proof[#:label "blocked-can-gives-bot"
       #:title "blocked and can give non-constructiveness"
       #:statement
       @list{For all @es[p], @es[θr], @es[E], @es[S]
                     
        if @es[(blocked-pure θr GO hole (in-hole E p))],
        @es[(binds (compile (in-hole E p)) θr)],
        and @es[(θ-ref-S θr S unknown)],
        and @es[(L∈ S (->S (Can (in-hole E p) θr)))],
        and @es[(L∈ S (->S (Can p θr)))]
        then @es[(= (of (compile p) S) ⊥)]}]{
 This follows directly from @proof-ref["blocked-gives-nc-cycle"], using the set of
 signals
 @es[(->S (Can (in-hole E p) θr))] and the empty path.
}

@proof[#:label "blocked-gives-nc-cycle"
       #:title "Blocked terms have nc-cycles"
       #:statement @list{For all @es[p-pure], @es[θr], @es[E-pure], @es[S],
        @es[L-S] and @es[Pnc] in @es[(compile (ρ θr GO (in-hole E-pure p-pure)))],@(linebreak)
        if @es[(blocked-pure θr GO hole (in-hole E-pure p-pure))],
        @es[(binds (compile (in-hole E-pure p-pure)) θr)],
        @es[(θ-ref-S θr S unknown)],@(linebreak)
        @es[(L∈ S (->S (Can (in-hole E-pure p-pure) θr)))],
        @es[(L∈ S (->S (Can p-pure θr)))],@(linebreak)
        for all @es[(L∈ S_p (->S (Can p-pure θr)))], either @es[(L∈ S_p L-S)] or @es[(Path∈ S_p Pnc)],@(linebreak)
        and either @es[(= (of (compile (in-hole E-pure p-pure)) (of Pnc 0)) (in-hole Cc1 S))]
        or @es[(= (of (compile (in-hole E-pure p-pure)) (of Pnc 0)) (in-hole Cc1 K0))]
        or @es[Pnc] is empty,@(linebreak)
        then there exists an @es[(L∈ S_q (->S (Can (in-hole E-pure p-pure) θr)))]
        such that there is an nc-cycle @es[Pnc_o] in @es[(compile (ρ θr GO (in-hole E-pure p-pure)))] on @es[S_q].}]{
 @sequenced{
  @#:step[breakup]{
   By @proof-ref["blocked-separable"], we can arrive
   at @es[(blocked-pure θr GO E p)].
  }
  @#:step[_]{
   @cases[#:of (L-S p-pure)
          (#:unchecked #:standard)
          #:lexicographic
          #:language esterel/typeset]{
  
    @;{base cases}
 
    @#:case[((LU (L1set S_b) L-S) (present S_b p-pure_i q-pure_i))]{
     By  @proof-ref["present-cycle-S"] we have an nc-path @es[Pnc_i1]
     from @es[S_b] to @es[S].
     By @proof-ref["present-cycle-K"] we have an nc-path @es[Pnc_i2]
     from @es[S_b] to @es[K0].
     
     If @es[Pnc] is empty, let @es[(= Pnc_o Pnc_i)].
     If the head of @es[(of Pnc 0)] depends on @es[S], then
         let @es[Pnc_o] be @es[Pnc_i] prepended to @es[Pnc].
     If the head of @es[(of Pnc 0)] depends on @es[K0], then
         let @es[Pnc_o] be @es[Pnc_i2] prepended to @es[Pnc].

     Then we induct on @es[S], @es[L-S] and @es[Pnc_o].}
    @#:case[(L-S (present S_b p-pure_i q-pure_i))]{
     where @es[(L¬∈ S_b L-S)].

     This this case we have that @es[(Path∈ S_b Pnc)].
     Therefore we can read-add @es[S_b] using the same argument
     we used in the previous case. In addition as we have re-added
     @es[S_b] to our path, the new path is a cycle. Thus
     we have shown there is an nc-cycle on @es[S_b].}
    @;{Base *and* Induction}
    @#:case[(L-S (seq p-pure_i q-pure_i))]
    @;{Induction}
    @#:case[(L-S (trap p-pure_i))]{
     Note that compilation trap passes the @es[S] wire unchanged.
     By @proof-ref["term-cycle-K"], we know that @es[K2] and @es[K0] of @es[(compile p-pure_i)],
     must be in an nc-path with @es[GO], therefore we can extend @es[Pnc] with the @es[K0] of
     @es[(compile (trap p-pure_i))]. (TODO, unconvincing)
     Therefore this case follows directly by induction on @es[L-S] and @es[p-pure_i]}
    @#:case[(L-S (suspend p-pure_i S_s))]{
     Note that compilation @es[suspend] passes the @es[S] and @es[K0] wires unchanged.
     Therefore this case follows directly by induction on @es[L-S] and @es[p-pure_i]}
    @#:case[(L-S (par p-pure_i q-pure_i))]{
     @sequenced{
      @#:step[path]{The compilation of @es[par] leaves signals unchanged.
       In addition by 
       By @proof-ref["term-cycle-K"], we know that all @es[Kn]s are in nc-paths with
       @es[GO], therefore we may extend @es[Pnc] with @es[K0], and use this path for induction.
       (TODO unconvincing)}
      @#:step[either]{
       By the definition of @es[Can],
       @es[(= (->S (Can (par p q) θ)) (LU (->S (Can p θ)) (->S (Can q θ))))]}
      @#:step[LorR]{
       By @either and laws of sets,
       this means that @es[S] must be in at least one of
       @es[(L∈ S (->S (Can p θ)))] or
       @es[(L∈ S (->S (Can q θ)))].}
      @#:step[either-blocked]{
       By the definition of @es[blocked-pure] and @breakup, at least one of
       @es[p-pure] or @es[q-pure] must be blocked.
      }
      @#:step[one-done]{
       By the definition of @es[blocked-pure] and @breakup, if @es[p-pure]
       or @es[q-pure] are not @es[blocked-pure], it must be @es[done].}
      @#:step[rec]{
       By @es[canₛ-done], the terms from @LorR must not be the terms
       which are @es[done]. Thus we may use induction to find our nc-cycle.}
      }}
    @;{impossible}
    @#:case[(L-S nothing)]{This violates the hypothesis
     that @es[(blocked-pure θr GO hole (in-hole E-pure p-pure))]}
    @#:case[(L-S (exit n))]{This violates the hypothesis
     that @es[(blocked-pure θr GO hole (in-hole E-pure p-pure))]}
    @#:case[(L-S pause)]{This violates the hypothesis
     that @es[(blocked-pure θr GO hole (in-hole E-pure p-pure))]}
    @#:case[(L-S (emit S))]{This violates the hypothesis
     that @es[(blocked-pure θr GO hole (in-hole E-pure p-pure))],
     as that requires @es[(= A WAIT)].}
    @#:case[(L-S (signal S p-pure_i))]{This violates the hypothesis
     that @es[(blocked-pure θr GO hole (in-hole E-pure p-pure))]}
    @#:case[(L-S (ρ θr A p-pure_i))]{This violates the hypothesis
     that @es[(blocked-pure θr GO hole (in-hole E-pure p-pure))]}
    @#:case[(L-S (loop p)) #:ignore]
    @#:case[(L-S (loop^stop p q)) #:ignore]}}}}


@section["Auxiliary Lemmas"]

@proof[#:label "present-cycle-S"
       #:title "Present can form an data nc-path"
       #:statement @list{
        For all @es[(= r-pure (present S_b p-pure q-pure))],
        @es[S], and @es[θr],
       if @es[(binds (compile r-pure) θr)],
       @es[(binds (compile r-pure) GO)],
       @es[(θ-ref-S θr S_b unknown)],
       @es[(θ-ref-S θr S unknown)], and
       @es[(L∈ S (->S (Can (present S_b p-pure q-pure) θr)))],
       then there is an nc-path @es[Pnc]
       from @es[Si_b] to @es[So].}]{
 @sequenced{
 @#:step[in]{
 By the definition of @es[compile], and @es[(binds (compile r-pure) GO)],
 we know that there is an nc-path from @es[Si_b] to the @es[GO]
 of @es[(compile p-pure)] and @es[(compile q-pure)].}
 @#:step[eq]{
 By the definition of @es[Can] and @es[(θ-ref-S θr S_b unknown)],
   we know that @es[(= (->S (Can (present S_b p-pure q-pure) θr)) (LU (->S (Can p-pure θr)) (->S (Can q-pure θr))))].
 }
 @#:step[Either]{
 By @eq it must be the case that @es[S] is in at least one of @es[(->S (Can p-pure θr))]
   and @es[(->S (Can q-pure θr))].
 }
 @#:step[connect]{By @proof-ref["term-cycle-S"] on whichever branch(es) @es[Either] says contains @es[S],
 we know that there is an nc-path @es[Pnc_t] from that terms @es[GO] to that terms @es[So].}
 @#:step[left]{By @in we can prefix the @es[Pnc_t] from @Either with @es[Si_b].}
 @#:step[final_1]{By @proof-ref["Can-S-is-sound"], we know that if the other branch does not contain @es[S]
 then that branches @es[So] must be @es[0] therefore we can extend the path from @es[left]
 with the @es[So] from @es[(compile r-pure)], giving us our nc-path.}
 @#:step[final_2]{If, however, the other branch does have @es[S] in it's @es[Can] set, then
 by @es[connect] we know there is an nc-path from @es[GO] to that branches @es[So].
 Thus we may still extend the nc-path from @es[left] with the @es[So] of @es[(compile r-pure)],
 as that @es[So] still cannot be @es[1].

 TODO this last step isn't very convincing...}}
}

@proof[#:label "present-cycle-K"
       #:title "Present can form an control nc-path"
       #:statement @list{
        For all @es[(= r-pure (present S_b p-pure q-pure))],
        @es[S], and @es[θr],
        @es[(binds (compile r-pure) GO)],
        then there is an nc-path @es[Pnc]
        from @es[Si_b] to @es[K0].}]{
 This proof follows by the same argument as @proof-ref["present-cycle-S"],
 just using @es[K0] instead of @es[S], and
 @proof-ref["term-cycle-K"] instead of @proof-ref["term-cycle-S"].
}


@proof[#:label "seq-cycle"
       #:title "seq can form an nc-path"
       #:statement @list{
        For all @es[E], @es[(= r-pure (seq p-pure q-pure))],
        @es[S_i], and @es[θr],
        if @es[(binds (compile r-pure) θr)],
        @es[(θ-ref-S θr S unknown)],
        @es[(L∈ S (->S (Can q-pure θr)))],
        then there is an nc-path @es[P]
        from @es[(of (compile p-pure) K0)] to @es[So].}]

@proof[#:label "term-cycle-S"
       #:title "Terms form a data nc-path"
       #:statement @list{
        For all @es[r-pure],
        @es[S], and @es[θr]
        if @es[(binds (compile r-pure) θr)],
        @es[(L∈ S (->S (Can r-pure θr)))],
        then there is an nc-path @es[Pnc]
        from @es[GO] to @es[So].}]

@proof[#:label "term-cycle-K"
       #:title "Terms form an control nc-path"
       #:statement @list{
        For all @es[r-pure], and @es[n]
        there is an nc-path @es[Pnc]
        from @es[GO] to @es[Kn].}]

@proof[#:label "blocked-respects-can"
       #:title "blocked respects Can"
       #:statement
       @list{For all @es[p], @es[E], @es[θ],
        @es[S],
        
        if @es[(blocked-pure θ A E p)],
        @es[(= (θ-get-S θ S) unknown)]
        and @es[(L¬∈ S (->S (Can-θ (ρ θ A (in-hole E p)) ·)))]

        then @es[(blocked-pure (<- θ (mtθ+S S absent)) A E p)]}]{
 @cases[#:language esterel/typeset
        #:of (blocked-pure θ A E p)
        #:induction
        @#:case[if]{This this case we can invoke
          @proof-ref["can-rho-idempotent"] using @es[θ] as
          @es[θ_1] and @es[·] as @es[θ_2] to obtain the needed
          premise to reconstruct the proof that the term is blocked.}
        @#:case[emit-wait]{As this case does not rely
          on @es[θ], the theorem still holds.}
        @#:case[parl]{
          Changing @es[θ] does not change that the right branch is
          @es[done]. Thus this holds by induction over the right branch.}
        @#:case[parr]{Analogous to the the prevous case.}
        @#:case[par-both]{
          This follows directly by induction on both premises
          of this clause of the judgment.
         }
        @#:case[seq]{This follows directly from
          induction over the premise of the judgment.}
        @#:case[suspend]{analogous to the prevous case.}
        @#:case[trap]{analogous to the prevous case.}
        @#:case[loop^stop #:ignore]{TODO}]
}
