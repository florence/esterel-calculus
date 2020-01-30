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
 @sequenced{
  @#:step[breakup]{
   By @proof-ref["blocked-separable"], we can arrive
   at @es[(blocked-pure θr GO E p)].
  }
  @#:step[_]{
   @cases[#:language esterel/typeset
          #:of (in-hole E p-pure)
          #:induction]{
    @#:case[nothing]{This case violates the hypothesis that @es[(blocked-pure θ GO hole (in-hole E p))]
     via @|breakup|.}
    @#:case[pause]{This case violates the hypothesis that @es[(blocked-pure θ GO hole (in-hole E p))]
     via @|breakup|.}
    @#:case[(exit n)]{This case violates the hypothesis that @es[(blocked-pure θ GO hole (in-hole E p))]
     via @|breakup|.}
    @#:case[(emit S)]{As @es[A] is given as @es[GO], this case violates
    the hypothesis that @es[(blocked-pure θ GO hole (in-hole E p))]
     via @|breakup|.}
    @#:case[(present S_p p-pure q-pure)]{
     @sequenced{
      @#:step[both]{By the fact that this term is @es[blocked-pure],yø
       and the definition of @es[Can], we know that
       @es[(= (->S (Can (present S_p p-pure q-pure) θ))
              (LU (->S (Can p-pure θ))
                  (->S (Can q-pure θ))))]}
       @#:step[p-pure-inaccessable]{}
       @#:step[_]{TODO}
                              
   }}
   @#:case[(suspend p S)]{This case follows directly by induction.}
   @#:case[(seq p q)]{TODO}
   @#:case[(par p q)]{
    @sequenced{ 
     @#:step[either]{
      By the definition of @es[Can],
      @es[(= (->S (Can (par p q) θ))
             (LU (->S (Can p θ))
                 (->S (Can q θ))))]}
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
       which are @es[done]. Thus by induction using @LorR and @one-done,
       the @es[S] wire in one of the subbranches must be @es[unknown].}
      @#:step[sum]{
       For the other branch (if one exists) the @es[S] must be @es[0].
       If that term is @es[done], then it is @es[0] by @es[canₛ-done]
       and @es["Can-S-is-sound"].
       If that term is @es[blocked-pure] then it is @es[0] by
       @es["Can-S-is-sound"].}
      @#:step[or]{By the definition of @es[compile],
    @es[(= (of (compile (par p q)) S) (or (of (compile p) S) (of (compile q) S)))]}
      @#:step[_]{by @rec, @sum, and @or, @es[(= (of (compile (par p q)) S) ⊥)].}}}
   @#:case[(trap p)]{This case follows directly by induction.}
   @#:case[(signal S p)]{This case violates the hypothesis that @es[(blocked-pure θ GO hole (in-hole E p))]
     via @|breakup|.}
    @#:case[(ρ θ A p)]{This case violates the hypothesis that @es[(blocked-pure θ GO hole (in-hole E p))]
     via @|breakup|.}
    @#:case[(loop p) #:ignore]{}
    @#:case[(loop^stop p q) #:ignore]{}
 }}}}

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
        @#:case[parr]{Analagous to the the prevous case.}
        @#:case[par-both]{
         This follows directly by induction on both premises
         of this clause of the judgment.
         }
        @#:case[seq]{This follows directly from
         induction over the premise of the judgment.}
        @#:case[suspend]{analagous to the prevous case.}
        @#:case[trap]{analagous to the prevous case.}
        @#:case[loop^stop #:ignore]{TODO}]
}

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
