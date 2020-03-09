#lang scribble/base

@(require "../../lib/redex-rewrite.rkt"
          "../../lib/util.rkt"
          "../../lib/proofs.rkt"
          "can-props.rkt"
          (except-in "../../lib/proof-extras.rkt"
                     FV FV/e θ-get-S)
          redex/reduction-semantics
          redex/pict
          pict 
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
 @es[θ], or they are @es[0] by @proof-ref["sel-start"] and @proof-ref["Can-S-is-sound"].

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
        then @es[(compile done)] is constructive}]{
 @cases[#:of done
        #:language esterel/typeset
        #:induction
        @#:case[nothing]{@check[(assert-totally-constructive (compile-esterel (term nothing)))]}
        @#:case[(exit n)]{@check[(assert-totally-constructive (compile-esterel (term (exit 5))))]}
        @#:case[pause]{@check[(assert-totally-constructive (compile-esterel (term pause)))]}
        @#:case[(seq paused q-pure)]{
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
            and @proof-ref["activation-constructiveness"], @es[(compile q-pure)] is constructive.
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


@proof[#:label "blocked-is-nc"
       #:title "Block terms are non-constructive"
       #:statement @list{
        For all @es[(= r-pure_outer (ρ θr GO r-pure))],
        if @es[(blocked-pure θr GO hole r-pure)], and
        @es[(≃ (of (compile (ρ θr GO r-pure)) SEL) 0)]
        then @es[(compile r-pure_outer)] is non-constructive.}]{
 @sequenced{
  @#:step[inn]{By @proof-ref["blocked-implies-can-rho"],
   we know that there is some signal @es[S] such that
   @es[(L∈ S (->S (Can-θ (ρ θ_1 A p-pure) ·)))].}
  @#:step[bot]{By @proof-ref["all-bot"], we know that
   any initial configuration is @es[nc].}
  @#:step[bot2]{By @bot and @proof-ref["blocked-reachable-nc"],
 we know that all reachable states will be @es[all-bot].}
  @#:step[reach-bot]{By @inn and @bot2 we can conclude that
 there will be some signal wire @es[So] such all reachable states
 will have that signal wire set to @es[⊥].}
 @#:step[_]{By @reach-bot, the circuit is non-constructive.}}
}



@proof[#:label "all-bot"
       #:title "initial configurations are nc"
       #:statement @list{For all
        @es[(ρ θr GO p-pure)], if @es[(closed (ρ θr GO p-pure))] then
        all possible initial configurations
        @es[cs_0] are @es[(all-bot (ρ θr WAIT p-pure) · cs_0)].}]{
 As all internal and output wires start as @es[⊥], and all return code and signal wires
 start are internal or output, and @es[all-bot] only makes demands about internal and output
 wires being @es[⊥] this follows trivially.
 
 The change form @es[GO] to @es[WAIT] is only necessary to enforce the grammar of @es[p-pure],
 as @es[all-bot] does not observe  @es[A] ever this does not have any meaningful effect on our statements.
}



@proof[#:label "blocked-implies-can-rho"
       #:title "blocked implies can-rho"
       #:statement
       @list{For all @es[p], @es[θr], @es[A],
        if
        @es[(blocked-pure (parens θr) GO hole p-pure)]
        then there exits some @es[S] such that
        @es[(L∈ S (->S (Can-θ (ρ θr GO p-pure) ·)))]}]{
 This follows directly by induction over @es[blocked-pure],
 as the only bases cases involve either @es[(L∈ S (->S (Can-θ (ρ θr A p-pure) ·)))]
 or @es[(= A WAIT)], and the second case is excluded by our premises.
}





@proof[#:label "blocked-reachable-nc"
       #:title "reachable states from blocked terms non-constructive"
       #:statement @list{For all @es[(= r-pure_outer (ρ θr GO r-pure))],
                                 
        @es[cs_0], @es[cs_2],
                                 
        let @es[(= c (compile r-pure))]. Let @es[cs_0] be an
        initial state.

        if
        @es[(⟶* cs_0 cs_1)],
        @es[(≃ (of (compile (ρ θr GO r-pure)) SEL) 0)],
        @es[(blocked-pure θr GO hole r-pure)], and
        @es[(all-bot r-pure θ cs_0)]
        then @es[(all-bot r-pure θ cs_2)]}]{
 @sequenced{
  @#:step[all-bot1]{By the definition of @es[all-bot], there
   must exist some @es[θ], such that @es[(all-bot r-pure θ cs_0)].}
  @#:step[binds]{As @es[all-bot] follows the same structure as @es[Can-θ],
   we can use @proof-ref["Can-rho-S-is-sound"] to conclude that
   @es[(binds r-pure θ)].
  }
  @#:step[call]{
   By @all-bot1 and @binds we may use  @proof-ref["blocked-remains-nc"].
   Thus by induction on the length of the reduction sequence
   @es[(⟶* cs_0 cs_1)], we may conclude that @es[(all-bot r-pure θ cs_2)].}
}}

@proof[#:label "blocked-remains-nc"
       #:title "Blocked terms remain non-constructive"
       #:statement @list{For all @es[(= r-pure_outer (ρ θr GO (in-hole E-pure r-pure)))],
                                 @es[θ],
                                 @es[cs_1], and @es[cs_2],
                                 
        let @es[(= c (compile r-pure))].

        if
        @es[(⟶ cs_1 cs_2)],
        @es[(≃ (of (compile r-pure) SEL) 0)],
        @es[(binds (compile r-pure) θ)],
        @es[(blocked-pure θr GO E-pure r-pure)], and
        @es[(all-bot r-pure θ cs_1)]
        then @es[(all-bot r-pure θ cs_2)]}]{
  TODO update for new θ.
 @cases[#:of (blocked-pure θr GO E-pure r-pure)
        #:language esterel/typeset
        #:induction]{
                     
  @#:case[if]{
   Let @es[cs_1p] and @es[cs_2p] be the substates
   that correspond to @es[p-pure] in @es[cs_1] and @es[cs_2] respectively. Let
   @es[cs_1q] and @es[cs_2q] be defined similarly.
   
   @sequenced{
    @#:step[inθ]{
     By the definition of @es[blocked-pure], we know that
     @es[(L∈ S (->S (Can-θ (ρ θr A (in-hole E (present S p q))) ·)))].
    }
    @#:step[bot]{
     By the definition of @es[blocked-pure], we know that @es[(θ-ref-S θr S unknown)].
    }
    @#:step[inn]{By @es[Canθₛ⊆Canₛ] and @inθ, we know that
     @es[(L∈ S (->S (Can (in-hole E (present S p q)) θr)))].
    }
    @#:step[bad]{By @inn, @proof-ref["S-maintains-across-E"] and our premise that
     @es[(all-bot r-pure θr cs_1)],
     we know that @es[(= (of cs_1 Si) (of cs_1 So) ⊥)].}
    @#:step[GO-1]{By @proof-ref["GO-maintains-across-E"], we know that
     @es[(= (of cs_1i GO) 1)].}
    @#:step[S-bot]{By @proof-ref["S-maintains-across-E"] and @bad, we know that
     @es[(= (of cs_1i Si) ⊥)].}
   
    @#:step[GO-bot]{By the definition of @es[compile], @GO-1, and @S-bot,
     we know that @es[(= (of cs_1p GO) ⊥)] and @es[(= (of cs_1q GO) ⊥)].}
    @#:step[sub]{By the definition of @es[all-bot], @es[all-bot-rec], @bot and @inn we know that
     @es[(all-bot p-pure θr cs_1p)] and @es[(all-bot p-pure θr cs_1q)].}
    @#:step[rec]{By our premise that @es[(≃ (of (compile r-pure) SEL) 0)],
     @es[(binds (compile r-pure) θr)],
     @GO-bot, and @sub, we may use @proof-ref["adequacy-of-can"] to conclude
     @es[(all-bot p-pure θr cs_2p)] and @es[(all-bot p-pure θr cs_2q)].}
    @#:step[rec2]{By the definition of @es[compile], the output signals
     are either @es[or]ed from both branches. For any signal that is in @es[Can] of
     the other branch it must either be in @es[Can] of the other branch, and therefore
     by @rec be @es[⊥], or it is not in @es[Can], and therefore by @proof-ref["Can-S-is-sound"],
     and therefore must be @es[0]. Therefore is a signal is in @es[Can] of the overall term,
     it is @es[⊥] in @es[cs_2]. The same argument holds for the return codes.}
    @#:step[final]{By @rec and @rec2 we may conclude that
     @es[(all-bot (present S p-pure q-pure) θr cs_2)].}
   
  }}
  @#:case[emit-wait]{
  This clause is not possible, as we specified our @es[A] to be @es[GO].}
  @#:case[suspend]
  @#:case[trap]
  @#:case[seq]
  @#:case[parl]
  @#:case[parr]
  @#:case[par-both]
  @#:case[loop^stop #:ignore]
 }
}



@proof[#:label "adequacy-of-can"
       #:title "Adequacy of Can"
       #:interpretation @list{
        The core idea of this proof is that not only is
        @es[Can] sound, but is adequite to tell us when wires are @es[⊥].
        Now this is subtle, as wires can be set to @es[1] without @es[Can] knowing,
        as it only analizes
        what @italic{Can} happen, not what @italic{Must} happen. Therefore this
        proof requires that @es[GO] is @es[⊥], which is essense says that @italic{nothing}
        must happen, as @es[GO] reprenents @italic{must} in the circuit.}
       #:statement
       @list{For all @es[r-pure], @es[θ], @es[cs_1], @es[cs_2]
        let @es[(= c (compile r-pure))],
        if @es/unchecked[(⟶ cs_1 cs_2)],
        @es[(≃ (of (compile r-pure) SEL) 0)],
        @es[(binds (compile r-pure) θ)],
        @es[(= (of cs_1 GO) ⊥)], and
        @es[(all-bot r-pure θ cs_1)]
        then
        @es[(all-bot r-pure θ cs_2)]}]{
 @cases[#:induction
 #:of r-pure
 #:language esterel/typeset]{
  @#:case[nothing]{
   @sequenced{
    @#:step[S]{@es[(->S (Can r-pure θ))] is empty, therefore
     @es[(all-bot-S nothing θ cs_2)] vacuously holds.}
    @#:step[K]{@es[(= (->K (Can r-pure θ)) (L1set 0))], therefore
     we must only show that @es[K0] is @es[⊥]. This holds trivially by the
     definition of @es[compile] and the fact that @es[(= (of c_s1 GO) ⊥)].
     Therefore @es[(all-bot-S nothing θ cs_2)] also holds.}
   @#:step[rec]{@es[(all-bot-rec nothing θ cs_2)] trivially holds.}
    @#:step[res]{By @S, @K, @rec, @es[(all-bot nothing θ cs_2)] holds.}}
  }
  @#:case[pause]{This is analagous to the previous clause.}
  @#:case[(exit n)]{This is analagous to the previous clause.}
  @#:case[(emit S_e)]{This clause is analgous to the previous clauses, except
   the argument for @es[Kn] is repeated for @es[S_e].}
  @#:case[(trap p-pure)]{
   let @es[cs_1i] and @es[cs_2i] be the substates of @es[cs_1] and @es[cs_2]
   which corrispond to @es[(compile p-pure)].
   @sequenced{
    @#:step[rec]{By the defintion of @es[all-bot] and @es[all-bot-rec], we know
    that @es[(all-bot p-pure θ cs_1i)].}
    @#:step[go]{By the defintion of @es[compile] we know that
     the inner @es[GO] wire is unchanged, therefore it is @es[⊥].}
    @#:step[end]{By the defintion of @es[compile] the signals
    are passed in unchanged, therefore @es[(binds (compile p-pure) θ)]}
    @#:step[sel]{By the defintion of @es[compile] @es[SEL] is unchanged,
     therefore @es[(≃ (of (compile p-pure) SEL) 0)].}
    @#:step[ind]{If the step from @es[cs_1] to @es[cs_2] changes the substate                  
     By @rec through @sel we can invoke our induction hypothesis
     to learn that @es[(all-bot r-pure θ cs_2i)] for the inner circuit. Otherwise
     the substate remains unchanged therefore we still have @es[(all-bot r-pure θ cs_2i)]}
    @#:step[comp]{By the definition of compile the output
     signals remain unchanged. Therefore @ind gives us that @es[(all-bot-S r-pure θ cs_2)]}
    @#:step[K]{Now we inspect the return codes and their wires. To show @es[(all-bot-S r-pure θ cs_2i)]
     from @es[(all-bot-S p-pure θ cs_2)] (by @ind),
     we must case on each @es[(L∈ n (->K (Can p-pure θ)))]:
     @cases[#:of/count n 4
            #:simple-cases
            #:language esterel/typeset]{
      @#:case[(= n 0)]{In this case we know that @es[(= (of cs_2i K0) ⊥)], and @es[(L∈ 0 (->K (Can r-pure θ)))].
       We have two subcases, either, @es[(L∈ 2 (->K (Can p-pure θ)))], in which case
       by @ind we know that @es[(= (of cs_2i K2) ⊥)], or @es[(L¬∈ 2 (->K (Can p-pure θ)))],
       in which case @es[(≃ (of (compile p-pure) K2) 0)]. In either case the only possible value
       for @es[(= (of cs_2 K0) ⊥)] is @es[⊥].}
      @#:case[(= n 1)]{In this case @es[K1] is pass out unchanged, thus it must still be @es[⊥]. }
      @#:case[(= n 2)]{This follow by the same arugment as the case for @es[0].}
      @#:case[(> n 3)]{In this case
       In this case @es[Kn] is pass out unchanged, but renamed to @es[Kn-1].
       This matches exactly with the behavior of @es[Can], therefore the wire will remain @es[⊥]}}}
    @#:step[_]{by @ind, @comp, and @K, we may conclude that @es[(all-bot r-pure θ cs_2)]}
                    
  }}
  
  @#:case[(suspend p-pure S_s)]{This case follows by a similar argument to @es[trap], but relies
   on @es[(≃ (of (compile r-pure) SEL) 0)] instead of reasoning about the @es[or] of @es[K0] and @es[K2].}
  
  @#:case[(present S_f p-pure q-pure)]{
                                       
   Let @es[cs_1p] and @es[cs_2p] be the substates of @es[cs_1] and @es[cs_2] that corrispond
   to @es[(compile p-pure)]. Let @es[cs_1q] and @es[cs_2q] be defined similarly.
   @cases[#:of (θ-get-S θ S_f)
          #:drawn-from status
          #:language esterel/typeset]{
    @#:case[present]{
     @sequenced{
      @#:step[sup]{By the definition of @es[all-bot] and @es[all-bot-rec],
       we know that @es[(all-bot p-pure θ cs_1p)].}
      @#:step[go-zero]{By @es[(binds (compile r-pure) θ)] we know that
       @es[(≃ (of (compile q) GO) 0)].}
      @#:step[sel-zero]{By @es[(≃ (of (compile r-pure) SEL) 0)] and the definition
       of @es[compile] we know that @es[(≃ (of (compile p-pure) SEL) 0)]
       and @es[(≃ (of (compile q-pure) SEL) 0)].}
      @#:step[out-zero]{By @go-zero, @sel-zero, and @proof-ref["activation-condition"]
       we know that all outputs of @es[(compile q-pure)] are @es[0].}
      @#:step[go-bot]{By the definition of @es[compile] we know that
       @es[(= (of cs_1p GO) ⊥)].}
      @#:step[binds]{As the signals are passed in unchanged we may conlcude that
       @es[(binds (compile p-pure) θ)].}
      @#:step[rec]{By @sup, @go-bot and @sel-zero, @binds and our induction hypothesis we know that
       @es[(all-bot p-pure θ cs_2p)]}
      @#:step[build]{By @out-zero we know that the outputs of the circuit are given by the output
       of @es[(compile p-pure)].}
      @#:step[_]{By @build and @rec we know that @es[(all-bot p-pure θ cs_2)]}}}
    @#:case[absent]{This case follows by an analagous arugment to the previous one.}
    @#:case[unknown]{
     @sequenced{
      @#:step[∉]{
       If @es[(L∈ S_f (->K (Can r-pure θ)))], we may repeat the
       argument from the @es[absent] case, by @proof-ref["Can-S-is-sound"].
       Therefore we must show this for @es[(L¬∈ S_f (->K (Can r-pure θ)))].}
      @#:step[sub]{By the definition of @es[all-bot] and @es[all-bot-rec],
       we know that @es[(all-bot p-pure θ cs_1p)]
       and @es[(all-bot q-pure θ cs_1q)].}
      @#:step[bot]{By @∉, and @es[(all-bot p-pure θ cs_1)],
       we know that @es[(= (of cs_1 So_f) ⊥)].}
      
      @#:step[inner-bot]{
       By @bot and
       @es[(= (of cs_1 GO) ⊥)], and the definition of @es[compile] we can conclude
       that @es[(= (of cs_1p GO) ⊥)] and @es[(= (of cs_1q GO) ⊥)]}
      @#:step[sel-zero]{By @es[(≃ (of (compile r-pure) SEL) 0)] and the definition
       of @es[compile] we know that @es[(≃ (of (compile p-pure) SEL) 0)]
       and @es[(≃ (of (compile q-pure) SEL) 0)].}
      @#:step[binds]{As the signals are passed in unchanged we may conlcude that
       @es[(binds (compile p-pure) θ)] and @es[(binds (compile q-pure) θ)].}
      @#:step[rec]{By @sel-zero, @binds, @inner-bot, and @sub we may conclude
       that @es[(all-bot p-pure θ cs_2p)] and @es[(all-bot q-pure θ cs_2q)]}
      @#:step[assemble]{By the definition of @es[compile], the output signals
      are either @es[or]ed from both branches. For any signal that is in @es[Can] of
      the other branch it must either be in @es[Can] of the other branch, and therefore
      by @rec be @es[⊥], or it is not in @es[Can], and therefore by @proof-ref["Can-S-is-sound"],
      and therefore must be @es[0]. Therefore is a signal is in @es[Can] of the overall term,
      it is @es[⊥] in @es[cs_2]. The same argument holds for the return codes.}
      @#:step[final]{By @rec and @assemble we may conclude that @es[(all-bot r-pure θ cs_2)].}
     }
  }}}
  @#:case[(seq p-pure q-pure)]{
   Let @es[cs_1p] and @es[cs_2p] be the substates of @es[cs_1] and @es[cs_2] that corrispond
   to @es[(compile p-pure)]. Let @es[cs_1q] and @es[cs_2q] be defined similarly.

   @sequenced{
              
    @#:step[sub]{By the definitions of @es[all-bot] and @es[all-bot-rec], we have two cases but
     both let us conclude that @es[(all-bot p-pure θ cs_1p)].}
    @#:step[go-bot]{As @es[GO] is sent directly to @es[(compile p-pure)],
     we may conclude that @es[(= (of cs_1i GO) ⊥)].}
    @#:step[binds]{By the definition of @es[compile], all of the signals
     are broadcast to the both subcircuits, thus we may conclude that
     @es[(binds (compile p-pure) θ)] and @es[(binds (compile q-pure) θ)].}
    @#:step[sel-zero]{By the definition of @es[compile] and the premise that
                                           
     @es[(≃ (of (compile r-pure) SEL) 0)] we may conclude that
     @es[(≃ (of (compile p-pure) SEL) 0)] and @es[(≃ (of (compile q-pure) SEL) 0)].}
    @#:step[rec1]{By @sel-zero, @sub, @go-bot, and @binds we may conclude that
     @es[(all-bot p-pure θ cs_2p)].}
    @#:step[split]{
     Following the structure of @es[Can] and @es[all-bot-rec], we have:
     @cases[#:of/count (L∈ 0 (->K (Can p-pure θ))) 2
            #:simple-cases
            #:language esterel/typeset]{
      @#:case[(L¬∈ 0 (->K (Can p-pure θ)))]{
       @sequenced{
        @#:step[k0-zero]{By @proof-ref["Can-K-is-sound"],
         we can conclude that @es[(≃ (of (compile p-pure) K0) 0)].}
        @#:step[go-zero]{By @k0-zero and the definition of @es[compile],
         we can conclude that @es[(≃ (of (compile q-pure) GO) 0)].}
        @#:step[out-zero]{By @go-zero, the premise that @es[(≃ (of (compile r-pure) SEL) 0)],
         and @proof-ref["activation-condition"], we may conclude that all the outputs
         of @es[(compile q-pure)] are @es[0].}
        @#:step[bots]{By the definition of @es[compile] and @out-zero, all signals and control wires
         will have their value defined by @es[(compile p-pure)]. Thus we may conclude that
         @es[(all-bot-S r-pure θ cs_2)] and @es[(all-bot-n r-pure θ cs_2)].}
        @#:step[assemble]{By @bots and @rec1 we may conclude that @es[(all-bot r-pure θ cs_2)].}
      }}
   
      @#:case[(L∈ 0 (->K (Can p-pure θ)))]{
       @sequenced{
        @#:step[sub1]{By the definitions of @es[all-bot] and @es[all-bot-rec] we may
         conclude that @es[(all-bot q-pure θ cs_2p)].}
        @#:step[k0-bot]{By @sub and the premise of this case we may conclude that
         @es[(= (of cs_1p K0) ⊥)].}
        @#:step[go-bot]{By @k0-bot and the definition of @es[compile] we may conclude that
         @es[(= (of cs_1q GO) ⊥)].}
        @#:step[rec2]{By @sel-zero, @binds, @go-bot, and @sub1 we may conclude that
         @es[(all-bot p-pure θ cs_2q)].}
        @#:step[build]{By the same argument as in the @es[present] case, using
         @rec1 and @rec2, we may conclude that @es[(all-bot-S r-pure θ cs_2)]
         and @es[(all-bot-n r-pure θ cs_2)].}
        @#:step[final]{By @rec1, @rec2, and @build we may conclude that
         @es[(all-bot r-pure θ cs_2)].}
      }}
  }}}}
  
  @#:case[(par p-pure q-pure)]{This case proceeds by a similar argument
   to the previous two cases, except that @es[GO] is broadcast to both subcircuits,
   therefore no argument is needed to show that the @es[GO] of the subcircuits
   are @es[⊥].}
  
  @#:case[(signal S_s p-pure)]{
                               
   Let @es[cs_1i] and @es[cs_2i] be the substates of @es[cs_1] and @es[cs_2]
   which corrispond to @es[(compile p-pure)].
   @sequenced{
    @#:step[sel-0]{By the definition of @es[compile], the @es[SEL] wire is unchanged, thus we may conclude
     that @es[(≃ (of (compile p-pure) SEL) 0)].}
    @#:step[go-bot]{By the definition of @es[compile], the @es[GO] wire is unchanged, thus we may conclude
     that @es[(= (of cs_1i GO) ⊥)].}
    @#:step[split]{By the definitions of @es[Can], and @es[all-bot-rec], we have
     the following cases:
     @cases[#:of/count (L∈ S_s (->S (Can p-pure (<- θ (mtθ+S S_s unknown))))) 2
            #:simple-cases
            #:language esterel/typeset]{

      @#:case[(L∈ S_s (->S (Can p-pure (<- θ (mtθ+S S_s unknown)))))]{
       @sequenced{
        @#:step[sub]{By the definitions of @es[all-bot] and @es[all-bot-rec],
         we know that @es[(all-bot p-pure (<- θ (mtθ+S S unknown)) cs_1i)].}
        @#:step[binds]{As @es[(<- θ (mtθ+S S_s unknown))] puts no restrictions on the values
         for @es[S_s], and the remainder of signal wires are passed in unchanged, we may conclude
         that @es[(binds p-pure (<- θ (mtθ+S S_s unknown)))].}
        @#:step[rec]{By @sub, @binds, @sel-0, and @go-bot, we may conclude that
         @es[(all-bot p-pure (<- θ (mtθ+S S unknown)) cs_2i)].}
        @#:step[assemble]{As all signal wires that are not @es[S_s]
         and all control wires are passed out unchanged, and as @es[S_s] is removed from the output of @es[Can],
         we may use @rec to conclude that @es[(all-bot-S r-pure θ cs_2)] and @es[(all-bot-n r-pure θ cs_2)].}
        @#:step[final]{By @rec and @assemble we may conclude that @es[(all-bot r-pure θ cs_2)].}
      }}
      @#:case[(L¬∈ S_s (->S (Can p-pure (<- θ (mtθ+S S unknown)))))]{
       @sequenced{
        @#:step[sub]{By the definitions of @es[all-bot] and @es[all-bot-rec],
         we know that @es[(all-bot p-pure (<- θ (mtθ+S S absent)) cs_1i)].}
        @#:step[binds-1]{By @proof-ref["Can-S-is-sound"], we may conclude that
        @es[(≃ (of (compile p-pure) So_s) 0)].}
        @#:step[binds-2]{By @binds-1 and the defintion of @es[complie] (which links @es[So_] to @es[Si_s]),
         we may conclude that @es[(≃ (of (compile p-pure) Si_s) 0)].}
        @#:step[binds]{As the remainder of the signal wires are unchanged, we may conclude that
         @es[(binds (compile p-pure) (<- θ (mtθ+S S absent)))]}
        @#:step[rec]{By @sub, @binds, @sel-0, and @go-bot, we may conclude that
         @es[(all-bot p-pure (<- θ (mtθ+S S absent)) cs_2i)].}
        @#:step[final]{By the same arguments in the previous subcase,
         we may conclude that @es[(all-bot r-pure θ cs_2)].}
       }
    }}}
    
  }}
  @#:case[(ρ θr WAIT p-pure)]{
   As this case is essentially the same as many nested @es[signal]s, it
   follows by a similar argument to the previous case.}
  @#:case[(loop p) #:ignore]
  @#:case[(loop^stop p q) #:ignore]
}}





@section["Auxiliary Lemmas"]

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
        @#:case[(loop^stop E_3 q) #:ignore]
        ]

}