#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
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


@title[#:style paper-title-style]{Adequacy}

The goal of this section is to prove computational adequacy of the calculus
with respect to the circuit translation.

@section["positive"]


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
            by @proof-ref["done-is-k1"] we know that, for any possible
            binding evironment @es[θ], @es[(L¬∈ 0 (->K (Can paused θ)))].
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

            By @go-1, @kill-0, @susp-0, @kill-0, and @θ-binds,
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
        @#:case[(loop^stop paused q)]{TODO}
        ]}


@proof[#:label "blocked-implies-can-rho"
       #:title "blocked implies can-rho"
       #:statement
       @list{For all @es[p], @es[E], @es[θ_1], @es[θ_2], @es[A],
        if
        @es[(blocked-pure (parens (<- θ_1 θ_2)) A hole (in-hole E p))]
        then there exits some @es[S] such that
        @es[(L∈ S (->S (Can-θ (ρ θ_1 A (in-hole E p)) θ_2)))]}]{
 TODO
}

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
        @#:case[if]{
          TODO fill out.
          True by @es[Canθₛ⊆Canₛ]}
        @#:case[emit-wait]{
          TODO fill out.
          True by @es[canₛ-capture-emit-signal].}
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
        @#:case[loop^stop]{TODO}]
}

@proof[#:label "blocked-rho-gives-bot"
       #:title "blocked and can-rho give non-constructiveness"
       #:statement
       @list{For all @es[θ_1], @es[θ_2], @es[p], @es[E], @es[S]
                     
        if @es[(blocked-pure (parens (<- θ_1 θ_2)) GO hole (in-hole E p))],
        @es[(distinct (Ldom θ_1) (Ldom θ_2))],
        @es[(binds (compile (in-hole E p)) (parens (<- θ_1 θ_2)))],
        and @es[(L∈ S (->S (Can-θ (ρ θ_1 GO (in-hole E p)) θ_2)))]
        
        then @es[(= (of (compile (in-hole E p)) S) ⊥)]}]{
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
                to conclude that @es[(= (of (compile (in-hole E p)) S) ⊥)].}
           }}}}
           @#:case[(= S S_1)]{TODO
            }}}]}
       


@proof[#:label "blocked-can-gives-bot"
       #:title "blocked and can give non-constructiveness"
       #:statement
       @list{For all @es[p], @es[θ], @es[E], @es[S]
                     
        if @es[(blocked-pure θ GO hole (in-hole E p))],
        @es[(binds (compile (in-hole E p)) θ)],
        and @es[(L∈ S (->S (Can (in-hole E p) θ)))]
        
        then @es[(= (of (compile (in-hole E p)) S) ⊥)]}]{
 @cases[#:language esterel/typeset
        #:of/count (Ldom θ) 2
        #:induction
        @#:case[(L0set)]{TODO}
        @#:case[_]{TODO}]
}

@proof[#:label "blocked-respects-can"
       #:title "blocked respects Can"
       #:statement
       @list{For all @es[p], @es[E], @es[θ],
        @es[S],
        
        if @es[(blocked-pure θ A E p)],
        @es[(= (θ-get-S θ S) unknown)]
        and @es[(L¬∈ S (->S (Can-θ (ρ θ A (in-hole E p)) ·)))]

        then @es[(blocked-pure (<- θ (mtθ+S S absent)) A hole (in-hole E p))]}]{
 @cases[#:language esterel/typeset
        #:of (blocked-pure θ A E p)
        #:induction
        @#:case[if]{This this case we can invoke
          @proof-ref["can-rho-idempotent"] using @es[θ] as
          @es[θ_1] and @es[·] as @es[θ_2] to obtain the needed
          premise to reconstruct the proof that the term is blocked.}
        @#:case[emit-wait]{As this case does not rely
          on @es[θ], the theorem still holds.}
        @#:case[parl]{TODO}
        @#:case[parr]{TODO}
        @#:case[seq]{TODO}
        @#:case[suspend]{TODO}
        @#:case[trap]{TODO}
        @#:case[par-both]{TODO}
        @#:case[loop^stop]{TODO}]
}

@proof[#:title "values and blocked are disjoint"
       #:label "vb-disjoint"
       #:statement
       @list{For all @es[done], @es[θ], @es[E], @es[A],
        not @es[(blocked-pure θ A E done)]}]{
 TODO
}

@proof[#:title "blocked-final"
       #:label "blocked is final"
       #:statement
       @list{for all @es[p], @es[θ], @es[A], @es[E],
        @es[p_1], @es[θ_1], @es[A_1], and @es[E_1],
                     
        if @es[(blocked-pure θ A E p)] and @es[(⟶ (ρ θ A (in-hole E p)) (ρ θ_1 A_1 (in-hole E_1 p_1)))]
        then @es[(blocked-pure θ_1 A_1 E_1 p_1)].}]{

 TODO

}

@proof[#:title "blocked-separable"
       #:label "blocked is separable"
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
        @#:case[(suspend E_3 S)]{TODO}
        @#:case[(trap E_3)]{TODO}
        @#:case[(seq E_3 q)]{TODO}
        @#:case[(par E_3 q)]{TODO}
        @#:case[(par p E_3)]{TODO}
        @#:case[(loop^stop E_3 q)]{TODO}
        ]

}

@section["Negative"]

@proof[#:title "Not values must step"
       #:label "nv-must-step"
       #:interpretation @list{This
        proof is the contrapositive of the notion
        that ``terms that do not reduce, modulo @rule["par-swap"],
        are values''. As we are working in a closed universe
        with decidable properties, the contrapositive will
        give us our}
       #:statement
       @list{For all @es[(= q (ρ θ A (in-hole E p)))],
        If @es[(closed q)] and
        @es/unchecked[(L¬∈ p done)] and
        @es[(not-blocked θ A E p)]
        then there exists
        some @es[θ_o] and @es[p_o]
        such that
        @es[(⟶^r q (ρ θ_o A (in-hole E p_o)))]
        or
        there exists some @es[r]
        such that @es[(⟶^s q (⟶^r (ρ θ A (in-hole E r)) (ρ θ_o A (in-hole E p_o))))]}]{
 @cases[#:of p-pure
        #:induction
        #:language esterel/typeset
        ;; terminal cases
        @#:case[nothing]{ This case violates our hypothesis that @es/unchecked[(L¬∈ p done)]. }
        @#:case[pause]{ This case violates our hypothesis that @es/unchecked[(L¬∈ p done)]. }
        @#:case[(exit n)]{ This case violates our hypothesis that @es/unchecked[(L¬∈ p done)]. }
        @#:case[(emit S)]{

          @sequenced{
                     
           @#:step[A]{
            By the definition of @es[closed], it must be the case that @es[(= A GO)]}
           @#:step[bound]{
                          
            As @es[(closed q)] and as @es[E] contains no binders,
            It must be the case that @es[(L∈ S (Ldom θ))].

           }
           @#:step[final]{

            Thus let @es[(= θ_o (<- θ (mtθ+S S present)))] and
            @es[(= p_o nothing)]. Let the step we take be @rule["emit"].

           }
         }}
        
        ;; E cases
        @#:case[(seq p_o q_o)]{
          @sequenced{

           @#:step[paused]{
                           
            By the definition of @es[done], we know that
            @es/unchecked[(L¬∈ p_o paused)].
                     
           }

           @#:step[blocked]{

            By the definition of @es[blocked], we know that
            @es[(not-blocked θ A (in-hole E (seq hole q_o)) p_o)].

           }

           @#:step[_]{

            We by @paused know that @es[p_o] is not @es[paused], but
            we must consider of @es[p_o] is @es[done]. By the definition
            of @es[done], this gives:

            @cases[#:of/count (L∈ p_o stopped) 2
                   #:simple-cases
                   #:no-check
                   #:language esterel/typeset]{

             @#:case[(L∈ p_o stopped)]{
              @cases[#:of p_o
                     #:drawn-from stopped
                     #:language esterel/typeset]{
                                                
               @#:case[nothing]{

                In this case, @es[(= θ_o θ)],
                the resulting @es[(= p_o q_o)],
                and we step by  @rule["seq-done"].
                
               }
                
               @#:case[(exit n)]{

                In this case, @es[(= θ_o θ)],
                the resulting @es[(= p_o (exit n))],
                and we step by  @rule["seq-exit"].
                
               }

             }}
             @#:case[(L¬∈ p_o stopped)]{
              @sequenced{
                        
               @#:step[done]{As we know that
                @es/unchecked[(L¬∈ p_o stopped)] and @es/unchecked[(L¬∈ p_o paused)],
                we know that @es/unchecked[(L¬∈ p_o done)].}

               @#:step[_]{
                          
                By @done, @paused, and @blocked, we can use our induction
                hypothesis on @es[p_o] and @es[(in-hole E (seq hole q_o))].
                As the result we get back differs from what we need only in
                that @es[(seq hole q_o)] was shifted from @es[p_o] to
                @es[E], we can shift it back an return the result unchanged.
                
         }}}}}}}
        
        @#:case[(par p_o q_o)]{
          There is only one way for a @es[par] to @es[done], thus we know that
          @es/unchecked[(not (parens (and (L∈ p_o paused) (L∈ q_o paused))))].           
                                                     
          There are three ways for an @es[par] to be @es[blocked], thus
          we know that
          
          @(let ()
             (define b1 (es/unchecked (parens (and (blocked-pure θ A (in-hole E (par hole q_o)) p_o) (blocked-pure θ A (in-hole E (par p_o hole)) q_o)))))
             (define b2 (es/unchecked (parens (and (blocked-pure θ A (in-hole E (par hole q_o)) p_o) (L∈ q_o done)))))
             (define b3 (es/unchecked (parens (and (L∈ p_o done) (blocked-pure θ A (in-hole E (par p_o hole)) q_o)))))
             (define on (hbl-append @es[not] (words "(")))
             (vl-append
             (hbl-append on b1)
             (hbl-append (ghost on) @es[or])
             (hbl-append (ghost on) b2)
             (hbl-append (ghost on) @es[or])
             (hbl-append (ghost on) b3 (words ")"))))

          On the whole this gives us the following expression:
          
                                   
          @(let ()
             (define pause @es/unchecked[(not (parens (and (L∈ p_o paused) (L∈ q_o paused))))])
             (define b1 (es/unchecked (parens (and (blocked-pure θ A (in-hole E (par hole q_o)) p_o) (blocked-pure θ A (in-hole E (par p_o hole)) q_o)))))
             (define b2 (es/unchecked (parens (and (blocked-pure θ A (in-hole E (par hole q_o)) p_o) (L∈ q_o done)))))
             (define b3 (es/unchecked (parens (and (L∈ p_o done) (blocked-pure θ A (in-hole E (par p_o hole)) q_o)))))
             (define on (hbl-append @es[not] (words "(")))
             (vl-append
              pause
              @es/unchecked[and]
              (hbl-append on b1)
              (hbl-append (ghost on) @es[or])
              (hbl-append (ghost on) b2)
              (hbl-append (ghost on) @es[or])
              (hbl-append (ghost on) b3 (words ")"))))
                                   
          
                                                                                            
          Note that a term which is @es[paused] is also @es[done]. Given this, we can find the the disjuctive
          normal form of the above expression, giving us four cases:

          @es/unchecked[(and (not-blocked θ A (in-hole E (par hole q_o)) p_o) (not-blocked θ A (in-hole E (par p_o hole)) q_o) (L¬∈ p_o paused))]
          
          @es/unchecked[(and (not-blocked θ A (in-hole E (par hole q_o)) p_o) (not-blocked θ A (in-hole E (par p_o hole)) q_o) (L¬∈ q_o paused))]
          
          @es/unchecked[(and (not-blocked θ A (in-hole E (par hole q_o)) p_o) (L¬∈ p_o done))]
          
          @es/unchecked[(and (not-blocked θ A (in-hole E (par p_o hole)) q_o) (L¬∈ q_o done))]
          
          @cases[#:of/count the\ above 4
                 #:simple-cases
                 #:no-check
                 #:language esterel/typeset]{
           @#:case[(and (not-blocked θ A (in-hole E (par hole q_o)) p_o) (not-blocked θ A (in-hole E (par p_o hole)) q_o) (L¬∈ q_o paused))]{
            In this case we have @sequenced{

             @#:step[blocked]{We know
              that @es[(not-blocked θ A (in-hole E (par hole p_o)) q_o)]}
             @#:step[paused]{We know that @es/unchecked[(L¬∈ q_o paused)]}
             @#:step[subcases]{
              @cases[#:of/count (L∈ q_o stopped) 2
                     #:simple-cases
                     #:no-check
                     #:language esterel/typeset]{
               @#:case[(L∈ q_o stopped)]{
                @cases[#:of/count (L∈ p_o done) 2
                       #:language esterel/typeset
                       #:no-check
                       #:simple-cases]{
                 @#:case[(L∈ p_o done)]{
                  @cases[#:of (p_o q_o)
                         #:tuplize
                         #:language esterel/typeset
                         #:drawn-from (done stopped)]{

                   @#:case[(nothing (exit n_2))]{
                                                 
                    In this case let @es[(= θ_o θ)] and @es[(= p_o (exit n_2))],
                    and our reduction be a single use of @rule["par-nothing"].

                   }
                   @#:case[((exit n_1) (exit n_2))]{
                    In this case let @es[(= θ_o θ)] and @es[(= p_o (exit (max n_1 n_2)))],
                    and our reduction be a single use of @rule["par-2exit"].
                    
                   }
                   @#:case[(paused (exit n_2))]{
                   
                    In this case let @es[(= θ_o θ)], @es[(= p_o (exit n_2))],
                    and @es[(= r (par (exit n_2) paused))]. Our reductions
                    are one use of @rule["par-swap"] and one use of @rule["par-1exit"].

                   }
                   @#:case[(done nothing)]{
                                           
                    This is analogues to the previous case, but using @rule["par-nothing"] instead
                    of @rule["par-1exit"].

                   }

                  }
                 }
                 @#:case[(L¬∈ p_o done)]{

                  In this case we may invoke our induction hypothesis on
                  @es[p_o], as we know
                  @es[(not-blocked θ A (in-hole E (par hole q_o)) p_o)] and
                  @es/unchecked[(L¬∈ p_o done)]. As usual we may reassemble
                  the result of the induction by shifting one frame of the
                  @es[E] back over and using the same reductions.

                 }
               }}
               @#:case[(L¬∈ q_o stopped)]{
                @sequenced{
                 @#:step[not-done]{As we know @es/unchecked[(L¬∈ q_o stopped)] and
                  @es/unchecked[(L¬∈ q_o paused)], we know @es/unchecked[(L¬∈ q_o done)].}
                 @#:step[exists]{

                  We may invoke our induction hypothesis on
                  @es[(in-hole E (par p_o hole))] and @es[q_o]. This gives us
                  that exists some @es[θ_o1] and @es[p_o1] using @blocked and @not-done such that
                  @es[(⟶^r q (ρ θ_o1 A (in-hole E p_o1)))] or there exists
                  some @es[r] such that
                  @es[(⟶^s q (⟶^r r (ρ θ_o1 A (in-hole (in-hole E (par p_o hole)) p_o1))))].

                 }
                 @#:step[final]{

                  In this case we can take the result from
                  @exists and shift The @es[(par p_o hole)] over to @es[p_o1].
                  Giving us a resulting @es[(= p_o2 (par p_o p_o1))], and an
                  unchanged @es[θ_o1]. As the overall terms have not changed,
                  the reductions form @exists are unchanged. Thus we return those
                  reductions.

           }}}}}}}
                                 
           @#:case[(and (not-blocked θ A (in-hole E (par hole q_o)) p_o) (not-blocked θ A (in-hole E (par p_o hole)) q_o) (L¬∈ p_o paused))]{

            This case is the same as the previous, but finding a
            reduction in the other branch. As in this case in the
            subcase where we concider one branch begin @es[done] and the
            other being @es[stopped], @es[p_o] is the branch that is
            @es[stopped] we do not need to use @es[⟶^s].

           }
            
           @#:case[(and (not-blocked θ A (in-hole E (par hole q_o)) p_o) (L¬∈ p_o done))]{
                                                                                          
            As we know that @es[p_o] is not @es[blocked] or @es[done]
            we can induct on @es[p_o] and
            @es[(in-hole E (par hole q_o))]. As usual we may reassemble
            the result of the induction by shifting one frame of the
            @es[E] back over and using the same reductions.
               
           }
            
           @#:case[(and (not-blocked θ A (in-hole E (par p_o hole)) q_o) (L¬∈ q_o done))]{

            This case is the same as the previous, but finding a reduction
            in the other branch.

         }}}
        @#:case[(trap p_o)]{
          @sequenced{
           @#:step[paused]{By the definition of @es[done]
            we know that @es/unchecked[(L¬∈ p_o paused)].
           }
           @#:step[blocked]{By the definition of @es[blocked]
            we know that @es[(not-blocked θ A (in-hole E (trap hole)) p_o)].}
           @#:step[_]{
            @cases[#:of/count (L∈ p_o stopped) 2
                   #:language esterel/typeset
                   #:no-check
                   #:simple-cases]{
             @#:case[(L∈ p_o stopped)]{In this case we may reduced by @rule["trap"].}
              @#:case[(L¬∈ p_o stopped)]{
             @sequenced{
               @#:step[done]{Given @es/unchecked[(L¬∈ p_o stopped)] and @paused,
                we know that @es/unchecked[(L¬∈ p_o done)]}
                @#:step[_]{Given @done and @blocked we may use our induction hypothesis
               on @es[p_o] and @es[(in-hole E (trap hole))]. As usual we may reassemble
               the result of the induction by shifting one frame of the @es[E] back over and
               using the same reductions.}
             }}}}}}
        @#:case[(suspend p_o S)]{This case is analogous to the previous case
          but reducing by @rule["suspend"] rather than @rule["trap"].}
        
        ;; the rest
        
        @#:case[(signal S p_o)]{
          In this case we may reduce by @rule["signal"].}
        @#:case[(ρ θ_o A_o p_o)]{
          In this case we may reduce by @rule["merge"],
          as by @es[(closed q)] we know that @es[(= A GO)],
          which must be @es[A->=] @es[A_o]. }
        @#:case[(present S p_o q_o)]{
          By @es[(closed q)] and @es[E] not containing
          any binders we know that @es[(L∈ S (Ldom θ))].

          @cases[#:of/count (θ-get-S θ S) 3
                 #:language esterel/typeset]{
           @#:case[absent]{
            Signals bound in a @es[ρ] must not be @es[absent],
            therefore this case is not possible.}
           @#:case[present]{
            In this case we may reduce by @rule["is-present"].}
           @#:case[unknown]{

            In this case, by @es[(not-blocked θ A E p)],
            It must be the case that @es[(L¬∈ S (->S (Can-θ (ρ θ A (in-hole E (present S p q))) ·)))].
            Therefore we may reduce by @rule["is-absent"].
            
         }}}
        
        ;; loops
        @#:case[(loop p_o)]{TODO}
        @#:case[(loop^stop p_o q_o)]{TODO}]}