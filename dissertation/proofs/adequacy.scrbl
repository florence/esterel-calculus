#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          redex/pict
          (except-in esterel-calculus/redex/model/shared FV FV/e)
          esterel-calculus/redex/test/binding
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
          (only-in esterel-calculus/redex/model/reduction
                   blocked-pure)
          (except-in scribble-abbrevs/latex definition))


@title[#:style paper-title-style]{Adequacy}


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
       @list{For all @es[p], @es[θ], @es[A], @es[E],
        @es[(blocked-pure θ A E p)]
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

@proof[#:label "blocked-gives-bot"
       #:title "blocked and can give non-constructiveness"
       #:statement
       @list{For all @es[p], @es[θ_1], @es[θ_2], @es[A], @es[E], @es[S]
                     
        if @es[(blocked-pure (parens (<- θ_1 θ_2)) A hole (in-hole E p))],
        @es[(binds (compile (in-hole E p)) (parens (<- θ_1 θ_2)))],
        and @es[(L∈ S (->S (Can-θ (ρ θ_1 A (in-hole E p)) θ_2)))]
        
        then @es[(= (of (compile (in-hole E p)) S) ⊥)]}]{
TODO
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