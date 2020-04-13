#lang scribble/base

@(require "../../lib/redex-rewrite.rkt"
          "../../lib/util.rkt"
          "../../lib/proofs.rkt"
          (except-in "../../lib/proof-extras.rkt"
                     FV FV/e θ-get-S)
          redex/reduction-semantics
          redex/pict
          pict
          (only-in esterel-calculus/redex/model/reduction
                   blocked-pure)
          (except-in scribble-abbrevs/latex definition))

@title["Negative"]

@proof[#:title "Non-stepping terms are values"
       #:label "step-is-v"
       #:statement
       @list{For all @es[(= q-pure (ρ θr A p-pure))],
                     
        If @es[(closed q-pure)], and
        there does not exists any @es[θr_o] and @es[p-pure_o]
        such that (either
        @es[(⟶^r q-pure (ρ θr_o A (in-hole E-pure p-pure_o)))]
        or
        there exists some @es[r]
        such that @es[(⟶^s q-pure (⟶^r (ρ θr A (in-hole E-pure r-pure)) (ρ θ_o A (in-hole E-pure p-pure_o))))])
        then either
        @es/unchecked[(L∈ p-pure done)]
        or
        @es[(blocked-pure θr A hole p-pure)]}]{
 As @es[blocked-pure] and whether or not a term is @es[done] are decidable properties,
 we may act as if we have the law of the excluded middle here.

 Thus we may take the contrapositive of @proof-ref["nv-must-step"], gives
 us this exactly.
 
}

@proof[#:title "Not values must step"
       #:label "nv-must-step"
       #:interpretation @list{This
        proof is the contrapositive of the notion
        that ``terms that do not reduce, modulo @rule["par-swap"],
        are values''. As we are working in a closed universe
        with decidable properties, the contrapositive will
        give us our}
       #:statement
       @list{For all @es[(= q-pure (ρ θr A (in-hole E-pure p-pure)))],
        If @es[(closed q-pure)],
        @es/unchecked[(L¬∈ p-pure done)], and
        @es[(not-blocked θr A E-pure p-pure)]
        then there exists
        some @es[θr_o] and @es[p-pure_o]
        such that either
        @es[(⟶^r q-pure (ρ θ_o A (in-hole E-pure p-pure_o)))]
        or
        there exists some @es[r-pure]
        such that @es[(⟶^s q-pure (⟶^r (ρ θr A (in-hole E-pure r-pure)) (ρ θr_o A (in-hole E-pure p-pure_o))))]}]{
 @cases[#:of p-pure
        #:induction
        #:language esterel/typeset
        ;; terminal cases
        @#:case[nothing]{ This case violates our hypothesis that @es/unchecked[(L¬∈ p-pure done)]. }
        @#:case[pause]{ This case violates our hypothesis that @es/unchecked[(L¬∈ p-pure done)]. }
        @#:case[(exit n)]{ This case violates our hypothesis that @es/unchecked[(L¬∈ p-pure done)]. }
        @#:case[(emit S)]{

          @sequenced{
                     
           @#:step[A]{
            By the definition of @es[closed], it must be the case that @es[(= A GO)]}
           @#:step[bound]{
                          
            As @es[(closed q-pure)] and as @es[E] contains no binders,
            It must be the case that @es[(L∈ S (Ldom θr))].

           }
           @#:step[final]{

            Thus let @es[(= θ_o (<- θ (mtθ+S S present)))] and
            @es[(= p-pure_o nothing)]. Let the step we take be @rule["emit"].

           }
         }}
        
        ;; E cases
        @#:case[(seq p-pure_o q-pure_o)]{
          @sequenced{

           @#:step[paused]{
                           
            By the definition of @es[done], we know that
            @es/unchecked[(L¬∈ p-pure_o paused)].
                     
           }

           @#:step[blocked]{

            By the definition of @es[blocked], we know that
            @es[(not-blocked θ A (in-hole E-pure (seq hole q-pure_o)) p-pure_o)].

           }

           @#:step[_]{

            We by @paused know that @es[p-pure_o] is not @es[paused], but
            we must consider of @es[p-pure_o] is @es[done]. By the definition
            of @es[done], this gives:

            @cases[#:of/count (L∈ p-pure_o stopped) 2
                   #:simple-cases
                   #:no-check
                   #:language esterel/typeset]{

             @#:case[(L∈ p-pure_o stopped)]{
              @cases[#:of p-pure_o
                     #:drawn-from stopped
                     #:language esterel/typeset]{
                                                
               @#:case[nothing]{

                In this case, @es[(= θr_o θr)],
                the resulting @es[(= p-pure_o q-pure_o)],
                and we step by  @rule["seq-done"].
                
               }
                
               @#:case[(exit n)]{

                In this case, @es[(= θr_o θ)],
                the resulting @es[(= p-pure_o (exit n))],
                and we step by  @rule["seq-exit"].
                
               }

             }}
             @#:case[(L¬∈ p_o stopped)]{
              @sequenced{
                        
               @#:step[done]{As we know that
                @es/unchecked[(L¬∈ p-pure_o stopped)] and @es/unchecked[(L¬∈ p-pure_o paused)],
                we know that @es/unchecked[(L¬∈ p-pure_o done)].}

               @#:step[_]{
                          
                By @done, @paused, and @blocked, we can use our induction
                hypothesis on @es[p-pure_o] and @es[(in-hole E-pure (seq hole q-pure_o))].
                As the result we get back differs from what we need only in
                that @es[(seq hole q-pure_o)] was shifted from @es[p-pure_o] to
                @es[E], we can shift it back an return the result unchanged.
                
         }}}}}}}
        
        @#:case[(par p-pure_o q-pure_o)]{
          There is only one way for a @es[par] to @es[done], thus we know that
          @es/unchecked[(not (parens (and (L∈ p-pure_o paused) (L∈ q-pure_o paused))))].           
                                                     
          There are three ways for an @es[par] to be @es[blocked], thus
          we know that
          
          @(let ()
             (define b1 (es/unchecked (parens (and (blocked-pure θr A (in-hole E-pure (par hole q-pure_o)) p-pure_o) (blocked-pure θr A (in-hole E-pure (par p-pure_o hole)) q-pure_o)))))
             (define b2 (es/unchecked (parens (and (blocked-pure θr A (in-hole E-pure (par hole q-pure_o)) p-pure_o) (L∈ q-pure_o done)))))
             (define b3 (es/unchecked (parens (and (L∈ p-pure_o done) (blocked-pure θ A (in-hole E (par p-pure_o hole)) q-pure_o)))))
             (define on (hbl-append @es[not] (words "(")))
             (vl-append
             (hbl-append on b1)
             (hbl-append (ghost on) @es[or])
             (hbl-append (ghost on) b2)
             (hbl-append (ghost on) @es[or])
             (hbl-append (ghost on) b3 (words ")"))))

          On the whole this gives us the following expression:
          
                                   
          @(let ()
             (define pause @es/unchecked[(not (parens (and (L∈ p-pure_o paused) (L∈ q-pure_o paused))))])
             (define b1 (es/unchecked (parens (and (blocked-pure θ A (in-hole E-pure (par hole q-pure_o)) p-pure_o) (blocked-pure θr A (in-hole E (par p-pure_o hole)) q-pure_o)))))
             (define b2 (es/unchecked (parens (and (blocked-pure θ A (in-hole E-pure (par hole q-pure_o)) p-pure_o) (L∈ q-pure_o done)))))
             (define b3 (es/unchecked (parens (and (L∈ p-pure_o done) (blocked-pure θr A (in-hole E (par p-pure_o hole)) q-pure_o)))))
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

          @es/unchecked[(and (not-blocked θr A (in-hole E-pure (par hole q-pure_o)) p-pure_o) (not-blocked θr A (in-hole E (par p-pure_o hole)) q-pure_o) (L¬∈ p-pure_o paused))]
          
          @es/unchecked[(and (not-blocked θr A (in-hole E-pure (par hole q-pure_o)) p-pure_o) (not-blocked θr A (in-hole E-pure (par p-pure_o hole)) q-pure_o) (L¬∈ q-pure_o paused))]
          
          @es/unchecked[(and (not-blocked θr A (in-hole E-pure (par hole q-pure_o)) p-pure_o) (L¬∈ p-pure_o done))]
          
          @es/unchecked[(and (not-blocked θr A (in-hole E-pure (par p-pure_o hole)) q-pure_o) (L¬∈ q-pure_o done))]
          
          @cases[#:of/count the\ above 4
                 #:simple-cases
                 #:no-check
                 #:language esterel/typeset]{
           @#:case[(and (not-blocked θr A (in-hole E (par hole q-pure_o)) p-pure_o) (not-blocked θr A (in-hole E-pure (par p-pure_o hole)) q-pure_o) (L¬∈ q-pure_o paused))]{
            In this case we have @sequenced{

             @#:step[blocked]{We know
              that @es[(not-blocked θr A (in-hole E (par hole p-pure_o)) q-pure_o)]}
             @#:step[paused]{We know that @es/unchecked[(L¬∈ q-pure_o paused)]}
             @#:step[subcases]{
              @cases[#:of/count (L∈ q-pure_o stopped) 2
                     #:simple-cases
                     #:no-check
                     #:language esterel/typeset]{
               @#:case[(L∈ q-pure_o stopped)]{
                @cases[#:of/count (L∈ p-pure_o done) 2
                       #:language esterel/typeset
                       #:no-check
                       #:simple-cases]{
                 @#:case[(L∈ p-pure_o done)]{
                  @cases[#:of (p-pure_o q-pure_o)
                         #:tuplize
                         #:language esterel/typeset
                         #:drawn-from (done stopped)]{

                   @#:case[(nothing (exit n_2))]{
                                                 
                    In this case let @es[(= θr_o θr)] and @es[(= p-pure_o (exit n_2))],
                    and our reduction be a single use of @rule["par-nothing"].

                   }
                   @#:case[((exit n_1) (exit n_2))]{
                    In this case let @es[(= θr_o θr)] and @es[(= p-pure_o (exit (max n_1 n_2)))],
                    and our reduction be a single use of @rule["par-2exit"].
                    
                   }
                   @#:case[(paused (exit n_2))]{
                   
                    In this case let @es[(= θr_o θr)], @es[(= p-pure_o (exit n_2))],
                    and @es[(= r-pure (par (exit n_2) paused))]. Our reductions
                    are one use of @rule["par-swap"] and one use of @rule["par-1exit"].

                   }
                   @#:case[(done nothing)]{
                                           
                    This is analogues to the previous case, but using @rule["par-nothing"] instead
                    of @rule["par-1exit"].

                   }

                  }
                 }
                 @#:case[(L¬∈ p-pure_o done)]{

                  In this case we may invoke our induction hypothesis on
                  @es[p-pure_o], as we know
                  @es[(not-blocked θr A (in-hole E-pure (par hole q-pure_o)) p-pure_o)] and
                  @es/unchecked[(L¬∈ p-pure_o done)]. As usual we may reassemble
                  the result of the induction by shifting one frame of the
                  @es[E] back over and using the same reductions.

                 }
               }}
               @#:case[(L¬∈ q-pure_o stopped)]{
                @sequenced{
                 @#:step[not-done]{As we know @es/unchecked[(L¬∈ q-pure_o stopped)] and
                  @es/unchecked[(L¬∈ q-pure_o paused)], we know @es/unchecked[(L¬∈ q-pure_o done)].}
                 @#:step[exists]{

                  We may invoke our induction hypothesis on
                  @es[(in-hole E-pure (par p-pure_o hole))] and @es[q-pure_o]. This gives us
                  that exists some @es[θr_o1] and @es[p-pure_o1] using @blocked and @not-done such that
                  @es[(⟶^r q-pure (ρ θr_o1 A (in-hole E-pure p-pure_o1)))] or there exists
                  some @es[r] such that
                  @es[(⟶^s q-pure (⟶^r r-pure (ρ θr_o1 A (in-hole (in-hole E-pure (par p-pure_o hole)) p-pure_o1))))].

                 }
                 @#:step[final]{

                  In this case we can take the result from
                  @exists and shift The @es[(par p-pure_o hole)] over to @es[p-pure_o1].
                  Giving us a resulting @es[(= p-pure_o2 (par p-pure_o p-pure_o1))], and an
                  unchanged @es[θr_o1]. As the overall terms have not changed,
                  the reductions form @exists are unchanged. Thus we return those
                  reductions.

           }}}}}}}
                                 
           @#:case[(and (not-blocked θr A (in-hole E-pure (par hole q-pure_o)) p-pure_o) (not-blocked θr A (in-hole E-pure (par p-pure_o hole)) q-pure_o) (L¬∈ p-pure_o paused))]{

            This case is the same as the previous, but finding a
            reduction in the other branch. As in this case in the
            subcase where we concider one branch begin @es[done] and the
            other being @es[stopped], @es[p-pure_o] is the branch that is
            @es[stopped] we do not need to use @es[⟶^s].

           }
            
           @#:case[(and (not-blocked θr A (in-hole E-pure (par hole q-pure_o)) p-pure_o) (L¬∈ p-pure_o done))]{
                                                                                          
            As we know that @es[p-pure_o] is not @es[blocked] or @es[done]
            we can induct on @es[p-pure_o] and
            @es[(in-hole E-pure (par hole q-pure_o))]. As usual we may reassemble
            the result of the induction by shifting one frame of the
            @es[E-pure] back over and using the same reductions.
               
           }
            
           @#:case[(and (not-blocked θr A (in-hole E-pure (par p-pure_o hole)) q-pure_o) (L¬∈ q-pure_o done))]{

            This case is the same as the previous, but finding a reduction
            in the other branch.

         }}}
        @#:case[(trap p-pure_o)]{
          @sequenced{
           @#:step[paused]{By the definition of @es[done]
            we know that @es/unchecked[(L¬∈ p_o paused)].
           }
           @#:step[blocked]{By the definition of @es[blocked]
            we know that @es[(not-blocked θr A (in-hole E-pure (trap hole)) p-pure_o)].}
           @#:step[_]{
            @cases[#:of/count (L∈ p-pure_o stopped) 2
                   #:language esterel/typeset
                   #:no-check
                   #:simple-cases]{
             @#:case[(L∈ p-pure_o stopped)]{In this case we may reduced by @rule["trap"].}
              @#:case[(L¬∈ p-pure_o stopped)]{
             @sequenced{
               @#:step[done]{Given @es/unchecked[(L¬∈ p-pure_o stopped)] and @paused,
                we know that @es/unchecked[(L¬∈ p-pure_o done)]}
                @#:step[_]{Given @done and @blocked we may use our induction hypothesis
               on @es[p_o] and @es[(in-hole E-pure (trap hole))]. As usual we may reassemble
               the result of the induction by shifting one frame of the @es[E-pure] back over and
               using the same reductions.}
             }}}}}}
        @#:case[(suspend p-pure_o S)]{This case is analogous to the previous case
          but reducing by @rule["suspend"] rather than @rule["trap"].}
        
        ;; the rest
        
        @#:case[(signal S p-pure_o)]{
          In this case we may reduce by @rule["signal"].}
        @#:case[(ρ θr_o A_o p-pure_o)]{
          In this case we may reduce by @rule["merge"],
          as by @es[(closed q)] we know that @es[(= A GO)],
          which must be @es[A->=] @es[A_o]. }
        @#:case[(present S p-pure_o q-pure_o)]{
          By @es[(closed q-pure)] and @es[E] not containing
          any binders we know that @es[(L∈ S (Ldom θr))].

          @cases[#:of/count (θ-get-S θr S) 3
                 #:language esterel/typeset]{
           @#:case[absent]{
            Signals bound in a @es[ρ] must not be @es[absent],
            therefore this case is not possible.}
           @#:case[present]{
            In this case we may reduce by @rule["is-present"].}
           @#:case[unknown]{

            In this case, by @es[(not-blocked θr A E p-pure_o)],
            It must be the case that @es[(L¬∈ S (->S (Can-θ (ρ θ A (in-hole E (present S p-pure_o q-pure_o))) ·)))].
            Therefore we may reduce by @rule["is-absent"].
            
         }}}
        
        ;; loops
        @#:case[(loop p_o) #:ignore]{TODO}
        @#:case[(loop^stop p_o q_o) #:ignore]{TODO}]}