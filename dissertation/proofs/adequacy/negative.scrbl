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

@title["Negative"]



@proof[#:title "Non-stepping terms are values"
       #:label "step-is-v"
       #:statement
       @list{For all @es[(= q (ρ θ A p))],
                     
        If @es[(closed q)], and
        there does not exists some @es[θ_o] and @es[p_o]
        such that
        @es[(⟶^r q (ρ θ_o A (in-hole E p_o)))]
        or
        there exists some @es[r]
        such that @es[(⟶^s q (⟶^r (ρ θ A (in-hole E r)) (ρ θ_o A (in-hole E p_o))))]
        then either
         @es/unchecked[(L∈ p done)]
        or
        @es[(blocked-pure θ A hole p)]}]{                                       
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