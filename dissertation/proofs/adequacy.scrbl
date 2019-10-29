#lang scribble/base

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          redex/reduction-semantics
          (except-in esterel-calculus/redex/model/shared FV FV/e)
          esterel-calculus/redex/test/binding
          esterel-calculus/redex/model/lset
          esterel-calculus/redex/model/potential-function
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
        @#:case[nothing]{TODO prove by rosette}
        @#:case[(exit n)]{TODO prove by rosette}
        @#:case[pause]{TODO prove by rosette}
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
          constructive. Note that the synchronizer is acylclic,
          therefore as all of its inputs are defined it too is
          constructive. Therefore the entire circuit is constructive.
         }
        @#:case[(suspend paused S)]{}
        @#:case[(loop^stop paused q)]{}
        ]}
