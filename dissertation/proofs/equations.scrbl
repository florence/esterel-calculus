#lang scribble/book

@(require "../lib/redex-rewrite.rkt"
          "../lib/util.rkt"
          "../lib/proofs.rkt"
          "../lib/proof-extras.rkt"
          "../lib/misc-figures.rkt"
          "../lib/rule-figures.rkt"
          "../lib/jf-figures.rkt"
          "../lib/cite.rkt"
          "../notations.scrbl"
          "../lib/proof-rendering.rkt"
          (only-in racket/list empty add-between)
          esterel-calculus/redex/model/shared
          scriblib/figure
          redex/pict
          syntax/parse/define
          esterel-calculus/redex/model/deps
          (for-syntax racket/base syntax/parse)
          pict
          racket/stxparam
          racket/math
          (only-in racket/bool implies))

@title{Proving equalities through the calculus}

The proofs in this section are written in a DSL which
checks them against the equations of the calculus, then
generates the prose in that section.

@[begin
       
 (define-simple-macro (equality-proof
                       #:title title
                       #:label tag
                       #:∀ x:expr ...
                       (~optional (~seq #:assume assumptions:expr ...))
                       dee)
   (let ()
     (lift-to-compile-time-for-effect!
      #:expand
      (unless (eq? #t
                   (redex-check
                    esterel/typeset (x ...)
                    (implies
                     (and (~? (~@ (if (dj? assumptions)
                                      (judgment-holds assumptions)
                                      (term assumptions))
                                  ...)))
                     (judgment-holds ≡j dee))
                    #:attempts 20
                    #:print? #f))
        (error "erg")))
     (proof
      #:type 'theorem
      #:title title
      #:label tag
      #:statement @list{For all @[add-between [list @es[x] ...] ", "], @(~? @~@{If @[add-between [list (es assumptions) ...] " and, "], then@(linebreak)})
  @(statement dee)}
      @list{
  @(with-paper-rewriters (render dee))
  By the above and @proof-ref["soundness"], we may conclude that @(statement dee).})))]

@[equality-proof
  #:title "Can swap adjacent signals"
  #:label "swap-sigs"
  #:∀ p S_1 S_2
  (de
   trans
   (signal S_1 (signal S_2 p))
   (de step 
       (signal S_1
         (signal S_2
           p))
       (ρ (mtθ+S S_1 unknown) WAIT
          (signal S_2
            p))
       "signal")
   (ρ (mtθ+S S_1 unknown) WAIT
      (signal S_2
        p))
   (de ctx
       (ρ (mtθ+S S_1 unknown) WAIT
          (signal S_2
            p))
       (ρ (mtθ+S S_1 unknown) WAIT
          (ρ (mtθ+S S_2 unknown) WAIT p))
       (de step
           (signal S_2
             p)
           (ρ (mtθ+S S_2 unknown) WAIT
              p)
           "signal"))
   (ρ (mtθ+S S_1 unknown) WAIT
      (ρ (mtθ+S S_2 unknown) WAIT
         p))
   (de step
       (ρ (mtθ+S S_1 unknown) WAIT
          (ρ (mtθ+S S_2 unknown) WAIT
             p))
       (ρ (<- (mtθ+S S_1 unknown) (mtθ+S S_2 unknown)) WAIT
          p)
       "merge")
   (ρ (<- (mtθ+S S_1 unknown) (mtθ+S S_2 unknown)) WAIT
      p)
   (de sym
       (ρ (<- (mtθ+S S_1 unknown) (mtθ+S S_2 unknown)) WAIT
          p)
       (ρ (mtθ+S S_2 unknown) WAIT
          (ρ (mtθ+S S_1 unknown) WAIT
             p))
       (de step
           (ρ (mtθ+S S_2 unknown) WAIT
              (ρ (mtθ+S S_1 unknown) WAIT
                 p))
           (ρ (<- (mtθ+S S_1 unknown) (mtθ+S S_2 unknown)) WAIT
              p)
           "merge"))
   (ρ (mtθ+S S_2 unknown) WAIT
      (ρ (mtθ+S S_1 unknown) WAIT
         p))
   (de sym
       (ρ (mtθ+S S_2 unknown) WAIT
          (ρ (mtθ+S S_1 unknown) WAIT
             p))
       (signal S_2
         (signal S_1
           p))
       (de trans
           (signal S_2
             (signal S_1
               p))
           (de step
               (signal S_2
                 (signal S_1
                   p))
               (ρ (mtθ+S S_2 unknown) WAIT
                  (signal S_1
                    p))
               "signal")
           (ρ (mtθ+S S_2 unknown) WAIT
              (signal S_2
                p))
           (de ctx
               (ρ (mtθ+S S_2 unknown) WAIT
                  (signal S_1
                    p))
               (ρ (mtθ+S S_2 unknown) WAIT
                  (ρ (mtθ+S S_1 unknown) WAIT
                     p))
               (de step
                   (signal S_1
                     p)
                   (ρ (mtθ+S S_1 unknown) WAIT
                      p)
                   "signal"))
           (ρ (mtθ+S S_2 unknown) WAIT
              (ρ (mtθ+S S_1 unknown) WAIT
                 p))))
   (signal S_2 (signal S_1 p)))]

@[equality-proof
  #:title "Can take the else branch for adjacent signals"
  #:label "else-branch"
  #:∀ S p q
  #:assume (L¬∈ S (->S (Can p (mtθ+S S unknown)))) (L¬∈ S (->S (Can q (mtθ+S S unknown))))
  (de
   trans
   (signal S (present S p q))
   (de step (signal S
              (present S p q))
       (ρ (mtθ+S S unknown) WAIT
          (present S p q))
       "signal")
   (ρ (mtθ+S S unknown) WAIT
      (present S p q))
   (de step (ρ (mtθ+S S unknown) WAIT
               (present S p q))
       (ρ (mtθ+S S unknown) WAIT
          q)
       "is-absent")
   (ρ (mtθ+S S unknown) WAIT
      q)
   (de sym
       (ρ (mtθ+S S unknown) WAIT
          q)
       (signal S
         q)
       (de step
           (signal S
             q)
           (ρ (mtθ+S S unknown) WAIT
              q)
           "signal"))
       
   (signal S q))]


@[equality-proof
  #:title "Lifting signals"
  #:label "lift-signals"
  #:∀ S p E A
  (de trans
      (ρ · A (in-hole E (signal S p)))
      (de ctx
          (ρ · A
             (in-hole E (signal S p)))
          (ρ · A
             (in-hole E (ρ (mtθ+S S unknown) WAIT p)))
          (de step
              (signal S p)
              (ρ (mtθ+S S unknown) WAIT p)
              "signal"))
      (ρ · A
         (in-hole E (ρ (mtθ+S S unknown) WAIT p)))
      (de step
          (ρ · A
             (in-hole E (ρ (mtθ+S S unknown) WAIT p)))
          (ρ (mtθ+S S unknown) A
             (in-hole E p))
          "merge")
      (ρ (mtθ+S S unknown) A
         (in-hole E p))
      (de sym
          (ρ (mtθ+S S unknown) A
             (in-hole E p))
          (ρ · A
             (ρ (mtθ+S S unknown) WAIT
                (in-hole E p)))
          (de step
              (ρ · A
                 (ρ (mtθ+S S unknown) WAIT
                    (in-hole E p)))
              (ρ (mtθ+S S unknown) A
                 (in-hole E p))
              "merge"))
      (ρ · A
         (ρ (mtθ+S S unknown) WAIT
            (in-hole E p)))
      (de ctx
          (ρ · A
             (ρ (mtθ+S S unknown) WAIT
                (in-hole E p)))
          (ρ · A
             (signal S
               (in-hole E p)))
          (de sym

              (ρ (mtθ+S S unknown) WAIT
                 (in-hole E p))
              (signal S
                (in-hole E p))
              (de step
                  (signal S
                    (in-hole E p))
                  (ρ (mtθ+S S unknown) WAIT
                     (in-hole E p))
                  "signal")))
      (ρ · A (signal S (in-hole E p))))]

