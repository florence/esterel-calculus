#lang racket
(require redex/reduction-semantics
         (except-in esterel-calculus/redex/model/shared)
         esterel-calculus/redex/model/reduction
         (only-in esterel-calculus/redex/test/binding esterel-L)
         esterel-calculus/redex/model/potential-function
         
         "send-lib.rkt"
         "send-basics.rkt")

(provide
 (contract-out
  [send-std (-> p? any)]))

(define (send-std p)
  (for ([p-run (in-list (term (wrap ,p)))])
    (define steps (apply-reduction-relation/tag-with-names R p-run))
    (match steps
      [(list) (send-no-steps p-run)]
      [(list (list rule p))
       (send-single-step p-run #:to p #:by rule)]
      [else (error 'send-std "non-deterministic step in standard reduction on: ~a" p-run)])))

(define-metafunction esterel-eval
  wrap : p -> ((ρ θ A p) ...)
  [(wrap (ρ θ A p)) ((ρ θ A p))]
  [(wrap p) ((ρ · GO p) (ρ · WAIT p))])

(define (send-no-steps p-run)
  (-> p? void?)
  (void "TODO")
  #;
  (error "TODO"))

(define (send-single-step lhs #:to rhs #:by rule)
  (-> p? #:to p? #:by? string? void?)
  (log-rule rule lhs)
  (define lhs-name (send-p lhs))
  (define rhs-name (send-p rhs))
  ;; TODO what is this for?
  #;(add-top-level-comment)
  (send-thing (list lhs rhs rule) "std"
              (~a lhs-name " ⇁ " rhs-name)
              spew-std-rule))

(define (spew-std-rule lhs+rhs+rule spew*)
  (match-define (list lhs rhs rule) lhs+rhs+rule)
  (spew-decomp-rule lhs rhs rule spew*))

(define refl "Prop.refl")
(define ¬p "(λ ())")
(define (spew-decomp-rule lhs rhs rule spew*)
  (define-values (E-decomp-label E-leftmost-label inner θ A)
    (get-decomp-labels lhs rhs))
  (define spew (decomp-rule-spewer E-decomp-label E-leftmost-label spew*))
  (define in
    (term-match/single
     esterel-L
     [("parr" (par p q))
      (spew "std-par-right"
            (send-stopped (term p))
            (send-done (term q)))]
     [("parl" (par p q))
      (spew "std-par-left"
            (send-paused (term p))
            (send-stopped (term q)))]
     [("is-present" (present S p q))
      (spew "std-is-present"
            (term S)
            (send-isSigϵ (term S) θ)
            refl)]
     [("is-absent" (present S p q))
      (spew "std-is-absent"
            (term S)
            (send-isSigϵ (term S) θ)
            refl)] 
     [("emit" (emit S))
      (spew "std-emit"
            (term S)
            (send-isSigϵ (term S) θ)
            ¬p)]
     [("loop" _)
      (spew "std-loop-unroll")]
     [("seq-done" _)
      (spew "std-seq-done")]
     [("seq-exit" _)
      (spew "std-seq-exit")]
     [("loop^stop-exit" _)
      (spew "std-loopˢ-exit")]
     [("suspend" (suspend p S))
      (spew "std-suspend-done"
            (send-stopped (term p)))]
     [("trap" (trap p))
      (spew "std-trap-done"
            (send-stopped (term p)))]
     [("signal" _)
      (spew "std-raise-signal")]
     [("shared" (shared s := e p))
      (spew "std-raise-shared"
            (send-all-ready (term e) θ))]
     [("set-old" (<= s e))
      (spew "std-set-shared-value-old"
            (send-all-ready (term e) θ)
            (send-isShrϵ (term s) θ)
            refl)]
     [("set-new" (<= s e))
      (spew "std-set-shared-value-new"
            (send-all-ready (term e) θ)
            (send-isShrϵ (term s) θ)
            refl)]
     [("var" (var x := e p))
      (spew "std-raise-var"
            (send-all-ready (term e) θ))]
     [("set-var" (:= x e))
      (spew "std-set-var"
            (send-isVar∈ (term x) θ)
            (send-all-ready (term e) θ))]
     [("if-false" (if x p q))
      (spew "std-if-false"
            (send-isVar∈ (term x) θ)
            refl)]
     [("if-true" (if x p q))
      (spew "std-if-true"
            (send-isVar∈ (term x) θ)
            refl)]
     [("merge" _)
      (spew "std-merge")]))
  (in (list rule inner)))

(define ((decomp-rule-spewer E-decomp-label E-leftmost-label spew) name . extras)
  (apply
   spew
   (apply ~a
          #:separator " "
          name (build-list (+ 2 (length extras)) (const "~a")))
   E-leftmost-label
   (append extras (list E-decomp-label))))
        

(define/contract (get-decomp-labels lhs rhs)
  (-> p? p? (values string? string? p? θ? A?))
  (define decomps
    (error "ug")
    #;
    (filter values
            ((term-match
              esterel-L
              [((ρ θ A (in-hole E p))
                (ρ θ_2 A_2 (in-hole E p_!_1)))
               (let ()
                 (define d (build-derivations (leftmost θ A E)))
                 (if (pair? d)
                     (list (term E) (first d) (term p) (term θ) (term A))
                     #f))])
             (list lhs rhs))))
  (match-define (list E E-deriv inner θ A)
    (argmax (lambda (x) (term (E-size ,(first x))))
            decomps))
  (values (send-E-decomposition E inner)
          (send-leftmost θ E E-deriv)
          inner
          θ
          A))

(define-metafunction esterel-L
  E-size : E -> natural
  [(E-size hole) 0]
  [(E-size (in-hole E1 E))
   ,(+ 1 (term (E-size E)))])