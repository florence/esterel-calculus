#lang racket
(require redex/reduction-semantics
         (except-in esterel-calculus/redex/model/shared)
         esterel-calculus/redex/model/reduction
         (only-in esterel-calculus/redex/test/binding esterel-L)
         esterel-calculus/redex/model/potential-function
         
         esterel-calculus/cross-tests/send-lib
         esterel-calculus/cross-tests/send-basics)

(provide
 (contract-out
  [send-std (-> p? void?)]))

(define (send-std p)
  (define p-run (term (wrap ,p)))
  (define steps (apply-reduction-relation/tag-with-names R p-run))
  (match steps
    [(list) (send-no-steps p-run)]
    [(list (list rule p))
     (send-single-step p-run #:to p #:by rule)]
    [else (error 'send-std "non-deterministic step in standard reduction on: ~a" p-run)]))

(define-metafunction esterel-eval
  wrap : p -> (ρ θ p)
  [(wrap (ρ θ p)) (ρ θ p)]
  [(wrap p) (ρ · p)])

(define (send-no-steps p-run)
  (-> p? void?)
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
  (cond
    [(member rule (list "absence" "readyness"))
     (spew-nodecomp-rule lhs rhs rule spew*)]
    [else
     (spew-decomp-rule lhs rhs rule spew*)]))

(define refl "Prop.refl")
(define ¬p "(λ ())")
(define (spew-decomp-rule lhs rhs rule spew*)
  (define-values (E-decomp-label E-leftmost-label inner θ) (get-decomp-labels lhs rhs))
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
     ["emit"
      (spew "std-emit"
            (term S)
            (send-isSigϵ (term S) θ))]
     [("loop" _)
      (spew "std-loop-unroll")]
     [("seq-done" _)
      (spew "std-seq-done")]
     [("seq-exit" _)
      (spew "std-seq-exit")]
     [("loop^stop-exit" _)
      (spew "loopˢ-exit")]
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
      (spew "std-set-shared-old"
            (send-all-ready (term e) θ)
            (send-isShrϵ (term s) θ)
            refl)]
     [("set-new" (<= s e))
      (spew "std-set-shared-old"
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
      (spew "std-is-false"
            (send-isVar∈ (term x) θ)
            refl)]
     [("if-true" (if x p q))
      (spew "std-is-true"
            (send-isVar∈ (term x) θ)
            refl)]
     [("merge" _)
      (spew "std-merge")]))
  (in (list rule inner)))

(define (spew-nodecomp-rule lhs rhs rule spew)
  (define in
    (term-match/single
     esterel-L
     [("absence" (ρ θ p))
      (spew "std-absence"
            (send-blocked-or-done lhs)
            ¬p)]
     [("readyness" (ρ θ p))
      (spew "std-readyness"
            (send-blocked-or-done lhs)
            refl
            ¬p)]))
  (in (list rule lhs)))

(define ((decomp-rule-spewer E-decomp-label E-leftmost-label spew) name . extras)
  (apply
   spew
   (apply ~a
          #:separator " "
          name (build-list (length extras) (const "~a")))
   E-leftmost-label
   (append extras (list E-decomp-label))))
        

(define/contract (get-decomp-labels lhs rhs)
  (-> p? p? (values string? string? p? θ?))
  (define decomps
    (filter values
            ((term-match
              esterel-L
              [((ρ θ (in-hole E p))
                (ρ θ_2 (in-hole E p_!_1)))
               (let ()
                 (define d (build-derivations (good E θ)))
                 (if (pair? d)
                     (list (term E) (first d) (term p) (term θ))
                     #f))])
             (list lhs rhs))))
  (match-define (list E E-deriv inner θ)
    (argmax (lambda (x) (term (E-size ,x)))
            decomps))
  (values (send-E-decomposition E (term (in-hole ,E ,inner)))
          (send-leftmost E-deriv)
          inner
          θ))

(define-metafunction esterel-L
  E-size : E -> natural
  [(E-size hole) 0]
  [(E-size (in-hole E1 E))
   ,(+ 1 (term (E-size E)))])