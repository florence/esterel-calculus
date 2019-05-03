#lang racket

;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require redex/reduction-semantics
         (except-in "../redex/model/shared.rkt" quasiquote)
         "../redex/model/calculus.rkt"
         (only-in "../redex/test/binding.rkt" esterel-L)
         "../redex/model/potential-function.rkt"
         
         "send-lib.rkt"
         "send-basics.rkt")
(provide send-steps)

(define/contract (send-steps p1)
  (-> p? (listof p?))
  (for*/list ([decomp-match (or (decompose p1) '())]
              [p1 (in-value (find-named-binding 'p decomp-match))]
              [label+p2 (in-list (apply-reduction-relation/tag-with-names ⇀ p1))])
    (define P (find-named-binding 'C decomp-match))
    ;; eventually, this should use `P` to send an in-context reduction(?)
    (define label (list-ref label+p2 0))
    (define p2 (list-ref label+p2 1))
    (send-step label p1 p2)
    p2))

(define decompose (redex-match esterel-L (in-hole (name C (cross p)) p)))

(define/contract (find-named-binding name mtch)
  (-> symbol? match? any/c)
  (for/or ([b (in-list (match-bindings mtch))])
    (and (equal? (bind-name b) name)
         (bind-exp b))))

(define/contract (send-step label p1 p2)
  (-> string? p? p? string?)
  (log-rule label p1)
  (define p1-name (send-p p1))
  (define p2-name (send-p p2))
  (add-to-top-level-comment
   (let ([w (max (string-length p1-name)
                 (string-length p2-name))])
     (~a "(" (~a #:width w p1-name) ")  " (~s p1)
         "\n  --> " label "\n"
         "(" (~a #:width w p2-name) ")  " (~s p2)
         "\n")))
  (send-thing (list p1 p2 label) "st"
              (~a p1-name " ⟶₁ " p2-name)
              recur-over-label-and-terms))

(define (recur-over-label-and-terms p1+p2+label spew)
  (match-define (list p1 p2 label) p1+p2+label)
  (match label
    ["par-swap"
     (spew "[par-swap]")]
    ["par-nothing"
     (redex-let
      esterel-L
      ([(par p q) p1])
     (spew "[par-nothing] ~a"
           (send-done (term q))))]
    ["par-1exit"
     (redex-let
      esterel-L
      ([(par (exit n) q) p1])
     (spew "[par-1exit] ~a ~a"
           (term n)
           (send-paused (term q))))]
    ["par-2exit"
     (redex-let
      esterel-L
      ([(par (exit n_1) (exit n_2)) p1])
     (spew "[par-2exit] ~a ~a"
           (term n_1)
           (term n_2)))]
    ["is-present"
     (redex-let
      esterel-L
      ([((ρ θ (in-hole E (present S p q)))
         (ρ θ (in-hole E p)))
        (list p1 p2)])
      (spew "[is-present] ~a ~a ~a ~a"
            (term S)
            (send-isSigϵ (term S) (term θ))
            "Prop.refl"
            (send-E-decomposition (term E) (term (present S p q)))))]
    ["is-absent"
     (redex-let
      esterel-L
      ([((ρ θ (in-hole E (present S p q)))
         (ρ θ (in-hole E q)))
        (list p1 p2)])
      (spew "[is-absent] ~a ~a ~a ~a"
            (term S)
            (send-isSigϵ (term S) (term θ))
            "Prop.refl"
            (send-E-decomposition (term E) (term (present S p q)))))]
    ["emit"
     (redex-let
      esterel-L
      ([((ρ θ_1 (in-hole E (emit S)))
         (ρ θ_2 (in-hole E nothing)))
        (list p1 p2)])
      (define decomp-label (send-E-decomposition (term E) (term (emit S))))
      (spew "[emit] ~a ~a ~a" (send-isSigϵ (term S) (term θ_1)) "(λ ())" decomp-label))]
    ["loop" (spew "[loop-unroll]")]
    ["seq-done" (spew "[seq-done]")]
    ["seq-exit" (spew "[seq-exit]")]
    ["loop^stop-exit" (spew "[loopˢ-exit]")]
    ["suspend"
     (redex-let
      esterel-L
      ([(suspend p S) p1])
      (spew "[suspend-done] ~a" (send-stopped (term p))))]
    ["trap"
     (redex-let
      esterel-L
      ([(trap p) p1])
      (spew "[trap-done] ~a" (send-stopped (term p))))]
    ["signal" (spew "[raise-signal]")]
    ["shared"
     (redex-let
      esterel-L
      ([((ρ θ (in-hole E (shared s := e p)))
         (ρ θ (in-hole E (ρ ((shar s ev old) ·) p))))
        (list p1 p2)])
      (spew "[raise-shared] ~a ~a"
            (send-all-ready (term e) (term θ))
            (send-E-decomposition (term E) (term (shared s := e p)))))]
    ["set-old"
     (redex-let
      esterel-L
      ([((ρ θ_1 (in-hole E (<= s e)))
         (ρ θ_2 (in-hole E nothing)))
        (list p1 p2)])
      (spew "[set-shared-value-old] ~a ~a Prop.refl ~a"
            (send-all-ready (term e) (term θ_1))
            (send-isShrϵ (term s) (term θ_1))
            (send-E-decomposition (term E) (term (<= s e)))))]
    ["set-new"
     (redex-let
      esterel-L
      ([((ρ θ_1 (in-hole E (<= s e)))
         (ρ θ_2 (in-hole E nothing)))
        (list p1 p2)])
      (spew "[set-shared-value-new] ~a ~a Prop.refl ~a"
            (send-all-ready (term e) (term θ_1))
            (send-isShrϵ (term s) (term θ_1))
            (send-E-decomposition (term E) (term (<= s e)))))]
    ["var"
     (redex-let
      esterel-L
      ([((ρ θ (in-hole E (var x := e p)))
         (ρ θ (in-hole E (ρ ((var· x ev) ·) p))))
        (list p1 p2)])
      (spew "[raise-var] ~a ~a"
            (send-all-ready (term e) (term θ))
            (send-E-decomposition (term E) (term (var x := e p)))))]
    ["set-var"
     (redex-let
      esterel-L
      ([((ρ θ_1 (in-hole E (:= x e)))
         (ρ θ_2 (in-hole E nothing)))
        (list p1 p2)])
      (spew "[set-var] ~a ~a ~a"
            (send-isVar∈ (term x) (term θ_1))
            (send-all-ready (term e) (term θ_1))
            (send-E-decomposition (term E) (term (:= x e)))))]
    ["if-false"
     (redex-let
      esterel-L
      ([((ρ θ (in-hole E (if x p q)))
         (ρ θ (in-hole E q)))
        (list p1 p2)])
      (spew "[if-false] ~a Prop.refl ~a"
            (send-isVar∈ (term x) (term θ))
            (send-E-decomposition (term E) (term (if x p q)))))]
    ["if-true"
     (redex-let
      esterel-L
      ([((ρ θ (in-hole E (if x p q)))
         (ρ θ (in-hole E p)))
        (list p1 p2)])
      (spew "[if-true] ~a Prop.refl ~a"
            (send-isVar∈ (term x) (term θ))
            (send-E-decomposition (term E) (term (if x p q)))))]
    ["absence"
     (redex-let
      esterel-L
      ([(ρ θ_1 p_1) p1]
       [(ρ θ_2 p_2) p2])
      (define S (find-difference (term θ_1) (term θ_2)))
      (unless S (error 'absence-rule "thetas dont seem different:\n  ~s\n  ~s"
                       (term θ_1) (term θ_2)))
      (spew "[absence] ~a ~a ~a ~a"
            S
            (send-isSigϵ S (term θ_1))
            "Prop.refl"
            (send-nat-not-in-nat-list (var->index S)
                                      (map var->index
                                           (flatten (term (->S (Can-θ (ρ θ_1 p_1) ·))))))))]
    ["readyness"
     (redex-let
      esterel-L
      ([((ρ θ_1 p)
         (ρ θ_2 p))
        (list p1 p2)])
      (define s (find-difference (term θ_1) (term θ_2)))
      (unless s (error 'absence-rule "thetas dont seem different:\n  ~s\n  ~s"
                       (term θ_1) (term θ_2)))
      (define old? (equal? (cdr (hash-ref (θ-to-hash (term θ_1)) s)) 'old))
      (spew "[readyness] ~a ~a ~a ~a"
            s
            (send-isShrϵ s (term θ_1))
            (if old? "(inj₁ Prop.refl)" "(inj₂ Prop.refl)")
            (send-nat-not-in-nat-list (var->index s)
                                      (map var->index (flatten (term (->sh (Can-θ (ρ θ_1 p) ·))))))))]
    ["merge"
     (redex-let
      esterel-L
      ([((ρ θ_1 (in-hole E (ρ θ_2 p)))
         (ρ θ_3 (in-hole E p)))
        (list p1 p2)])
      (define decomp-label (send-E-decomposition (term E) (term (ρ θ_2 p))))
      (spew "[merge] ~a" decomp-label))]))


;; assumes that θ1 and θ2 have the same keys
;; but that one maps one thing differently; returns
;; the key that's differently mapped
(define/contract (find-difference θ1 θ2)
  (-> θ? θ? (or/c symbol? #f))
  (define ht.1 (θ-to-hash θ1))
  (define ht.2 (θ-to-hash θ2))
  (for/or ([(k v1) (in-hash ht.1)])
    (and (not (equal? (hash-ref ht.2 k) v1))
         k)))
 
