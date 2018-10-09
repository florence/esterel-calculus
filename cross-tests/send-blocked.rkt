#lang racket

;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require "send-lib.rkt" "send-basics.rkt"
         esterel-calculus/redex/model/reduction
         redex/reduction-semantics)

(provide send-blocked)

(define/contract (send-blocked θ p)
  (-> θ? p? string?)
  (define is-blocked? (judgment-holds (blocked ,θ ,p)))
  (define statement
    (~a "⌊ blocked-dec "
        (send-θ θ)
        " "
        (send-p p)
        " ⌋ Prop.≡ "
        (if is-blocked? "true" "false")))
  (send-thing (list p θ) "Blocked" statement (λ (p spew) (spew "Prop.refl"))))
