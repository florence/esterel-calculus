#lang racket

;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require "send-lib.rkt" "send-basics.rkt"
         esterel-calculus/redex/model/reduction
         redex/reduction-semantics)

(provide send-blocked)
(define/contract (send-blocked θ A p)
  (-> θ? A? p? string?)
  (define is-blocked? (judgment-holds (blocked ,θ ,A ,p)))
  (define statement
    (~a "⌊ blocked-dec "
        (send-θ θ)
        " "
        (send-p p)
        " "
        (send-A A)
        " ⌋ Prop.≡ "
        (if is-blocked? "true" "false")))
  (send-thing (list p θ) "Blocked" statement (λ (p spew) (spew "Prop.refl"))))
