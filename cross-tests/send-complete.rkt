#lang racket

;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require "send-lib.rkt" "send-basics.rkt"
         (except-in "../redex/model/shared.rkt" quasiquote)
         redex/reduction-semantics)

(provide send-complete)

(define complete? (redex-match? esterel-eval complete))

(define/contract (send-complete p)
  (-> p? string?)
  (define is-complete? (complete? p))
  (define statement
    (~a "⌊ complete-dec "
        (send-p p)
        " ⌋ Prop.≡ "
        (if (complete? p) "true" "false")))
  (send-thing p "Complete" statement (λ (p spew) (spew "Prop.refl"))))

