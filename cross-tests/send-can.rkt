#lang racket

;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require "send-lib.rkt" "send-basics.rkt"
         (only-in "../redex/model/lset.rkt" Lflatten)
         (except-in "../redex/model/shared.rkt" quasiquote)
         "../redex/model/potential-function.rkt"
         redex/reduction-semantics)

(provide send-can)

(define/contract (send-can p θ)
  (-> p? θ? string?)
  (define p-label (send-p p))
  (match-define `(S-code-s ,Ss ,codes ,ss) (term (Can ,p ,θ)))
  (define (exit-code->agda-exit-code k)
    (match k
      ['nothin "Code.nothin"]
      ['paus "Code.pause"]
      [(? integer? k) (~a "(Code.exit " k ")")]))
  (define θ-var (send-θ θ))
  (add-to-top-level-comment (format "(~a) ~s" θ-var θ))
  (send-thing p "cantest"
              (format "Can ~a ~a Prop.≡ (~a , ~a , ~a)"
                      p-label
                      θ-var
                      (to-agda-list (map var->index (flatten Ss)))
                      (to-agda-list (map exit-code->agda-exit-code (term (Lflatten ,codes))))
                      (to-agda-list (map var->index (flatten ss))))
              (λ (p spew) (spew "Prop.refl"))))
