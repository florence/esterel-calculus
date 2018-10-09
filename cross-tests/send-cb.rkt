#lang racket

(require "send-lib.rkt"
         "send-basics.rkt"
         "../redex/test/binding.rkt"
         "../redex/model/lset.rkt"
         redex/reduction-semantics)

(provide send-CB)

#|
generate these later

⌊ binding-dec p1 ⌋ ≡ true

|#

(define/contract (send-CB p)
  (-> p? string?)
  (send-thing p
              "CB"
              (~a "⌊ binding-dec "
                  (send-p p)
                  " ⌋ Prop.≡ "
                  (if (judgment-holds (CB ,p))
                      "true"
                      "false"))
              (λ (p spew) (spew "Prop.refl"))))

#|

The things below generate proofs about
`distinct` and `distinct'` but they
aren't used now, because `binding-dec`
does the needful on the Agda side

|#

(define/contract (send-distinct L1 L2)
  (-> L? L? string?)
  (send-thing (list L1 L2)
              "distinctL"
              (~a "distinct\n   (" (spew-L L1) ")\n   (" (spew-L L2) ")")
              recur-over-distinct-Ls))

(define (recur-over-distinct-Ls L1+L2 spew)
  (match-define (list L1 L2) L1+L2)
  (define-values (Ss1 ss1 xs1) (L->three-nat-lists L1))
  (define-values (Ss2 ss2 xs2) (L->three-nat-lists L2))
  (spew "(~a , ~a , ~a)"
        (send-distinctprime Ss1 Ss2)
        (send-distinctprime ss1 ss2)
        (send-distinctprime xs1 xs2)))

(define/contract (send-L L)
  (-> L? string?)
  (define-values (Ss ss xs) (L->three-nat-lists L))
  (cond
    [(and (null? Ss) (null? ss) (null? xs))
     "base"]
    [else
     (send-thing L "L" "VarList" spew-L)]))

(define (spew-L L spew)
  (define-values (Ss ss xs) (L->three-nat-lists L))
  (spew "(~a , ~a , ~a)" (to-agda-list Ss) (to-agda-list ss) (to-agda-list xs)))

(define (L->three-nat-lists L)
  (define ss '())
  (define Ss '())
  (define xs '())
  (let loop ([L L])
    (match L
      [`{} (void)]
      [`{,(? S? S) ,L} (set! Ss (cons S Ss)) (loop L)]
      [`{,(? s? s) ,L} (set! ss (cons s ss)) (loop L)]
      [`{,(? x? x) ,L} (set! xs (cons x xs)) (loop L)]))

  (values (map var->index (reverse Ss))
          (map var->index (reverse ss))
          (map var->index (reverse xs))))

(define/contract (send-distinctprime l1 l2)
  (-> (listof natural?) (listof natural?) string?) 
  (send-thing (list l1 l2)
              "distinctprime"
              (~a "distinct' (" (to-agda-list l1) ") (" (to-agda-list l2) ")")
              recur-over-distinct-lists))

(define (recur-over-distinct-lists l1+l2 spew)
  (match-define (list l1 l2) l1+l2)
  (spew "\\ {\n")
  (for ([e1 (in-list l1)]
        [i (in-naturals)])
    (spew "  .~a ~s -> ~a;\n"
          e1
          (for/fold ([e `(here Prop.refl)])
                    ([_ (in-range i)])
            `(there ,e))
          (send-nat-not-in-nat-list e1 l2)))
  (spew "  _ ~s _\n  }\n"
        (for/fold ([e `()])
                  ([_ (in-range (length l1))])
          `(there ,e))))
