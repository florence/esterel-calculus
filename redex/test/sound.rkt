#lang racket
(require redex/reduction-semantics
         (except-in esterel-calculus/redex/model/shared quasiquote)
         (prefix-in calculus: esterel-calculus/redex/model/calculus)
         esterel-calculus/redex/model/instant
         (only-in esterel-calculus/redex/test/binding CB esterel-L)
         esterel-calculus/cross-tests/send-lib)

;; assert-sound : (listof p) (listof S)^3 -> void
;; checks that each step in `ps` is sound
(define (assert-sound ps S_i S_o S_i_on)
  (for ([p (in-list ps)]
        [q (in-list (cdr ps))])
    (unless (sound p q S_i S_o S_i_on)
      (error 'assert-sound
             "failed:\n~a"
             (pretty-format
              `(sound ',p ',q ',S_i ',S_o ',S_i_on)
              #:mode 'write)))))

;; sound : p^2 (listof S)^3 -> boolean
(define (sound p q S_i S_o S_i_on)
  (implies (and (term (CB ,p))
                (term (CB ,q))
                (same-as-sets? (term (FV ,p)) (append S_i S_o))
                (subset? S_i_on S_i)
                (=e1 p q))
           (equal? (eval_std p S_i S_o S_i_on)
                   (eval_std q S_i S_o S_i_on))))

(define (same-as-sets? a b) (and (subset? a b) (subset? b a)))

(define (=e1 p q)
  (member q (apply-reduction-relation calculus:R p)))

;; eval_std : p (listof S)^3 -> (listof S) or #f
;; evaluates `p` for one instant with:
;;  - S_i as the input signals,
;;  - S_o as the output signals, and
;;  - S_i_on as the input signals that are
;;    raised at he beginning of the instant
;; the result is the output signals that got
;; raised or #f if the program is not constructive
(define (eval_std p S_i S_o S_i_on)
  (define θ (for/fold ([θ `·])
                      ([S (in-list (append S_i S_o))])
              (define status
                (cond
                  [(member S S_i_on) 'present]
                  [else 'unknown]))
              `{(sig S ,status) ,θ}))
  (define res (term (instant (ρ ,θ ,p) ())))
  (cond
    [res
     (redex-let
      esterel-eval ([(p (S ...)) res])
      (sort (set->list (set-intersect (list->set S_o) (list->set (term (S ...)))))
            symbol<?))]
    [else #f]))

;; picks a random p and then tries
;; to generate a reduction sequence
;; from it. if it finds a non-empty
;; sequence, then makes some choices
;; about input/output signals and
;; passes it to `assert-sound`
(define (try-for-unsoundness)
  (define _p
    (case (random 2)
      [(0) (list 'R (generate-term #:source calculus:R* 5))]
      [(1) (generate-term esterel-L #:satisfying (CB p) 5)]))
  (when _p
    (define p (clean-up-p (list-ref _p 1)))
    (define p+1s (apply-reduction-relation calculus:R p))
    (unless (null? p+1s)
      (define qs (random-next-steps (pick-one p+1s)))
      (define Ss (shuffle (term (FV ,p))))
      (define S_i (take-random-prefix Ss))
      (define S_o (drop Ss (length S_i)))
      (define S_i_on (take-random-prefix S_i))
      (assert-sound (cons p qs) S_i S_o S_i_on))))

;; random-next-steps : p -> (non-empty-listof p)
;; result is a trace of steps such that
;; each -> reduces to the next
(define (random-next-steps p)
  (let loop ([p p])
    (cond
      [(zero? (random 4)) (list p)]
      [else
       (define qs (apply-reduction-relation calculus:R p))
       (cond
         [(null? qs) (list p)]
         [else (cons p (loop (pick-one qs)))])])))

(define (take-random-prefix l)
  (take l (random (+ 1 (length l)))))

(define/contract (pick-one l)
  (-> (non-empty-listof any/c) any/c)
  (list-ref l (random (length l))))

(module+ test
  (for ([i (in-range 100)])
    (try-for-unsoundness)))
