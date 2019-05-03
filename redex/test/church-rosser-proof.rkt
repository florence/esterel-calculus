#lang racket
(provide (all-defined-out))
(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/calculus/variants/control
         "model-test.rkt"
         "generator.rkt"
         rackunit
         (for-syntax syntax/parse
                     racket/list
                     racket/syntax
                     racket/sequence))

(module+ test (require rackunit))

(define-extended-language esterel-gen esterel-eval
  (e ::= (+ s/l ...))
  (s/l ::= s x n)
  (ev ::= n)
  (i ::= (emit S) (<= s e) (:= x e))
  (R ::=
     i
     (present S p q)
     (if x p q) (shared s := e p) (var x := e p)))

(define-logger esterel-calculus)

;; property:
;; p RPar q && p RPar q'
;; => ∃q'', q Rpar q'' && q' Rpar q''

(define (check-par-diamond)
  (redex-check
   esterel-gen
   p
   (do-test `p)
   #:prepare fixup2
   #:attempts 1000)
  (redex-check
   esterel-gen
   (p (name i (S_!_g S_!_g ...)) (name o (S_!_g S_!_g ...)) ((S ...) ...))
   (let-values ([(p e) (calc-shuffle `p 3)])
     (do-test p))
   #:prepare fixup
   #:attempts 100))

(define (reduce p)
  (apply-reduction-relation ⟶ p))
(define (zero-to-two p)
  (define one (reduce p))
  (append
   (cons p one)
   (append-map reduce one)))

(define (do-test p)
  (redex-let
   esterel-eval
   ([p p])
   (log-esterel-calculus-debug "staring with ~a" (pretty-format (term p)))
   (define candidates (reduce `p))
   (log-esterel-calculus-debug "available steps: ~a" (pretty-format candidates))
   (define result
     (for*/and ([c1 (in-list candidates)]
                [c2 (in-list candidates)])
       (define out1 (zero-to-two c1))
       (define out2 (zero-to-two c2))
       (log-esterel-calculus-debug "can from ~a to ~a" c1 (pretty-format out1))
       (log-esterel-calculus-debug "can from ~a to ~a" c2 (pretty-format out2))
       (define result
         (for*/or ([o1 (in-list out1)]
                   [o2 (in-list out2)])
           (equal? o1 o2)))
       (unless result
         (log-esterel-calculus-error "p = ~a\n" `p)
         (log-esterel-calculus-error "q = ~a\n" c1)
         (log-esterel-calculus-error (pretty-format out1))
         (log-esterel-calculus-error "q' = ~a\n" c2)
         (log-esterel-calculus-error (pretty-format out2)))
       result))
   result))

(define (fixup2 p)
  `(clear-dups ,p))

(define-metafunction esterel-eval
  clear-dups : any -> any
  [(clear-dups (ρ θ A p))
   (ρ (remove-dups θ) A (clear-dups p))]
  [(clear-dups (loop p))
   (loop (clear-dups p))]
  [(clear-dups (any ...))
   ((clear-dups any) ...)]
  [(clear-dups any) any])

(define-metafunction esterel-eval
  remove-dups : θ -> θ
  [(remove-dups θ) θ])

(module+ test
  (test-case ""
    (check-true
     (do-test
      `(par
        (ρ {(sig S present) ·} GO nothing)
        (ρ {(sig ST present) ·} GO nothing))))

    (check-true
     (do-test
      `(par
        (ρ {(sig S present) ·} WAIT nothing)
        (ρ {(sig ST present) ·} WAIT nothing))))
    (check-true
     (do-test
      `(par
        (ρ {(sig S present) ·} GO nothing)
        (ρ {(sig ST present) ·} WAIT nothing))))
    (check-true
     (do-test
      `(par
        (ρ {(sig S present) ·} WAIT nothing)
        (ρ {(sig ST present) ·} GO nothing))))
    (check-true
     (do-test
      `(par
        (ρ {(sig S unknown) ·} GO nothing)
        (ρ {(sig ST unknown) ·} WAIT nothing))))


    (check-true
     (do-test
      `(ρ · WAIT
          (par
           (ρ · GO nothing)
           (ρ · WAIT nothing)))))
    (check-true
     (do-test
      `(ρ · GO
          (par
           (ρ · GO nothing)
           (ρ · WAIT nothing)))))


    
    (check-true
     (do-test
      `(ρ {(sig S unknown)
           ((sig S1 unknown)
            ((var· x 0) ·))}
          GO
          (if x nothing (emit S1)))))
    (check-true
     (do-test
      `(ρ {(sig S unknown)
           ((sig S1 unknown)
            ((var· x 0) ·))}
          WAIT
          (if x nothing (emit S1)))))
    (check-true
     (do-test
      `(seq
        (ρ ((sig Sg350095 unknown) ·) GO pause)
        (loop pause))))
    (check-true
     (do-test
      `(seq
        (ρ ((sig Sg350095 unknown) ·) WAIT pause)
        (loop pause))))
    (check-true
     (do-test
      `(seq
        (ρ
         ((sig Sg13633 unknown) ·)
         GO
         (par
          pause
          (seq
           (emit Sg13633)
           nothing)))
        (seq nothing nothing))))
    (check-true
     (do-test
      `(seq
        (ρ
         ((sig Sg13633 unknown) ·)
         WAIT
         (par
          pause
          (seq
           (emit Sg13633)
           nothing)))
        (seq nothing nothing))))
    (check-true
     (do-test
      `(seq
        (ρ
         ((sig Sg144814 absent) ((sig Sg144815 unknown) ·))
         GO
         (par
          pause
          (present Sg144814 nothing (emit Sg144815))))
        (loop pause))))
    (check-true
     (do-test
      `(seq
        (ρ
         ((sig Sg144814 absent) ((sig Sg144815 unknown) ·))
         WAIT
         (par
          pause
          (present Sg144814 nothing (emit Sg144815))))
        (loop pause))))
    (check-true
     (do-test
      `(par
         (signal SxYWk (shared sYpw := (+) (exit 0)))
         (ρ
          ·
          GO
          (shared sn := (+) pause)))))
    (check-true
     (do-test
      `(par
         (signal SxYWk (shared sYpw := (+) (exit 0)))
         (ρ
          ·
          WAIT
          (shared sn := (+) pause)))))
    (check-true
     (do-test
      `(par
         (signal SxYWk (shared sYpw := (+) (exit 0)))
         (ρ
          ·
          GO
          (shared sn := (+) pause)))))
    (check-true
     (do-test
      `(par
         (signal SxYWk (shared sYpw := (+) (exit 0)))
         (ρ
          ·
          WAIT
          (shared sn := (+) pause)))))
    (check-par-diamond)))


(define-relation esterel-eval
   ~ ⊂ E x E
   [(~ hole hole)]
   [(~ (seq E q) (seq E_* q_*))
    (~ E E_*)]
   [(~ (par E q) (par E_* q_*))
    (~ E E_*)]
   [(~ (par p E) (par p_* E_*))
    (~ E E_*)]
   [(~ (trap E) (trap E_*))
    (~ E E_*)]
   [(~ (suspend E S) (suspend E_* S))
    (~ E E_*)])

(module+ test
  (let ()
    (local-require "binding.rkt")
    (define-judgment-form esterel-L
      #:mode (epull I)
      [(R-in-E p)
       (θ-in-E p)
       -------------
       (epull p)])

    (define-judgment-form esterel-L
      #:mode (R-in-E I)
      [(R-in-E R)]
      [(R-in-E p)
       ---------
       (R-in-E (seq p q))]
      [(R-in-E p)
       ---------
       (R-in-E (par p q))]
      [(R-in-E q)
       -------------
       (R-in-E (par p q))]
      [(R-in-E p)
       -------------
       (R-in-E (trap p))]
      [(R-in-E p)
       ------------
       (R-in-E (suspend p S))])

    (define-judgment-form esterel-L
      #:mode (θ-in-E I)
      [(θ-in-E (ρ θ A p))]
      [(θ-in-E p)
       ------------
       (θ-in-E (seq p q))]
      [(θ-in-E p)
       ----------
       (θ-in-E (par p q))]
      [(θ-in-E q)
       ----------
       (θ-in-E (par p q))]
      [(θ-in-E p)
       ---------
       (θ-in-E (trap p))]
      [(θ-in-E p)
       ------------
       (θ-in-E (suspend p S))])

    #|
    ∀ E_in1, R, E_in2, θ, p_in
    E_in[R] = E_in2[(ρ θ p_in)] => ∃E_out s.t E_out[R] = E_in2[p_in], E_out ~ E_in1
    |#
    (define-judgment-form esterel-L
      #:mode (prop I)
      [(where (in-hole E_in1 R) p_in)
       (where (in-hole E_in2 (ρ θ A p)) p_in)
       (where (in-hole E_out R) (in-hole E_in2 p))
       (~ E_out E_in1)
       ----------------
       (prop p_in)])

    (redex-check
     esterel-L
     #:satisfying (epull p)
     (judgment-holds (prop p))
     #:attempts 1000)))
