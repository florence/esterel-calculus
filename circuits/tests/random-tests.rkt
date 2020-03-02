#lang racket
(provide test-normal test-ρ)
(require redex/reduction-semantics
         rackunit
         esterel-calculus/circuits/compiler
         esterel-calculus/redex/test/generator
         esterel-calculus/redex/model/calculus
         circuitous)

(define counter-table
  (hash-copy
   (for/hash ([k (in-list (reduction-relation->rule-names ⟶))]
              #:unless
              (regexp-match? #rx"(set|var|shared|if-)" (symbol->string k)))
     (values (symbol->string k) 0))))
(define ATTEMPTS 100)

(define (test-normal iterations)
  (define test-count 0)
  (define start-time (current-seconds))
  (redex-check
   esterel-check
   p-pure
   (let ()
     (set! test-count (add1 test-count))
     (when (zero? (modulo test-count 100))
       (printf "running test ~a\n" test-count)
       (printf "has been running for ~a seconds\n" (- (current-seconds) start-time))
       (flush-output))
     (for ([x* (in-list (apply-reduction-relation/tag-with-names ⟶ (term p-pure)))])
       (match-define (list name x) x*)
       (hash-set! counter-table name
                  (add1 (hash-ref counter-table name)))
       (assert-same
        #:constraints '(implies (+ SEL) (- GO))
        (constructive->classical
         (compile-esterel (term p-pure)))
        (constructive->classical
         (compile-esterel x)))
       (assert-same
        (constructive->classical
         (compile-esterel/guard (term p-pure)))
        (constructive->classical
         (compile-esterel/guard x))))
     #;(displayln 'done))
   #:attempts iterations))

(define (test-ρ iterations)
  (define test-count 0)
  (define start-time (current-seconds))
  (redex-check
   esterel-check
   (ρ θ-pure A p-pure-ext)
   (let ()
     (set! test-count (add1 test-count))
     (when (zero? (modulo test-count 100))
       (printf "running test ~a\n" test-count)
       (printf "has been running for ~a seconds\n" (- (current-seconds) start-time))
       (flush-output))
     (for ([x* (in-list (apply-reduction-relation/tag-with-names ⟶ (term (ρ θ-pure A p-pure-ext))))])
       (match-define (list name x) x*)
       (hash-set! counter-table name
                  (add1 (hash-ref counter-table name)))
       (assert-same
        #:constraints '(implies (+ SEL) (- GO))
        (constructive->classical
         (compile-esterel (term (ρ θ-pure A p-pure-ext))))
        (constructive->classical
         (compile-esterel x)))
       (assert-same
        (constructive->classical
         (compile-esterel/guard (term (ρ θ-pure A p-pure-ext))))
        (constructive->classical
         (compile-esterel/guard x)))))
   #:attempts iterations))


(module+ test
  (test-normal ATTEMPTS)
  (test-ρ ATTEMPTS)
  (pretty-print
   counter-table))
