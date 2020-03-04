#lang racket
(provide test-normal test-ρ)
(require redex/reduction-semantics
         rackunit
         esterel-calculus/circuits/compiler
         esterel-calculus/redex/test/generator
         esterel-calculus/redex/model/calculus
         circuitous
         esterel-calculus/circuits/tests/regression)

(define ATTEMPTS 100)

(define (test-normal iterations)
  (define test-count 0)
  (define start-time (current-seconds))
  (redex-check
   esterel-check
   p-loopy 
   (let ()
     (set! test-count (add1 test-count))
     (when (zero? (modulo test-count 100))
       (printf "running test ~a\n" test-count)
       (printf "has been running for ~a seconds\n" (- (current-seconds) start-time))
       (pretty-print
        counter-table)
       (flush-output))
     (test-term (term p-loopy))
     #;(displayln 'done))
   #:attempts iterations))

(define (test-ρ iterations)
  (define test-count 0)
  (define start-time (current-seconds))
  (redex-check
   esterel-check
   (ρ θ-pure A p-loopy)
   (let ()
     (set! test-count (add1 test-count))
     (when (zero? (modulo test-count 100))
       (printf "running test ~a\n" test-count)
       (printf "has been running for ~a seconds\n" (- (current-seconds) start-time))
       (pretty-print
        counter-table)
       (flush-output))
     (test-term (term (ρ θ-pure A p-loopy))))
   #:attempts iterations))


(module+ test
  (test-normal ATTEMPTS)
  (test-ρ ATTEMPTS)
  (pretty-print
   counter-table))
