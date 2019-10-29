#lang racket
(require redex/reduction-semantics
         rackunit
         "../compiler.rkt"
         esterel-calculus/redex/test/generator
         esterel-calculus/redex/model/calculus
         circuitous)

(define counter
  (hash-copy
   (for/hash ([k (in-list (reduction-relation->rule-names ⟶))]
              #:unless
              (regexp-match? #rx"(set|var|shared|if-)" (symbol->string k)))
     (values (symbol->string k) 0))))
(define ATTEMPTS 100)

(redex-check
 esterel-check
 p-pure
 (begin
   ;(displayln (term p-pure))
   (for ([x* (in-list (apply-reduction-relation/tag-with-names ⟶ (term p-pure)))])
     (match-define (list name x) x*)
     (hash-set! counter name
                (add1 (hash-ref counter name)))
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
 #:attempts ATTEMPTS)

(redex-check
 esterel-check
 (ρ θ-pure A p-pure-ext)
 (begin
   #;(displayln (term p-pure-ext))
   (for ([x* (in-list (apply-reduction-relation/tag-with-names ⟶ (term (ρ θ-pure A p-pure-ext))))])
     (match-define (list name x) x*)
     (hash-set! counter name
                (add1 (hash-ref counter name)))
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
 #:attempts ATTEMPTS)

(pretty-print
 counter)
