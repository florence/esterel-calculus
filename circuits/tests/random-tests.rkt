#lang racket
(require redex/reduction-semantics
         rackunit
         "../compiler.rkt"
         esterel-calculus/redex/test/generator
         esterel-calculus/redex/model/calculus
         circuitous)

(define counter
  (hash-copy
   (for/hash ([k (in-list (reduction-relation->rule-names ⟶))])
     (values (symbol->string k) 0))))
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
 #:attempts 150)

(redex-check
 esterel-check
 p-pure-ext
 (begin
   #;(displayln (term p-pure-ext))
   (for ([x* (in-list (apply-reduction-relation/tag-with-names ⟶ (term p-pure-ext)))])
     (match-define (list name x) x*)
     (hash-set! counter name
                (add1 (hash-ref counter name)))
     (assert-same
      #:constraints '(implies (+ SEL) (- GO))
      (constructive->classical
       (compile-esterel (term p-pure-ext)))
      (constructive->classical
       (compile-esterel x)))
     (assert-same
      (constructive->classical
       (compile-esterel/guard (term p-pure-ext)))
      (constructive->classical
       (compile-esterel/guard x)))))
 #:attempts 150)

(pretty-print
 counter)
