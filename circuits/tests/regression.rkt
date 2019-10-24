#lang racket
(require redex/reduction-semantics
         rackunit
         "../compiler.rkt"
         esterel-calculus/redex/test/generator
         esterel-calculus/redex/model/calculus
         circuitous)

(define (test-term t)
  (for ([x* (in-list (apply-reduction-relation/tag-with-names ⟶ t))])
    (match-define (list name x) x*)
    (test-case (~a t)
      (check-pred
       unsat?
       (verify-same
        #:constraints '(implies SEL (not GO))
        (compile-esterel t)
        (compile-esterel x))
       (format
        "testing ~a\nagainst ~a\nin the constructive case\nreduced via ~a"
        (pretty-format t)
        (pretty-format x)
        name))
      (check-pred
       unsat?
       (verify-same
        #:constraints '(implies (+ SEL) (- GO))
        (constructive->classical (compile-esterel t))
        (constructive->classical (compile-esterel x)))
       (format
        "testing ~a\nagainst ~a\nin the classical case\nreduced via ~a"
        (pretty-format t)
        (pretty-format x)
        name)))))

(test-term (term (par nothing pause)))
(test-term (term (trap (par nothing pause))))
(test-term (term (seq (trap (par nothing pause)) nothing)))
(test-term (term (seq (par nothing pause) pause)))
(test-term (term (seq (trap (par nothing pause)) pause)))