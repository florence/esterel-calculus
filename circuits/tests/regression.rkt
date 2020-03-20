#lang racket
(provide
 test-term
 counter-table)
(require redex/reduction-semantics
         rackunit
         "../compiler.rkt"
         esterel-calculus/redex/test/generator
         esterel-calculus/redex/model/calculus
         circuitous)
(define initial-counter-table
  (for/hash ([k (in-list (reduction-relation->rule-names ⟶))]
              #:unless
              (regexp-match? #rx"(set|var|shared|if-)" (symbol->string k)))
     (values (symbol->string k) 0)))
(define (reset-hash!)
  (set! counter-table
        (hash-copy initial-counter-table)))
(define counter-table
  (hash-copy initial-counter-table))

(define (test-term t)
  (for ([x* (in-list (apply-reduction-relation/tag-with-names ⟶ t))])
    (match-define (list name x) x*)
    (hash-set! counter-table name
               (add1 (hash-ref counter-table name)))
    (define (check x y guard? classical?)
      (define compile
        (compose
         (if classical? constructive->classical values)
         (if guard? compile-esterel/guard compile-esterel)))
      (check-pred
       unsat?
       (verify-same
        #:constraints (if guard? 'true '(implies --SEL (not GO)))
        (compile x)
        (compile y))
       (format
        "testing ~a\nagainst ~a\nin the ~a~a case\nreduced via ~a"
        (pretty-format x)
        (pretty-format y)
        (if guard? "guarded " "")
        (if classical? "classical" "constructive")
        name)))
    (for ([guard? (in-list (list #f #t))]
          [classical? (in-list (list #f #t))])
      (check t x guard? classical?))))

(module+ test
  (test-term (term (par nothing pause)))
  (test-term (term (trap (par nothing pause))))
  (test-term (term (seq (trap (par nothing pause)) nothing)))
  (test-term (term (seq (par nothing pause) pause)))
  (test-term (term (seq (trap (par nothing pause)) pause)))

  (test-term (term (ρ ((sig SX present) ·) GO (present SX nothing (exit 3)))))

  (reset-hash!))