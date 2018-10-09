#lang racket


;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require (only-in "../redex/model/shared.rkt" #;quasiquote) ;; don't import quasiquote!
         "send-lib.rkt"
         "send-basics.rkt"
         redex/reduction-semantics)

(provide check-the-examples
         register-calculus-example)

(define examples-to-check '())

(define (register-calculus-example prems conc proof
                                   #:source-file [source-file #f]
                                   #:source-line [source-line #f])
  (set! examples-to-check
        (cons (λ ()
                (when source-file
                  (define short-name
                    (if (path-string? source-file)
                        (let-values ([(base name dir?) (split-path source-file)])
                          name)
                        source-file))
                  (printf "building agda from ~a...\n"
                          (if source-line
                              (~a short-name ":" source-line)
                              short-name)))
                (establish-context
                 (premises "CalcExample"
                           prems
                           proof)
                 (send-set conc)))
              examples-to-check)))

(define (check-the-examples)
  (add-prefix "open import calculus-examples")
  (add-prefix "open import calculus")
  (add-prefix "open import sn-calculus-props")
  (add-prefix "open import eval")
  (add-prefix "open import binding-preserve")
  (add-prefix "open import eval-props")
  (add-prefix "open import calculus.properties")

  (establish-context
   "examplesinpaper.agda"
   (for ([example-to-check (in-list examples-to-check)])
     (example-to-check)))

  (printf "running agda...\n")
  (run-agda "examplesinpaper.agda"))
