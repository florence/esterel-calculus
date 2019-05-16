#lang racket

(require esterel-calculus/hiphop/find
         esterel-calculus/hiphop/parse
         esterel-calculus/front-end-tester
         esterel-calculus/redex/model/instant)
(define-logger hiphop)

; path-string? ->
; Runs the hiphop.js test at the given path or by the given name.
(define (run-hiphop-test path-or-name)
  (define path (hiphop-test->path path-or-name))
  (display (format "Running test ~a\n" path))
  (define p (load-hiphop-test path))
  (log-hiphop-debug "parsed program to ~a" (pretty-format p))
  (eval-front-end-test p)
  (void))

; ->
(define (run-all-hiphop-tests)
  (parameterize ([current-check-standard-implies-calculus #f])
    (for-each run-hiphop-test (find-all-hiphop-tests))))

(module+ test
  (run-all-hiphop-tests))
