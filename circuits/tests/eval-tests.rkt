#lang racket
(require rackunit
         "../compiler.rkt"
         (except-in circuitous FV)
         redex/reduction-semantics)

(check-equal?
 (run/circuit
  'nothing
  '()
  '()
  '())
 '())
(check-equal?
 (run/circuit
  'nothing
  '()
  '()
  '(()))
 (list (set)))
(check-equal?
 (run/circuit
  'nothing
  '()
  '()
  '(() ()))
 (list (set) (set)))
(check-equal?
 (run/circuit
  'pause
  '()
  '()
  '(() ()))
 (list (set) (set)))
(check-equal?
 (run/circuit
  'pause
  '()
  '()
  '(() () ()))
 (list (set) (set) (set)))
(check-equal?
 (run/circuit
  '(emit S)
  '()
  '(S)
  '(() ()))
 (list (set 'S) (set)))
(check-equal?
 (run/circuit
  '(seq (emit S)
        (seq pause (emit S)))
  '()
  '(S)
  '(() ()))
 (list (set 'S) (set 'S)))
(check-equal?
 (run/circuit
  '(seq (emit S)
        (seq pause (emit S)))
  '()
  '(S)
  '(() () ()))
 (list (set 'S) (set 'S) (set)))
(check-equal?
 (run/circuit
  '(present S (emit S1) nothing)
  '(S)
  '(S1)
  '(() ()))
 (list (set) (set)))
(check-equal?
 (run/circuit
  '(present S (emit S1) nothing)
  '(S)
  '(S1)
  '((S) ()))
 (list (set 'S1) (set)))
(check-equal?
 (run/circuit
  (term (seq nothing (exit 0)))
  '()
  '()
  '(()))
 (list (set)))
(test-case "internal eval issues"
  (define p++regs
    (term (compile-esterel/top (trap (seq nothing (exit 0))))))
  (check-equal?
   (length
    (execute
     (make-circuit
      #:inputs empty
      #:outputs empty
      #:register-pairs (second p++regs) 
      (first p++regs))
     '() '() '() '()))
   4))
(check-equal?
 (run/circuit
  (term (trap (seq nothing (exit 0))))
  '()
  '()
  '(() () () ()))
 (list (set) (set) (set) (set)))
(check-equal?
 (run/circuit
  (term (trap (seq (emit S) (exit 0))))
  '()
  '(S)
  '(() () () ()))
 (list (set 'S) (set) (set) (set)))
(check-equal?
 (run/circuit
  (term (loop (seq pause (emit S))))
  '()
  '(S)
  '(() () () ()))
 (list (set) (set 'S) (set 'S) (set 'S)))
(check-equal?
 (run/circuit
  (term (seq (trap (seq pause (seq (emit S) (exit 0))))
             (trap (seq pause (seq (emit S) (exit 0))))))
  '()
  '(S)
  '(() () () ()))
 (list (set) (set 'S) (set 'S) (set)))
(check-equal?
 (run/circuit
  (term (seq (trap (seq pause (seq nothing (exit 0))))
             (trap (seq pause (seq nothing (exit 0))))))
  '()
  '()
  '(() () () ()))
 (list (set) (set) (set) (set)))
(check-equal?
 (run/circuit
  (term (loop (trap (seq pause (seq (emit S) (exit 0))))))
  '()
  '(S)
  '(() () () ()))
 (list (set) (set 'S) (set 'S) (set 'S)))
(test-case "regression tests from random testing"
  (check-equal?
   (run/circuit
    (term (seq pause (emit SA)))
    '(Sr)
    '(Sρ Sbl SA)
    '(() () () ()))
   (list (set) (set 'SA) (set) (set)))
  (check-equal?
   (run/circuit
    (term (seq (suspend pause Sr) (emit SA)))
    '(Sr)
    '(Sρ Sbl SA)
    '((Sr) () (Sr) ()))
   (list (set) (set 'SA) (set) (set)))
  (check-equal?
   (run/circuit
    (term (suspend (suspend (seq pause (emit SA)) Sr) Sr))
    '(Sr)
    '(Sρ Sbl SA)
    '((Sr) () (Sr) ()))
   (list (set) (set 'SA) (set) (set)))
  (check-equal?
   (run/circuit
    (term (seq (suspend (suspend pause Sr) Sr) (emit SA)))
    '(Sr)
    '(Sρ Sbl SA)
    '((Sr) () (Sr) ()))
   (list (set) (set 'SA) (set) (set))))