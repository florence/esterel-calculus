#lang racket
(require rackunit
         "../compiler.rkt"
         (except-in circuitous FV)
         (prefix-in circ: circuitous)
         redex/reduction-semantics
         (for-syntax syntax/parse))

(define-syntax check-verify-same
  (syntax-parser
    [(_ pred b ... c1 c2)
     #`(let ([x c1]
             [y c2])
         #,(syntax/loc this-syntax
             (check-pred
              pred
              (circ:verify-same
               b ... x y)))
         #,(syntax/loc this-syntax
             (check-pred
              pred
              (circ:verify-same
               b ...
               (constructive->classical c1)
               (constructive->classical c2)))))]))
(check-verify-same
 unsat?
 (compile-esterel (term (par nothing nothing)))
 (compile-esterel (term nothing)))
(check-verify-same
 unsat?
 (compile-esterel (term (par (exit 2) nothing)))
 (compile-esterel (term (exit 2))))
(check-verify-same
 unsat?
 (compile-esterel (term (par (exit 2) (exit 4))))
 (compile-esterel (term (exit 4))))
(check-verify-same
 unsat?
 (compile-esterel (term (signal Ss (present Ss (emit S1) (emit S2)))))
 (compile-esterel (term (emit S2))))
(check-verify-same
 unsat?
 (compile-esterel (term (suspend nothing Ss)))
 (compile-esterel (term nothing)))
(check-verify-same
 unsat?
 (compile-esterel (term (suspend (exit 2) Ss)))
 (compile-esterel (term (exit 2))))
(check-verify-same
 unsat?
 (compile-esterel (term (trap nothing)))
 (compile-esterel (term nothing)))
(check-verify-same
 unsat?
 (compile-esterel (term (trap (exit 0))))
 (compile-esterel (term nothing)))
(check-verify-same
 unsat?
 (compile-esterel (term (trap (exit 4))))
 (compile-esterel (term (exit 3))))
(check-verify-same
 unsat?
 (compile-esterel (term (par (nts p 1) (nts q 1))))
 (compile-esterel (term (par (nts q 1) (nts p 1)))))
(check-verify-same
 unsat?
 (compile-esterel (term (par (nts p 5) (nts q 5))))
 (compile-esterel (term (par (nts q 5) (nts p 5)))))
(check-verify-same
 unsat?
 (compile-esterel (term (suspend nothing S)))
 (compile-esterel (term nothing)))
(check-verify-same
 unsat?
 (compile-esterel (term (par pause (exit 0))))
 (compile-esterel (term (exit 0))))
(check-verify-same
 unsat?
 (compile-esterel (term (suspend (par pause (exit 0)) S)))
 (compile-esterel (term (exit 0))))
(check-verify-same
 list?
 (compile-esterel (term (suspend nothing S)))
 (compile-esterel (term (exit 2))))
(check-verify-same
 list? 
 (compile-esterel (term (signal S (present S (emit S) (emit S)))))
 (compile-esterel (term nothing)))
(check-verify-same
 list?
 (compile-esterel (term
                   (signal S
                     (seq (emit S)
                          (present S (exit 2) nothing)))))
 (compile-esterel (term (exit 2))))
(check-verify-same
 list?
 (compile-esterel
  (term (signal S
          (seq (emit S)
               (present S (exit 2) nothing)))))
 (compile-esterel (term (exit 2))))
(check-pred
 unsat?
 (verify-same
 #:constraints '(not GO)
 (compile-esterel
  (term (signal S
          (seq (emit S)
               (present S (exit 2) nothing)))))
 (compile-esterel (term (exit 2)))))
(check-pred
 unsat?
 (verify-same
  #:constraints '(- GO)
  (constructive->classical
   (compile-esterel
    (term (signal S
            (seq (emit S)
                 (present S (exit 2) nothing))))))
  (constructive->classical
   (compile-esterel (term (exit 2))))))
(check-pred
 unsat?
 (verify-same
  #:constraints 'GO
  (compile-esterel
   (term (signal S
           (seq (emit S)
                (present S (exit 2) nothing)))))
  (compile-esterel (term (exit 2)))))
(check-pred
 unsat?
 (verify-same
  #:constraints '(+ GO)
  (constructive->classical
   (compile-esterel
    (term (signal S
            (seq (emit S)
                 (present S (exit 2) nothing))))))
  (constructive->classical
   (compile-esterel (term (exit 2))))))
(check-verify-same
 unsat?
 (compile-esterel (term (exit 2)))
 (compile-esterel
  (term
   (par (par nothing (exit 1))
        (par (exit 0)
             (par (exit 1)
                  (exit 2)))))))
(check-verify-same
 unsat?
 (compile-esterel (term (seq (suspend (suspend pause Sr) Sr) (emit SA))))
 (compile-esterel (term (suspend (suspend (seq pause (emit SA)) Sr) Sr))))
(check-verify-same
 unsat?
 (compile-esterel (term (seq (suspend (suspend pause Sr) Sr) (emit SA))))
 (compile-esterel (term (seq (suspend pause Sr) (emit SA)))))
    
(check-verify-same
 list?
 (compile-esterel (term (ρ · GO nothing)))
 (compile-esterel (term nothing)))
(check-pred
 unsat?
 (verify-same
  #:constraints 'GO
  (compile-esterel (term (ρ · GO nothing)))
  (compile-esterel (term nothing))))
(check-pred
 unsat?
 (verify-same
  #:constraints '(+ GO)
  (constructive->classical
   (compile-esterel (term (ρ · GO nothing))))
  (constructive->classical
   (compile-esterel (term nothing)))))
(check-pred
 unsat?
 (verify-same
  #:constraints 'GO
  (compile-esterel (term (ρ {(sig S present)·} GO nothing)))
  (compile-esterel (term nothing))))
(check-pred
 unsat?
 (verify-same
  #:constraints '(+ GO)
  (constructive->classical
   (compile-esterel (term (ρ {(sig S present)·} GO nothing))))
  (constructive->classical
   (compile-esterel (term nothing)))))
(check-pred
 unsat?
 (verify-same
  #:constraints 'GO
  (compile-esterel (term (ρ {(sig S unknown)·} GO nothing)))
  (compile-esterel (term nothing))))
(check-pred
 unsat?
 (verify-same
  #:constraints '(+ GO)
  (constructive->classical
   (compile-esterel (term (ρ {(sig S unknown)·} GO nothing))))
  (constructive->classical
   (compile-esterel (term nothing)))))


(check-pred
 unsat?
 (verify-same
 #:constraints '(implies --SEL (not GO))
 (compile-esterel (term (ρ · GO (seq nothing nothing))))
 (compile-esterel (term (ρ · GO nothing)))))
(check-pred
 unsat?
 (verify-same
  #:constraints '(implies (+ --SEL) (- GO))
  (constructive->classical
   (compile-esterel (term (ρ · GO (seq nothing nothing)))))
  (constructive->classical
   (compile-esterel (term (ρ · GO nothing))))))
    
(check-verify-same
 unsat?
 (compile-esterel (term (ρ · GO (seq nothing nothing))))
 (compile-esterel (term (ρ · GO nothing))))

(check-verify-same
 unsat?
 (compile-esterel (term (seq (exit 1) (suspend pause Sk))))
 (compile-esterel (term (exit 1))))
    
(test-case "state and Can"
  (define p
    (compile-esterel
     (term
      (signal S2
        (seq
         (present S2 (emit S1) nothing)
         (seq pause
              (emit S2)))))))
  (define q
    (compile-esterel
     (term
      (signal S2
        (seq
         nothing
         (seq pause
              (emit S2)))))))
  (check-verify-same
   list?
   p q)
  (check-pred
   unsat?
   (verify-same
    #:constraints (term (implies --SEL (not GO)))
    p q))
  (check-pred
   unsat?
   (verify-same
    #:constraints (term (implies (+ --SEL) (- GO)))
    (constructive->classical p)
    (constructive->classical q))))