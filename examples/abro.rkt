#lang racket
(require "../front-end.rkt" redex/reduction-semantics)
(define abro-machine
  (esterel-machine
   #:inputs (A B R) #:outputs (O)
   (loop-each&
    R
    (seq& (par& (await& A) (await& B))
          (emit& O)))))

(pretty-print (machine-prog abro-machine))
(eval-top abro-machine '(A))
