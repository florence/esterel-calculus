#lang racket
(require "../front-end.rkt")
(module+ test  (require "test-harness.rkt"))
(define emit
  (esterel-machine
   #:inputs () #:outputs (O)
    (emit& O)))
(module+ test
  (test-seq
   emit
   (() (O))
   (() (O))
   (() (O))))

(define emit/pause
  (esterel-machine
   #:inputs () #:outputs (O)
   (seq& (emit& O) pause&)))
(module+ test
  (test-seq
   emit/pause
   (() (O))
   (() ())
   (() (O))
   (() ())))

(define emit/loop
  (esterel-machine
   #:inputs () #:outputs (O)
   (loop& (seq& (emit& O) (seq& pause& pause&)))))
(module+ test
  (test-seq
   emit/loop
   (() (O))
   (() ())
   (() (O))
   (() ())))

(define input
  (esterel-machine
   #:inputs (A) #:outputs (O)
   (present& A (emit& O))))
(module+ test
  (test-seq
   input
   ((A) (O))
   ((A) (O))
   ((A) (O))
   (() ())
   ((A) (O))
   (() ())
   (() ())))


(define par
  (esterel-machine
   #:inputs () #:outputs (O1 O2)
   (par& (seq& pause& (emit& O2))
         (seq& (emit& O1) pause&))))
(module+ test
  (test-seq
   par
   (() (O1))
   (() (O2))
   (() (O1))
   (() (O2))
   (() (O1))
   (() (O2))
   (() (O1))
   (() (O2))))
(define loop/trap
  (esterel-machine
   #:inputs (A) #:outputs (O)
   (seq&
    (trap& T
           (loop& (present& A (exit& T) pause&)))
    (emit& O))))
(module+ test
  (test-seq
   loop/trap
   (() ())
   (() ())
   ((A) (O))))

(define loop/trap/pause
  (esterel-machine
   #:inputs (A) #:outputs (O)
   (seq&
    (trap& T
           (loop& (seq& pause& (present& A (exit& T)))))
    (emit& O))))
(module+ test
  (test-seq
   loop/trap/pause
   (() ())
   (() ())
   (() ())
   ((A) (O))))
