#lang racket
(require esterel/front-end)
(module+ test (require "test-harness.rkt"))

(define reincarnation1
  (esterel-machine
   #:inputs () #:outputs (O1 O2)
   (loop&
    (signal& S
     (present& S (emit& O1) (emit& O2))
     pause&
     (emit& S)
     (present& S (emit& O1) (emit& O2))))))

(module+ test
  (test-seq
   reincarnation1
   (() (O2))
   (() (O1 O2))
   (() (O1 O2))))


(define reincarnation2
  (esterel-machine
   #:inputs () #:outputs (O1 O2)
   (loop&
    (signal& S
     (trap& T
            (par&
             (seq& pause& (emit& S) (exit& T))
             (loop&
              (present& S (emit& O1) (emit& O2))
              pause&)))))))

(module+ test
  (test-seq
   reincarnation2
   (() (O2))
   (() (O1 O2))
   (() (O1 O2))))
