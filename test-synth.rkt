#lang rosette/safe

(require booleans/rosette
         rosette/lib/synthax
         rosette/query/debug)
(module+ test (require rackunit))

(define-synthax from-const
  ([(_ (x ...) ...) (choose x ... ...)]))

(define-synthax (BExpr +args -args k)
  #:base
  (from-const (#t #;#f) +args -args)
  #:else
  (choose
   (from-const (#t #;#f) +args -args)
   (or
    (BExpr +args -args (sub1 k))
    (BExpr +args -args (sub1 k)))
   (and
    (BExpr +args () (sub1 k))
    (BExpr () -args (sub1 k)))))

(define-wires
  #:constraints i
  GO RES SEL SUSP KILL K0 K1
  reg-out reg-in)

(define-circuit (circ1 GO RES SEL SUSP
                       reg-out reg-in KILL
                       K0 K1)
  (= r0 GO)
  ;; pause
  (= l1 GO)
  (= l0 (and RES reg-out))
  (= SEL reg-out)
  (= reg-in (and (not KILL) reg-set))
  (= reg-set (or is-susp GO))
  (= is-susp (and SUSP reg-out))
  ;; synchronizer
  (= K1 (and left1 (and both1 right1)))
  (= K0 (and left0 (and both0 right0)))
  (= left1 (or left0 l1))
  (= right1 (or right0 #f))
  (= both1 (or l1 #f))
  (= left0 (or l0 lem))
  (= right0 (or r0 (not GO)))
  (= both0 (or l0 r0))
  (= lem (or reg-out (not GO))))
  

(define-circuit (circ2
                 GO RES SEL SUSP
                 reg-out reg-in KILL
                 K0 K1)
  (= K1 GO)
  (= K0 (and RES reg-out))
  (= SEL reg-out)
  (= reg-in (and (not KILL) reg-set))
  (= reg-set (or is-susp GO))
  (= is-susp (and SUSP reg-out)))

(define/debug (precondition
               +GO -GO +RES -RES +SEL -SEL
               +SUSP -SUSP
               +reg-out -reg-out +reg-in -reg-in +KILL -KILL
               +K0 -K0 +K1 -K1)
  (and
   ;(defined reg-out)
   (convert (<=> reg-out #f))
   (wire-constraints GO RES SEL SUSP reg-out reg-in KILL K0 K1)))

(define (safe +GO -GO +RES -RES +SEL -SEL
              +SUSP -SUSP
              +reg-out -reg-out +reg-in -reg-in +KILL -KILL
              +K0 -K0 +K1 -K1)
  (implies (BExpr 
            (+GO +RES +SUSP +KILL)
            (-GO -RES -SUSP -KILL)
            0)
           (<=>
            (circ1 GO RES SEL SUSP
                   reg-out reg-in KILL
                   K0 K1)
            (circ2 GO RES SEL SUSP
                   reg-out reg-in KILL
                   K0 K1))))

(define res
  (synthesize
   #:forall (list +GO -GO +RES -RES +SEL -SEL
                  +SUSP -SUSP
                  +reg-out -reg-out
                  +reg-in -reg-in
                  +KILL -KILL
                  +K0 -K0 +K1 -K1)
   #:guarantee
   (assert
    (implies
     (precondition
      +GO -GO +RES -RES +SEL -SEL
      +SUSP -SUSP
      +reg-out -reg-out +reg-in -reg-in +KILL -KILL
      +K0 -K0 +K1 -K1)
     (safe +GO -GO +RES -RES +SEL -SEL
           +SUSP -SUSP
           +reg-out -reg-out +reg-in -reg-in +KILL -KILL
           +K0 -K0 +K1 -K1)))))

(define (do-verify)
  (verify
   #:guarantee
   (assert
    (implies
     (precondition
      +GO -GO +RES -RES +SEL -SEL
      +SUSP -SUSP
      +reg-out -reg-out +reg-in -reg-in +KILL -KILL
      +K0 -K0 +K1 -K1)
     (safe +GO -GO +RES -RES +SEL -SEL
           +SUSP -SUSP
           +reg-out -reg-out +reg-in -reg-in +KILL -KILL
           +K0 -K0 +K1 -K1)))))

(define (verify-correct x)
  (verify
   #:guarantee
   (assert
    (implies
     (precondition
      +GO -GO +RES -RES +SEL -SEL
      +SUSP -SUSP
      +reg-out -reg-out +reg-in -reg-in +KILL -KILL
      +K0 -K0 +K1 -K1)
     (implies x
              (circ2 GO RES SEL SUSP
                     reg-out reg-in KILL
                     K0 K1))))))

(module+ test
  (check-true (sat? (verify-correct #t)))
  (check-true (unsat? (verify-correct #f)))
  (check-true (unsat? (verify-correct (convert (<=> GO #t)))))
  (check-true (unsat? (verify-correct (convert (<=> GO #f)))))
  (check-true (unsat? (verify-correct (defined GO)))))

(print-forms res)

