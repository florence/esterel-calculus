#lang rosette

(require booleans/rosette
         rosette/lib/synthax
         rosette/query/debug)


(define-wires
  #:constraints c
  GO RES SUSP KILL K0 K1 reg-out)

(define-circuit (left GO RES SUSP KILL K0 K1)
  (= lem (not (or #f GO)))
  (= l0 #f)
  (= l1 #f)
  (= l2 GO)
  (= rem (not (or r-sel GO)))
  (= r0 (and reg-out RES))
  (= r1 GO)
  (= r2 #f)
  (= r-sel reg-out)
  (= reg-in (and (not do-kill) reg-set))
  (= reg-set (or GO is-susp))
  (= is-susp (and SUSP r-sel))
  (= do-kill (or KILL I2))
  
  (= K0 (or I0 I2))
  (= K1 I1)
  
  (= SEL reg-out)
  ;; synchronizer
  (= left0 (or l0 lem))
  (= both0 (or l0 r0))
  (= right0 (or r0 rem))
  (= I0 (and left0 (and both0 right0)))
  (= left1 (or left0 l1))
  (= both1 (or l1 r1))
  (= right1 (or right0 r1))
  (= I1 (and left1 (and both1 right1)))
  (= left2 (or left1 l2))
  (= both2 (or l2 r2))
  (= right2 (or right1 r2))
  (= I2 (and left2 (and both2 right2))))

(define-circuit (end GO RES SUSP KILL K0 K1)
  (= K0 GO)
  (= K1 false)
  (= SEL false))


(define r
  (verify
   #:assume
   (assert
    (and (convert (<=> reg-out #f))
         c))
   #:guarantee
   (assert (<=>
            (end GO RES SUSP KILL K0 K1)
            (left GO RES SUSP KILL K0 K1)))))

(define (simplify-model s)
  (define h (model s))
  (define (get-minus k)
    (for/first ([(k* v) (in-hash h)]
                #:when
                (and
                 (not (eq? k k*))
                 (equal? (substring (~a k) 1)
                         (substring
                          (~a k*)
                          1))))
      (displayln (list k k*))
      v))
         
  (for/hash ([(k v) (in-hash h)]
             #:when
             (~a k))
    (values
     k
     (match* (v (get-minus k))
       [(#f #f) '⊥]
       [(#t #f) #t]
       [(#f #t) #f]))))
          