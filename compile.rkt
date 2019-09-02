#lang rosette
(require booleans/rosette
         (submod booleans/rosette name-manipulation)
         (for-syntax syntax/parse))

(struct wire (+ -))
(define-syntax define/splice
  (syntax-parser
    [(_ n:id)
     #`(begin
         (define #,(+ #'n) (wire-+ n))
         (define #,(- #'n) (wire-- n)))]))

(define 0w (wire #f #t))
(define 1w (wire #t #f))

(define-syntax unsplice
  (syntax-parser
    [(_ n:id)
     #`(wire #,(+ #'n) #,(- #'n))]))
     

;; e WIRE WIRE WIRE WIRE (hashof symbol WIRE) -> Circuit x Wire x (hashof nat WIRE)
(define (sem e GO KILL RES SUSP)
  (define/splice GO)
  (define/splice KILL)
  (define/splice RES)
  (define/splice SUSP)
  (match e
    [`nothing
     (define-wires  #:constraints k
       K0)
     (values
      (and k
           (circuit
            #:interface (GO K0)
            (= K0 GO)))
      0w
      (hash 0 (unsplice K0)))]
    [`pause
     (define-wires #:constraints c
       K0 K1 SEL)
     (values
      (and
       c
       (circuit
        #:interface (GO RES SUSP KILL K0 K1 SEL)
        (= K1 GO)
        (= K0 (and RES reg-out))
        (= SEL reg-out)
        (= reg-in (and (not KILL) reg-set))
        (= reg-set (or is-susp GO))
        (= is-susp (and SUSP reg-out))))
       (unsplice SEL)
       (hash 0 (unsplice K0)
             1 (unsplice K1)))]))

;; expr -> Circuit x Wire x Wire (go, k0)
(define (compile e)
  (define-wires #:constraints w
    GO RES SUSP KILL)
  (define-wires #:constraints k*
    K0*)
  (define-values (s _ h)
    (sem e (unsplice GO) (unsplice RES) (unsplice SUSP) (unsplice KILL)))
  (values
   (and
    w
    (circuit
     #:interface (RES SUSP KILL)
     (= RES #t)
     (= SUSP #t)
     (= KILL #f))
    (if (hash-has-key? h 0) #t k*)
    s)
   (unsplice GO)
   (if (hash-has-key? h 0) (hash-ref h 0) (unsplice K0*))))
    
  