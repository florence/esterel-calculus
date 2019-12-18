#lang racket
(provide clause compile-def esterel-interface)
(require diagrama diagrama/circuit pict racket/syntax
         "proof-extras.rkt"
         "redex-rewrite.rkt"
         syntax/parse/define)

(define (textify i)
  (define s (~a i))
  (match (string-split s "_")
    [(list x) (text x)]
    [(list x y)
     (hbl-append
      (text x)
      (text y '(subscript)))]))

(define (esterel-interface l
                           #:tag-prefix [tag* #f]
                           #:extra-input-signals [si empty]
                           #:extra-output-signals [so empty]
                           #:wire-length [wire-length 2])
  (define wire-spacing 2)
  (define tag (or tag* (format-symbol "~a~a" 'INTERFACE (random 10000))))
  (define (tg . t)
    (format-symbol "~a~a" tag (apply ~a t)))
  (define h (* wire-spacing 6))
  (define w (* wire-spacing (+ (length (append si so)) 5)))
  (define box
    (with-unit
     (lambda (u)
       (img
        (filled-rectangle (* u w) (* u h) #:color "white")))))
  (define (add-wire dir t)
    (define-values (there back)
      (case dir
        [(up) (values line-up move-down)]
        [(down) (values line-down move-up)]
        [(left) (values line-left move-right)]
        [(right) (values line-right move-left)]))
    (after
     (save (back .5) (tag-location (tg t '-label)))
     (save (there wire-length)
           (tag-location (tg t)))))
  (define wires
    (after
     (save
      (move-up (/ h 2)) (move-left (/ w 2))
      (move-down wire-spacing) (add-wire 'left 'GO)
      (move-down wire-spacing) (add-wire 'left 'RES)
      (move-down wire-spacing) (add-wire 'left 'SUSP)
      (move-down wire-spacing) (add-wire 'left 'KILL))
     (save (move-up (/ h 2)) (move-left (/ w 2))
           (move-right (* 2 wire-spacing))
           (add-wire 'up 'E_i)
           (for/after ([s (in-list si)])
             (after (move-right wire-spacing) (add-wire 'up s))))
     (save (move-up (/ h 2)) (move-right (/ w 2))
           (move-left (* 2 wire-spacing)) (add-wire 'up 'E_o)
           (for/after ([s (in-list so)])
             (after (move-left wire-spacing) (add-wire 'up s))))
     (save (move-up (/ h 2)) (move-right (/ w 2))
           (move-down wire-spacing) (add-wire 'right 'SEL)
           (move-down wire-spacing) (add-wire 'right 'K0) 
           (move-down wire-spacing) (add-wire 'right 'K1)
           (move-down wire-spacing) (add-wire 'right 'K2)
           (move-down wire-spacing) (move-left .5) (tag-location (tg '...-label)))))
  (define (add-label s align)
    (after (move-to-tag (tg s '-label))
           (img (textify s) align)))
  (define labels
    (after
     (for/after ([t (in-list '(GO RES SUSP KILL))])
       (add-label t 'lc))
     (for/after ([t (in-list '(SEL K0 K1 K2 ...))])
       (add-label t 'rc))
     (for/after ([t (in-sequences
                     (in-list '(E_o E_i))
                     (in-list si)
                     (in-list so))])
       (add-label t 'ct))))
  (after
   wires
   box
   (img l)
   labels))

(define input-spacing 3)
(define fab-four
  (after (tag-location 'GO)
         (move-down input-spacing) (tag-location 'RES)
         (move-down input-spacing) (tag-location 'SUSP)
         (move-down input-spacing) (tag-location 'KILL)))
         

(define basic-interface 
  (esterel-interface (blank)))
(define signal-pict
  (after
   (esterel-interface (es (compile p))
                      #:tag-prefix '||
                      #:extra-input-signals '(S_i)  #:extra-output-signals '(S_o))
   (move-to-tag 'S_i)
   (line-to-tag 'S_o)))
(define (only-kode n)
  (after
   (img (textify "GO") 'rc)
   (line-right 4)
   (before
    (buffer)
    (line-right 4)
    (img (textify (~a "K" n)) 'lc))))
(define nothing (only-kode 0))
(define emit
  (after
   (img (textify "GO") 'rc)
   (line-right 3)
   (split
    (after
     (line-up 2)
     (line-right 3)
     (before (buffer)
             (line-right 3)
             (img (textify "S_o") 'lc)))
    (after
     (line-down 2)
     (line-right 3)
     (before (buffer)
             (line-right 3)
             (img (textify "K0") 'lc))))))

(define pause
  (let ()
    (define inputs fab-four)
    (define susp-and
      (after
       (move-to-tag 'SUSP)
       (line-right 6) (move-down 1)
       (and-gate #:tag-out 'susp-and-out
                 #:tag-in3 'susp-and-sel)))
    (define susp-or
      (after
       (move-to-tag 'susp-and-out)
       (line-right 3) (move-up 1)
       (or-gate #:tag-in1 'susp-or-go
                #:tag-out 'susp-or-out)))
    (define susp-and2
      (after
       (move-to-tag 'susp-or-out)
       (line-right 3) (move-down 1)
       (and-gate #:tag-in3 'susp-and-kill
                 #:tag-out 'susp-out-reg
                 #:in3 #t)))
    (define reg
      (after
       (move-to-tag 'susp-out-reg)
       (line-right 3)
       (register
        #:tag-out 'reg-out)))
    (define k0-and
      (after
       (move-to-tag 'reg-out)
       (move-right input-spacing) (move-up 1)
       (and-gate
        #:tag-in1 'k0-and-res
        #:tag-in3 'k0-and-sel
        #:tag-out 'k0-r)))
    (define wire-k0
      (after
       (move-to-tag 'k0-r)
       (line-right 1)
       (tag-location 'K0)))
    (define wire-sel
      (after
       (move-to-tag 'reg-out)
       (split
        (line-to-tag 'k0-and-sel)
        (after
         (line-down input-spacing)
         (split
          (with-loc
           (lambda (_ y)
             (with-locations-of
              'K0
              (lambda (x _)
                (after
                (line-to x y)
                (tag-location 'SEL))))))
          (line-to-tag 'susp-and-sel))))))
    (define wire-kill
      (line-between 'KILL 'susp-and-kill))
    (define wire-go
      (with-locations-of
       'GO 'susp-or-go 'K0
       (lambda (gx gy x y kx ky)
         (after
          (move-to gx gy)
          (line-to x gy)
          (split
           (line-to-tag 'susp-or-go)
           (after
            (line-to (- kx (* 2 input-spacing)) gy)
            (before
             (buffer)
             (line-to kx gy)
             (tag-location 'K1))))))))
    (define wire-labels
      (after
       (move-to-tag 'GO) (img (textify "GO") 'rc)
       (move-to-tag 'SUSP) (img (textify "SUSP") 'rc)
       (move-to-tag 'RES) (img (textify "RES") 'rc)
       (move-to-tag 'KILL) (img (textify "KILL") 'rc)
       (move-to-tag 'K0) (img (textify "K0") 'lc)
       (move-to-tag 'K1) (img (textify "K1") 'lc)
       (move-to-tag 'SEL) (img (textify "SEL") 'lc)))
    (define wire-res
      (after
       (move-to-tag 'RES)
       (line-to-tag 'k0-and-res)))
    (after
     inputs
     susp-and
     susp-or
     susp-and2
     reg
     k0-and
     wire-k0
     wire-sel
     wire-kill
     wire-go
     wire-res
     wire-labels)))


(define present-pict
  (let ()
    (define p
      (esterel-interface (es (compile p)) #:tag-prefix 'p))
    (define q
      (esterel-interface (es (compile q)) #:tag-prefix 'q))
    (define tag-setup
      (after
       (save
        (move-up 6)
        (tag-location 'E)
        (move-down 1) (tag-location 'S))
       (tag-location 'GO)
       (move-down 3) (tag-location 'RES)
       (move-down 3) (tag-location 'SUSP)
       (move-down 3) (tag-location 'KILL)))
    (define then-and
      (after
       (move-to-tag 'pGO)
       (line-left 6)
       (and-gate #:tag-in1 'GO1
                 #:tag-in3 'S1
                 #:tag-out 'pGOwrite)))
    (define else-and
      (after
       (move-to-tag 'qGO)
       (line-left 6)
       (and-gate #:tag-in1 'S2 #:in1 #t
                 #:tag-in3 'GO2
                 #:tag-out 'qGOwrite)))
    (define inners
      (after
       (save p)
       (move-down 15)
       q))
    (define go-wires
      (after
       (move-to-tag 'GO1)
       (move-left 3) (tag-location 'GO)
       (save (label "GO" 'left))
       (line-right 2)
       (split
        (line-to-tag 'GO1)
        (line-to-tag 'GO2 #:h-first #f))))
    (define (wires start end sp lbl)
      (after
       (move-to-tag start)
       (line-left sp)
       (split
        (line-to-tag end #:h-first #f)
        (with-locations-of
         'GO start
         (lambda (x _ __ y)
           (after
            (line-to x y)
            (label lbl 'left)))))))
    (define E_i
      (after
       (move-to-tag 'pE_i)
       (line-up 2)
       (line-left 5)
       (split
        (line-to-tag 'qE_i #:h-first #f)
        (with-locations-of
         'GO 'pE_i
         (lambda (x _ __ y)
           (after
            (line-to x (- y 2))
            (tag-location 'E_i)
            (label "E_i" 'left)))))))
    (define E_o
      (after
       (move-to-tag 'pE_o)
       (line-up 2)
       (line-right 20)
       (move-down 1)
       (tag-location 'Eor)
       (or-gate #:tag-in1 '_
                #:tag-in3 'qE_qo
                #:tag-out 'E_oo)
       (move-to-tag 'E_oo)
       (label "E_o" 'right)
       (move-to-tag 'qE_qo)
       (line-left 12)
       (line-to-tag 'qE_o #:h-first #f)))
    (define outputs
      (let ([space (move-down 6.34)])
        (after
         (with-locations-of
          'Eor 'pSEL
          (lambda (x _ __ y)
            (move-to x y)))
         (move-down 1)
         (or-gate #:tag-in1 'pSELor
                  #:tag-in2 'qSELor
                  #:tag-out 'oSEL)
         (save (move-to-tag 'oSEL)
               (label "SEL" 'right))
         space
         (or-gate #:tag-in1 'pK0or
                  #:tag-in3 'qK0or
                  #:tag-out 'oK0)
         (save (move-to-tag 'oK0)
               (label "K0" 'right))
         space
         (or-gate #:tag-in1 'pK1or
                  #:tag-in3 'qK1or
                  #:tag-out 'oK1)
         (save (move-to-tag 'oK1)
               (label "K1" 'right))
         space
         (or-gate #:tag-in1 'pK2or
                  #:tag-in3'qK2or
                  #:tag-out 'oK2)
         (save (move-to-tag 'oK2)
               (label "K2" 'right)))))
    (define S
      (after
       (move-to-tag 'E_i)
       (move-down 1)
       (label "S" 'left)
       (line-to-tag 'S1)
       (split
        (img (blank))
        (line-to-tag 'S2))))
    (after
     inners
     then-and
     else-and
     go-wires
     (wires 'pRES 'qRES 1 "RES")
     (wires 'pSUSP 'qSUSP 2 "SUSP")
     (wires 'pKILL 'qKILL 3 "KILL")
     E_i
     E_o
     outputs
     (for/after ([x (in-list '(pSELor pK0or pK1or pK2or))]
                 [y (in-list '(pSEL pK0 pK1 pK2))]
                 [i (in-naturals)])
       (after
        (move-to-tag x)
        (line-left i)
        (line-to-tag y #:h-first (eq? y 'pSEL))))
     (for/after ([x (in-list '(qSEL qK0 qK1 qK2))]
                 [y (in-list '(qSELor qK0or qK1or qK2or))]
                 [i (in-naturals 1)])
       (after
        (move-to-tag x)
        (line-right i)
        (line-to-tag y #:h-first #f)))
     S)))

(define suspend-pict
  (let ()
    (define p
      (esterel-interface (es (compile p)) #:tag-prefix 'p))
    (after
     fab-four
     (move-to-tag 'RES)
     (line-right 3)
     (move-up 1)
     (and-gate #:tag-in1 'reSEL
               #:tag-out 'dores
               #:tag-in2 'fromres)
     (move-to-tag 'dores)
     (split
      (after (line-right 3)
             (move-down 1)
             (and-gate
              #:tag-in1 '_
              #:tag-in3 'Sres #:in3 #t
              #:tag-out 'resing))
      (after
       (line-down 8)
       (line-right 3)
       (and-gate #:tag-in1 'Ssusp
                 #:tag-in3 '_
                 #:tag-out 'doK1))))))

suspend-pict


(define-simple-macro (clause term pict)
  (clausef (es/unchecked term) pict))

(define (clausef term pict)
  (vl-append
   (hbl-append term (es =))
   (hc-append (blank 10)
              pict)))
(define compile-def
  (list
   
   (clause (compile nothing) nothing)
   (clause (compile (exit n)) (only-kode 'n))
   (clause (compile (emit S)) emit)
   (clause (compile pause) pause)
   (clause (compile (signal S p)) signal-pict)
   (clause (compile (present S p q)) present-pict)
   (clause (compile (suspend p s)) suspend-pict)))