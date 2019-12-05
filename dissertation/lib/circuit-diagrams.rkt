#lang racket
(require diagrama diagrama/circuit pict racket/syntax
         "redex-rewrite.rkt")

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
         

(define basic-interface 
  (esterel-interface (blank)))
(define signal-pict
  (after
   (esterel-interface (es (compile p))
                      #:tag-prefix '||
                      #:extra-input-signals '(S_i)  #:extra-output-signals '(S_o))
   (move-to-tag 'S_i)
   (line-to-tag 'S_o)))
(define nothing
  (after
   (img (textify "GO") 'rc)
   (line-right 4)
   (before
    (buffer)
    (line-right 4)
    (img (textify "K0") 'lc))))
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
    (define input-spacing 3)
    (define inputs
      (after (tag-location 'GO)
             (move-down input-spacing) (tag-location 'RES)
             (move-down input-spacing) (tag-location 'SUSP)
             (move-down input-spacing) (tag-location 'KILL)))
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