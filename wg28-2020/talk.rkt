#lang racket
(require "lib.rkt"
         slideshow)

(define (example1)
  (define an-aterm
    (aterm (signal S
             (seq (emit S)
                  (present S
                           (emit SO1)
                           (emit SO2))))))

  (define (add-S-arrow label)
    (add-arc an-aterm
             '(2 1 1)
             ct-find
             '(2 2 1)
             rc-find
             (cons 80 -90)
             label
             #:start-pull 1.5
             #:end-pull 2
             #:start-angle (* pi 1/2)
             #:end-angle pi
             ))

  (define with-S-⊥ (add-S-arrow '⊥))
  (define with-S-1 (add-S-arrow 1))
  
  (slide (aterm->pict an-aterm))
  (slide (aterm->pict with-S-⊥))
  (slide (aterm->pict (add-left-finger with-S-⊥ '())))
  (slide (aterm->pict (add-left-finger with-S-⊥ '(2))))
  (slide (aterm->pict (add-right-finger with-S-⊥ '(2 1))))
  (slide (aterm->pict (add-left-finger with-S-1 '(2 2))))
  (slide (aterm->pict (add-left-finger with-S-1 '(2 2 2)))))

(define (example2)
  (define an-aterm
    (aterm (signal S
             (par (emit S)
                  (present S
                           (emit SO1)
                           (emit SO2))))))

  (define (add-S-arrow label)
    (add-arc an-aterm
             '(2 1 1)
             ct-find
             '(2 2 1)
             rc-find
             (cons 80 -90)
             label
             #:start-pull 1.5
             #:end-pull 2
             #:start-angle (* pi 1/2)
             #:end-angle pi
             ))

  (define with-S-⊥ (add-S-arrow '⊥))
  (define with-S-1 (add-S-arrow 1))

  (slide (aterm->pict an-aterm))
  (slide (aterm->pict with-S-⊥))
  (slide (aterm->pict (add-left-finger with-S-⊥ '())))
  (slide (aterm->pict (add-left-finger with-S-⊥ '(2))))
  (slide (aterm->pict (add-right-finger (add-left-finger with-S-⊥ '(2 2)) '(2 1))))
  (slide (aterm->pict (add-left-finger with-S-1 '(2 2))))
  (slide (aterm->pict (add-left-finger with-S-1 '(2 2 2)))))


(define constructive-cycle-aterm
  (aterm (signal S1
           (signal S2
             (par
              (present S1
                       nothing
                       (emit S2))
              (present S2
                       nothing
                       (emit S1))
              (emit S2))))))

(define (constructive-cycle-example)

  (define (with-arrows S1-label S2-nested-label S2-label)
    (add-S2-arrow
     S2-label
     (add-S2-nested-arrow
      S2-nested-label
      (add-S1-arrow
       S1-label
       constructive-cycle-aterm))))
  
  (define ⊥⊥⊥ (with-arrows '⊥ '⊥ '⊥))
  (define ⊥⊥1 (with-arrows '⊥ '⊥ 1))
  (define 0⊥1 (with-arrows 0 '⊥ 1))
  (define a011 (with-arrows 0 1 1))
  
  (slide (aterm->pict constructive-cycle-aterm))
  (slide (aterm->pict ⊥⊥⊥))
  (slide (aterm->pict (add-left-finger ⊥⊥⊥ '())))
  (slide (aterm->pict (add-left-finger ⊥⊥⊥ '(2))))
  (slide (aterm->pict (add-left-finger ⊥⊥⊥ '(2 2))))
  (slide (aterm->pict (add-left-finger ⊥⊥⊥ '(2 2 1) '(2 2 2) '(2 2 3))))
  (slide (aterm->pict (add-left-finger ⊥⊥1 '(2 2 1) '(2 2 2))))
  (slide (aterm->pict (add-right-finger (add-left-finger 0⊥1 '(2 2 1)) '(2 2 2 2))))
  (slide (aterm->pict (add-right-finger (add-left-finger 0⊥1 '(2 2 1 3)) '(2 2 2 2))))
  (slide (aterm->pict (add-right-finger a011 '(2 2 2 2)))))

(define nonconstructive-cycle-aterm
  (aterm (signal S1
           (signal S2
             (par
              (present S1
                       nothing
                       (emit S2))
              (present S2
                       nothing
                       (emit S1)))))))

(define (nonconstructive-cycle-example)

  (define ⊥⊥
    (add-S2-nested-arrow
     '⊥
     (add-S1-arrow
      '⊥
      nonconstructive-cycle-aterm)))
  
  (slide (aterm->pict nonconstructive-cycle-aterm))
  (slide (aterm->pict ⊥⊥))
  
  (slide (aterm->pict (add-left-finger ⊥⊥ '())))
  (slide (aterm->pict (add-left-finger ⊥⊥ '(2))))
  (slide (aterm->pict (add-left-finger ⊥⊥ '(2 2))))
  (slide (aterm->pict (add-left-finger ⊥⊥ '(2 2 1) '(2 2 2))))
  )

(define (constructive/nonconstructive-cycle-with-cycle-shown)
  (define non
    (aterm->pict
     (add-present-S1->then-arrow
      (add-present-S1->else-arrow
       (add-present-S2->then-arrow
        (add-present-S2->else-arrow
         (add-S2-nested-arrow
          #f
          (add-S1-arrow
           #f
           nonconstructive-cycle-aterm))))))))
  (define con
    (aterm->pict
     (add-S2-arrow
      #f
      (add-present-S1->then-arrow
       (add-present-S1->else-arrow
        (add-present-S2->then-arrow
         (add-present-S2->else-arrow
          (add-S2-nested-arrow
           #f
           (add-S1-arrow
            #f
            constructive-cycle-aterm)))))))))

  (slide (lt-superimpose (ghost con) non))
  (slide (lt-superimpose con (ghost non))))
  
(define (add-S1-arrow label an-aterm)
  (add-arc an-aterm
           '(2 2 2 3 1)
           rc-find
           '(2 2 1 1)
           rc-find
           (cons 130 -100)
           label
           #:start-pull 1
           #:end-pull 1.2
           #:start-angle 0
           #:end-angle pi
           ))

(define (add-S2-nested-arrow label an-aterm)
  (add-arc an-aterm
           '(2 2 1 3 1)
           rc-find
           '(2 2 2 1)
           rc-find
           (cons 120 -20)
           label
           #:start-pull 1
           #:end-pull 1
           #:start-angle 0
           #:end-angle pi
           ))

(define (add-S2-arrow label an-aterm)
  (add-arc an-aterm
           (find-path an-aterm 'S2 3)
           rc-find
           (find-path an-aterm 'S2 2)
           rc-find
           (cons 100 45)
           label
           #:start-pull 3.2
           #:end-pull 1.3
           #:start-angle 0
           #:end-angle pi
           ))

(define (add-present-S1->else-arrow an-aterm)
  (add-arc an-aterm
           (find-path an-aterm 'S1 1)
           lb-find
           (find-path an-aterm 'nothing 0)
           lc-find
           (cons 130 -100)
           #f
           #:start-pull 1
           #:end-pull 1.2
           #:start-angle (* 1.1 pi)
           #:end-angle 0
           ))

(define (add-present-S1->then-arrow an-aterm)
  (add-arc an-aterm
           (find-path an-aterm 'S1 1)
           lb-find
           (find-path an-aterm '(emit S2) 0)
           lc-find
           (cons 130 -100)
           #f
           #:start-pull 1
           #:end-pull 1.2
           #:start-angle (* 1.1 pi)
           #:end-angle 0
           ))

(define (add-present-S2->else-arrow an-aterm)
  (add-arc an-aterm
           (find-path an-aterm 'S2 2)
           lb-find
           (find-path an-aterm 'nothing 1)
           lc-find
           (cons 130 -100)
           #f
           #:start-pull 1
           #:end-pull 1.2
           #:start-angle (* 1.1 pi)
           #:end-angle 0
           ))

(define (add-present-S2->then-arrow an-aterm)
  (add-arc an-aterm
           (find-path an-aterm 'S2 2)
           lb-find
           (find-path an-aterm '(emit S1) 0)
           lc-find
           (cons 130 -100)
           #f
           #:start-pull 1
           #:end-pull 1.2
           #:start-angle (* 1.1 pi)
           #:end-angle 0
           ))

;(example1)
;(example2)
(constructive-cycle-example)
(nonconstructive-cycle-example)
(constructive/nonconstructive-cycle-with-cycle-shown)