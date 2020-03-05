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

  (define with-S-arrow
    (add-arc an-aterm
             '(1 1 2)
             ct-find
             '(1 2 2)
             rc-find
             #f
             #:start-pull 1.5
             #:end-pull 2
             #:start-angle (* pi 1/2)
             #:end-angle pi
             ))

  (slide (aterm->pict an-aterm))
  (slide (aterm->pict with-S-arrow))
  (slide (aterm->pict (add-left-finger with-S-arrow '())))
  (slide (aterm->pict (add-left-finger with-S-arrow '(2))))
  (slide (aterm->pict (add-right-finger with-S-arrow '(1 2))))
  (slide (aterm->pict (add-left-finger with-S-arrow '(2 2))))
  (slide (aterm->pict (add-left-finger with-S-arrow '(2 2 2)))))

(define (example2)
  (define an-aterm
    (aterm (signal S
             (par (emit S)
                  (present S
                           (emit SO1)
                           (emit SO2))))))

  (define with-S-arrow
    (add-arc an-aterm
             '(1 1 2)
             ct-find
             '(1 2 2)
             rc-find
             #f
             #:start-pull 1.5
             #:end-pull 2
             #:start-angle (* pi 1/2)
             #:end-angle pi
             ))

  (slide (aterm->pict an-aterm))
  (slide (aterm->pict with-S-arrow))
  (slide (aterm->pict (add-left-finger with-S-arrow '())))
  (slide (aterm->pict (add-left-finger with-S-arrow '(2))))
  (slide (aterm->pict (add-right-finger (add-left-finger with-S-arrow '(2 2)) '(1 2))))
  (slide (aterm->pict (add-left-finger with-S-arrow '(2 2))))
  (slide (aterm->pict (add-left-finger with-S-arrow '(2 2 2)))))


(example1)
(example2)
