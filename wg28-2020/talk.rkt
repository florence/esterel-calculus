#lang racket
(require "lib.rkt"
         slideshow)

(define an-aterm
  (aterm (signal S
           (par (emit S)
                (present S
                         (emit SO1)
                         (emit SO2))))))

(slide (aterm->pict an-aterm))
(slide (aterm->pict (add-left-finger an-aterm '())))
(slide (aterm->pict (add-left-finger an-aterm '(2))))
(slide (aterm->pict (add-right-finger an-aterm '(1 2))))
