#lang racket
(require esterel-calculus/paper/redex-rewrite
         esterel-calculus/redex/model/potential-function
         redex/reduction-semantics
         esterel-calculus/redex/model/shared
         (prefix-in calculus: esterel-calculus/redex/model/calculus)
         (prefix-in standard: esterel-calculus/redex/model/reduction)
         redex/pict
         (only-in pict show-pict scale hc-append))

(define (render)
  (define (show p) (show-pict (scale p 1.2)))
  (with-paper-rewriters
   (parameterize ([rule-pict-style 'horizontal])
     (show
      (render-reduction-relation calculus:⇀))
     (show
      (render-reduction-relation standard:R))
     (show
      (hc-append
       (render-language esterel)
       (render-language esterel-eval)
       (render-metafunction Can))))))

(module+ render (render))
