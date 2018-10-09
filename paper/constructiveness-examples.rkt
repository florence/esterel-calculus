#lang racket

(require "calculus-figures.rkt"
         "redex-rewrite.rkt"
         "util.rkt"
         rackunit
         redex/reduction-semantics
         (prefix-in standard: esterel-calculus/redex/model/reduction)
         esterel-calculus/redex/model/eval
         esterel-calculus/redex/model/shared)

(provide init-term/block
         init-term
         std-reduced/block
         std-reduced
         extra-info-visible
         extra-info-visible/block
         the-context
         the-context/block
         final-term
         final-term/block)

(define/esblock init-term init-term/block
  (signal S1
    (present S1
             (signal S2
               (seq (emit S2) 
                    (present S2
                             nothing
                             (emit S1))))
             nothing)))

(define/esblock std-reduced std-reduced/block
  (ρ (mtθ+S S1 unknown)
     (present
      S1
      (signal S2
        (seq (emit S2)
             (present S2 nothing (emit S1))))
      nothing)))

(check-not-false
 (member std-reduced
         (apply-reduction-relation*
          standard:R
          (term (ρ · ,init-term)))))

(define/esblock extra-info-visible extra-info-visible/block
  (ρ (mtθ+S S1 unknown)
     (present
      S1
      (ρ (mtθ+S S2 present)
         (seq nothing
              (present S2
                       nothing
                       (emit S1))))
      nothing)))

(define/esblock the-context the-context/block
  (ρ (mtθ+S S1 unknown)
     (present S1
              hole
              nothing)))

(check-not-false
 (member extra-info-visible
         (judgment-holds
          (≡e ()
              ;; contexts
              (hole
               ,the-context)
              ;; trans
              ((ρ ((sig S1 unknown) ·)
                  (present
                   S1
                   (ρ
                    ((sig S2 unknown) ·)
                    (seq (emit S2) (present S2 nothing (emit S1))))
                   nothing)))
              ,std-reduced
              p)
          p)))

(define/esblock final-term final-term/block
  (ρ (mtθ+S S1 absent) nothing))

(check-not-false
 (member final-term
         (apply-reduction-relation*
          standard:R
          extra-info-visible)))
