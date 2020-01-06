#lang racket
(provide count)
(require redex/reduction-semantics esterel-calculus/redex/model/shared)


(define-metafunction esterel-eval
  count : p-pure -> n
  [(count nothing) 0]
  [(count pause) 0]
  ;; zero, as its step is accounted for by `trap`
  [(count (exit n)) 0]
  [(count (emit S)) 1]
  ;; one step for ->ρ, one for merging
  [(count (signal S p)) (Σ 2 (count p))]
  [(count (present S p q)) (Σ 1 (count p) (count q))]
  [(count (par p q)) (Σ 1 (count p) (count q))]
  [(count (seq p q)) (Σ 1 (count p) (count q))]
  [(count (trap p)) (Σ 1 (count p))]
  [(count (suspend p S)) (Σ 1 (count p))]
  ;; presence accounted for by the emit
  ;; only step is merge
  [(count (ρ θr A p)) (Σ 1 (count p))]
  [(count (loop p)) (Σ 2 (count p) (count p))]
  [(count (loop^stop p q)) (Σ 1 (count p) (count q))])

(module+ test
  (require rackunit
           esterel-calculus/redex/model/calculus
           esterel-calculus/redex/test/generator)
  (define (smaller? p q)
    (> (term (count ,p)) (term (count ,q))))
  (define-check (check-smaller p)  
    (for/and ([q (in-list (apply-reduction-relation/tag-with-names ⟶ p))]
              #:unless (equal? (first q) "par-swap"))
      (smaller? p (second q))))
  (check-smaller (term nothing))
  (check-smaller (term (seq nothing nothing)))
  (check-smaller (term (signal S (emit S))))
  (check-smaller (term (ρ (mtθ+S S unknown) GO (emit S))))
  (check-smaller (term (par (ρ (mtθ+S S unknown) GO (emit S)) nothing)))
  (check-smaller (term (par nothing pause)))
  (check-smaller (term (par pause nothing)))
  (check-smaller (term (par (exit 3) pause)))
  (check-smaller (term (par pause (exit 3))))
  (check-smaller (term (par nothing (exit 3))))
  (check-smaller (term (par (exit 3) nothing)))
  (check-smaller (term (trap (exit 3))))
  (check-smaller (term (trap nothing)))
  
  
  (redex-check
   esterel-eval p-pure
   (check-smaller (term p-pure)))
  (redex-check
   esterel-eval (p-pure (S_1 ...) (S_2 ...) ((S_3 ...) ...))
   (for/and ([q (in-list (apply-reduction-relation/tag-with-names ⟶ (term p-pure)))]
             #:unless (equal? (first q) "par-swap"))
     (check-smaller (term p-pure)))
   #:prepare fixup/allow-empty-signals))
   
  