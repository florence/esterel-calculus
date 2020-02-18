#lang racket
(provide count)
(require redex/reduction-semantics esterel-calculus/redex/model/shared)


(define-metafunction esterel-eval
  count : p-pure+GO -> n
  [(count nothing) 0]
  [(count pause) 0]
  ;; zero, as its step is accounted for by `trap`
  [(count (exit n)) 0]
  [(count (emit S)) 1]
  ;; one step for ->ρ, one for merging
  [(count (signal S p-pure+GO)) (Σ 2 (count p-pure+GO))]
  [(count (present S p-pure+GO q-pure+GO)) (Σ 1 (count p-pure+GO) (count q-pure+GO))]
  [(count (par p-pure+GO q-pure+GO)) (Σ 1 (count p-pure+GO) (count q-pure+GO))]
  [(count (seq p-pure+GO q-pure+GO)) (Σ 1 (count p-pure+GO) (count q-pure+GO))]
  [(count (trap p-pure+GO)) (Σ 1 (count p-pure+GO))]
  [(count (suspend p-pure+GO S)) (Σ 1 (count p-pure+GO))]
  ;; presence accounted for by the emit
  ;; only step is merge
  [(count (ρ θr A p-pure+GO)) (Σ 1 (count p-pure+GO))]
  [(count (loop p-pure+GO)) (Σ 2 (count p-pure+GO) (count p-pure+GO))]
  [(count (loop^stop p-pure+GO q-pure+GO)) (Σ 1 (count p-pure+GO) (count q-pure+GO))])

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
   
  