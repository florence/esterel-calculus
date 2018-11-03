#lang racket

(require (only-in esterel-calculus/redex/model/shared
                  esterel-eval θ-ref-S θ-ref-s θ-ref-x
                  add2 <- dom get-unknown-signals
                  mtθ+S mtθ+s mtθ+x
                  Lwithoutdom L∈dom θ-get-S)
         esterel-calculus/redex/model/lset
         redex/reduction-semantics)
(module+ test (require rackunit))

(define-syntax quasiquote (make-rename-transformer #'term))


(provide

 ;; still operate on (S ...) and (s ...)
 Cannot Cannot_shared

 ;; adjusted to operate on L-S, etc.
 Can-θ
 Can Can_K Can_S Can_shared
 ->K ->S ->sh)

(define-metafunction esterel-eval
  Cannot : p θ (S ...) -> (S ...) or ⊥
  [(Cannot p θ (S_o ...))
   {S_1 S_r ...}
   (where (S-code-s L-S L-κ L-s) (Can p θ))
   (where {S_1 S_r ...}
          ,(filter (lambda (s) (not (member s (flatten `L-S)))) `{S_o ...}))]
  [(Cannot p θ {S ...}) ⊥])

(define-metafunction esterel-eval
  LCannot : p θ L-S -> L-S
  [(LCannot p θ L-S) (Lset-sub L-S (->S (Can p θ)))])

(module+ test
  (define (LCannot/Cannot in)
    (define (norm l) (sort l symbol<?))
    (define (to-list l)
      (match l
        [`⊥ '()]
        [(? pair?) l]))
    (equal? (norm (flatten (term (LCannot (seq (emit S1) (emit S2)) · ,in))))
            (norm (to-list (term (Cannot (seq (emit S1) (emit S2)) · ,(flatten in)))))))
  (check-true (LCannot/Cannot (term (L0set))))
  (check-true (LCannot/Cannot (term (L1set S1))))
  (check-true (LCannot/Cannot (term (L1set S2))))
  (check-true (LCannot/Cannot (term (L1set S3))))
  (check-true (LCannot/Cannot (term (L2set S1 S2))))
  (check-true (LCannot/Cannot (term (L2set S1 S3))))
  (check-true (LCannot/Cannot (term (L2set S2 S3)))))

(define-metafunction esterel-eval
  Cannot_shared : p θ (s ...) -> (s ...) or ⊥
  [(Cannot_shared p θ {s_o ...})
   {s_1 s_r ...}
   (where (S-code-s L-S L-κ L-s)
          (Can p θ))
   (where {s_1 s_r ...}
          ,(filter (lambda (x) (not (member x (flatten `L-s)))) `{s_o ...}))]
  [(Cannot_shared p θ {s ...}) ⊥])

(define-metafunction esterel-eval
  ->S : Can-result -> L-S
  [(->S (S-code-s L-S L-κ L-s)) L-S])
(define-metafunction esterel-eval
  ->K : Can-result -> L-κ
  [(->K (S-code-s L-S L-κ L-s)) L-κ])
(define-metafunction esterel-eval
  ->sh : Can-result -> L-s
  [(->sh (S-code-s L-S L-κ L-s)) L-s])

(define-metafunction esterel-eval
  Can-θ : (ρ θ p) θ -> Can-result

  [(Can-θ (ρ θ p) θ_2)
   (Can-θ (ρ (Lwithoutdom θ S) p) (<- θ_2 (mtθ+S S absent)))
   (judgment-holds (L∈dom S θ)) ;; S ∈ dom(θ_1)
   (judgment-holds (θ-ref-S θ S unknown)) ;; θ_1(S) = present
   (judgment-holds (L¬∈ S (->S (Can-θ (ρ (Lwithoutdom θ S) p) (<- θ_2 (mtθ+S S unknown))))))]

  [(Can-θ (ρ θ p) θ_2)
   (Can-θ (ρ (Lwithoutdom θ S) p) (<- θ_2 (mtθ+S S (θ-get-S θ S))))
   (judgment-holds (L∈dom S θ))] ;; S ∈ dom(θ_1)

  [(Can-θ (ρ θ_1 p) θ_2)
   (Can p θ_2)])

(define-metafunction esterel-eval
  Can : p θ -> Can-result
  [(Can (ρ θ_1 p) θ_2)
   (S-code-s (Lset-sub (->S (Can-θ (ρ θ_1 p) θ_2)) (Ldom θ_1))
             (->K (Can-θ (ρ θ_1 p) θ_2))
             (Lset-sub (->sh (Can-θ (ρ θ_1 p) θ_2)) (Ldom θ_1)))]

  [(Can nothing θ) (S-code-s (L0set) (L1set nothin) (L0set))]

  [(Can pause θ) (S-code-s (L0set) (L1set paus) (L0set))]

  [(Can (exit n) θ) (S-code-s (L0set) (L1set n) (L0set))]

  [(Can (emit S) θ) (S-code-s (L1set S) (L1set nothin) (L0set))]

  [(Can (present S p q) θ)
   (Can p θ)
   (judgment-holds (θ-ref-S θ S present))]

  [(Can (present S p q) θ)
   (Can q θ)
   (judgment-holds (θ-ref-S θ S absent))]

  [(Can (present S p q) θ)
   (S-code-s (LU (->S (Can p θ)) (->S (Can q θ)))
             (LU (->K (Can p θ)) (->K (Can q θ)))
             (LU (->sh (Can p θ)) (->sh (Can q θ))))]

  [(Can (suspend p S) θ)
   (Can p θ)]

  [(Can (seq p q) θ)
   (Can p θ)
   (judgment-holds (L¬∈ nothin (->K (Can p θ))))]

  [(Can (seq p q) θ)
   (S-code-s (LU (->S (Can p θ)) (->S (Can q θ)))
             (LU (Lset-sub (->K (Can p θ)) (L1set nothin)) (->K (Can q θ)))
             (LU (->sh (Can p θ)) (->sh (Can q θ))))]

  [(Can (loop p) θ)
   (Can p θ)]

  [(Can (loop^stop p q) θ)
   (Can p θ)]

  [(Can (par p q) θ)
   (S-code-s (LU (->S (Can p θ)) (->S (Can q θ)))
             (Lmax* (->K (Can p θ)) (->K (Can q θ)))
             (LU (->sh (Can p θ)) (->sh (Can q θ))))]

  [(Can (trap p) θ)
   (S-code-s (->S (Can p θ)) (Lharp... (->K (Can p θ))) (->sh (Can p θ)))]

  [(Can (signal S p) θ)
   (S-code-s (Lset-sub (->S (Can p (<- θ (mtθ+S S absent)))) (L1set S))
             (->K (Can p (<- θ (mtθ+S S absent))))
             (->sh (Can p (<- θ (mtθ+S S absent)))))
   (judgment-holds (L¬∈ S (->S (Can p (<- θ (mtθ+S S unknown))))))]

  [(Can (signal S p) θ)
   (S-code-s (Lset-sub (->S (Can p θ_2)) (L1set S)) (->K (Can p θ_2)) (->sh (Can p θ_2)))
   (where θ_2 (<- θ (mtθ+S S unknown)))]

  [(Can (shared s := e p) θ)
   (S-code-s (->S (Can p θ)) (->K (Can p θ)) (Lset-sub (->sh (Can p θ)) (L1set s)))]
  [(Can (<= s e) θ)
   (S-code-s (L0set) (L1set nothin) (L1set s))]

  [(Can (var x := e p) θ)
   (Can p θ)]
  [(Can (:= x e) θ)
   (S-code-s (L0set) (L1set nothin) (L0set))]
  [(Can (if x p q) θ)
   (S-code-s (LU (->S (Can p θ)) (->S (Can q θ)))
             (LU (->K (Can p θ)) (->K (Can q θ)))
             (LU (->sh (Can p θ)) (->sh (Can q θ))))])

(define-metafunction esterel-eval
  Can_S : p θ -> L-S
  [(Can_S p θ) (->S (Can p θ))])

(define-metafunction esterel-eval
  Can_K : p θ -> L-κ
  [(Can_K p θ) (->K (Can p θ))])

(define-metafunction esterel-eval
  Can_shared : p θ -> L-s
  [(Can_shared p θ) (->sh (Can p θ))])

(module+ test
  (check-equal?
   (term (Can_S (par (seq pause (emit SI))
                     (seq (present SI nothing (emit SC))
                          (present SC (emit SC) nothing)))
                ((sig SI unknown)
                 ((sig SC unknown)
                  ·))))
   (term (L2set SC SC)))
  (check-equal?
   `(Can_K (par (present SS (exit 0) nothing)
                nothing)
           {(sig SS unknown) ·})
   (term (L2set 0 nothin)))
  (check-equal?
   `(Can (seq
          (ρ {(sig S_I unknown) ((sig S_C unknown) ·)}
             (par (seq nothing (emit S_I))
                  (seq
                   (seq
                    (present S_I nothing (emit S_C))
                    (present S_C (emit S_C) nothing))
                   pause)))
          (loop nothing)) ·)
   `(S-code-s (L0set) (L1set paus) (L0set)))

  (check-equal?
   `(Cannot  (shared s2 := (+ s) pause)
             ((shar s 1 new) ·)
             (get-unknown-signals ((shar s 1 new) ·)))
   `⊥)

  (check-equal?
   `(Can_K (trap (exit 0)) ·)
   (term (L1set nothin)))
  (check-equal?
   `(Can_K (trap (par (exit 0) pause)) ·)
   `(L1set nothin))
  (check-equal?
   `(Can_shared (ρ ((shar s 0 old) ·) (<= s (+ 0))) ·)
   `())

  (check-equal? (term (Can-θ (ρ · (emit S)) ·))
                (term (S-code-s (L1set S) (L1set nothin) (L0set))))

  (check-equal? (term (Can-θ (ρ ({sig S1 unknown} ·) (present S1 nothing (emit S))) ·))
                (term (S-code-s (L1set S) (L1set nothin) (L0set))))

  (check-equal? (term (Can-θ (ρ ({sig S1 unknown} ·) (present S1 (emit S) nothing)) ·))
                (term (S-code-s (L0set) (L1set nothin) (L0set))))

  (check-equal? (term (Can-θ (ρ ({sig S1 unknown} ·) (present S1 (emit S1) (emit S))) ·))
                (term (S-code-s (L2set S1 S) (L2set nothin nothin) (L0set))))
  (check-equal?
   (term (Can (loop^stop nothing (seq (emit S) (seq (<= s (+ 1)) pause))) ·))
   (term (S-code-s (L0set) (L1set nothin) (L0set)))))