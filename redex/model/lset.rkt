#lang racket

(require esterel-calculus/redex/model/shared
         redex/reduction-semantics)
(module+ test (require rackunit))

#|

Various lists-as-sets utility functions

|#

(provide L0set L1set L2set L¬∈ L∈ L∈-OI LU L∩
         L⊂ Lset-sub Lremove distinct
         Lflatten
         Lunflatten
         Lharp... Lmax* Ldom LFV/e
         Lget-unknown-signals
         Lresort
         Lget-unready-shared)

(define-metafunction esterel-eval
  L0set : -> L
  [(L0set) ()])

(define-metafunction esterel-eval
  L1set : any -> L
  [(L1set any_a) (any_a ())])
(module+ test
  (check-equal? (term (L1set 0)) (term (0 ()))))

(define-metafunction esterel-eval
  L2set : any any -> L
  [(L2set any_a any_b) (any_a (any_b ()))])
(module+ test
  (check-equal? (term (L2set 0 1)) (term (0 (1 ())))))

(define-judgment-form esterel-eval
  #:mode (L¬∈ I I)
  #:contract (L¬∈ any L)
  [--------------
   (L¬∈ any_1 ())]

  [(where #t (different any_1 any_2)) (L¬∈ any_1 L)
   ------------------------------------------------
   (L¬∈ any_1 (any_2 L))])
(module+ test
  (check-true  (judgment-holds (L¬∈ 0 ())))
  (check-true  (judgment-holds (L¬∈ 0 (1 ()))))
  (check-false (judgment-holds (L¬∈ 1 (1 ()))))
  (check-false (judgment-holds (L¬∈ 1 (1 (0 ())))))
  (check-false (judgment-holds (L¬∈ 0 (1 (0 ())))))
  (check-true  (judgment-holds (L¬∈ 3 (1 (0 ()))))))

(define-judgment-form esterel-eval
  #:mode (L∈ I I)
  #:contract (L∈ any L)
  [--------------------
   (L∈ any_1 (any_1 L))]

  [(where #t (different any_1 any_2)) (L∈ any_1 L)
   ------------------------------------
   (L∈ any_1 (any_2 L))])
(module+ test
  (check-false (judgment-holds (L∈ 0 ())))
  (check-false (judgment-holds (L∈ 0 (1 ()))))
  (check-true  (judgment-holds (L∈ 1 (1 ()))))
  (check-true  (judgment-holds (L∈ 1 (1 (0 ())))))
  (check-true  (judgment-holds (L∈ 0 (1 (0 ())))))
  (check-false (judgment-holds (L∈ 3 (1 (0 ()))))))

(define-judgment-form esterel-eval
  #:mode (L∈-OI O I)
  #:contract (L∈-OI any L)
  [--------------------
   (L∈-OI any_1 (any_1 L))]

  [(L∈-OI any_1 L)
   ------------------------
   (L∈-OI any_1 (any_2 L))])
(module+ test
  (check-false (judgment-holds (L∈-OI 0 ())))
  (check-false (judgment-holds (L∈-OI 0 (1 ()))))
  (check-true  (judgment-holds (L∈-OI 1 (1 ()))))
  (check-true  (judgment-holds (L∈-OI 1 (1 (0 ())))))
  (check-true  (judgment-holds (L∈-OI 0 (1 (0 ())))))
  (check-false (judgment-holds (L∈-OI 3 (1 (0 ()))))))

(define-judgment-form esterel-eval
  #:mode (L∈-OI/first O I)
  #:contract (L∈-OI/first any L)
  [--------------------
   (L∈-OI/first any_1 (any_1 L))])

(define-metafunction esterel-eval
  L∩ : L L -> L
  [(L∩ {} L) {}]
  [(L∩ {any_1 L_1} L)
   (LU {any_1 {}} (L∩ L_1 L))
   (judgment-holds (L∈ any_1 L))]
  [(L∩ {any_1 L_1} L) (L∩ L_1 L)])
(module+ test
  (check-equal? (term (L∩ () ())) (term ()))
  (check-equal? (term (L∩ (1 ()) (2 ()))) (term ()))
  (check-equal? (term (L∩ (1 ()) (1 ()))) (term (1 ())))
  (check-equal? (term (L∩ (1 (2 (3 (4 (5 (6 (7 (8 ()))))))))
                          (1 (12 (3 (14 (5 (16 (7 (18 ()))))))))))
                (term (1 (3 (5 (7 ())))))))

(define-metafunction esterel-eval
  LU : L L -> L
  [(LU {} L) L]
  [(LU (any L_1) L) (any (LU L_1 L))])

(define-metafunction esterel-eval
  Lset-sub : L L -> L
  [(Lset-sub L {}) L]
  [(Lset-sub L_2 (any_1 L_1)) (Lremove (Lset-sub L_2 L_1) any_1)])
(module+ test
  (check-equal? (term (Lset-sub (L2set 0 1) (L0set))) (term (L2set 0 1)))
  (check-equal? (term (Lset-sub (L2set 0 1) (L1set 0))) (term (L1set 1)))
  (check-equal? (term (Lset-sub (L2set 0 1) (L1set 1))) (term (L1set 0)))
  (check-equal? (term (Lset-sub (L2set 0 1) (L2set 0 1))) (term (L0set)))
  (check-equal? (term (Lset-sub (L2set 0 1) (L2set 3 4))) (term (L2set 0 1))))

(define-metafunction esterel-eval
  Lremove : L any -> L
  [(Lremove {} any) {}]
  [(Lremove (any_1 L) any_1) (Lremove L any_1)]
  [(Lremove (any_1 L) any_2) (any_1 (Lremove L any_2))])
(module+ test
  (check-equal? (term (Lremove (L2set 0 1) 0)) (term (L1set 1)))
  (check-equal? (term (Lremove (L2set 0 1) 0)) (term (L1set 1)))
  (check-equal? (term (Lremove (L2set 0 1) 2)) (term (L2set 0 1)))
  (check-equal? (term (Lremove (L2set 11 11) 11)) (term (L0set))))

(define-judgment-form esterel-eval
  #:mode (L⊂ I I)
  #:contract (L⊂ L L)

  [---------
   (L⊂ () L)]

  [(L∈ any L_2) (L⊂ L_1 L_2)
   -------------------------
   (L⊂ (any L_1) L_2)])
(module+ test
  (check-true (judgment-holds (L⊂ () (x (y (z ()))))))
  (check-true (judgment-holds (L⊂ (y ()) (x (y (z ()))))))
  (check-false (judgment-holds (L⊂ (x (y (z ()))) ())))
  (check-true (judgment-holds (L⊂ (x (y (z ()))) (y (x (q (z ()))))))))

(define-judgment-form esterel-eval
  #:mode (distinct I I)
  #:contract (distinct L L)
  [---------------
   (distinct {} L)]
  [(L¬∈ any L_2)
   (distinct L_1 L_2)
   ----------------------
   (distinct {any L_1} L_2)])
(module+ test
  (check-true (judgment-holds (distinct (L2set 0 1) (L2set 2 3))))
  (check-false (judgment-holds (distinct (L2set 0 1) (L2set 0 3))))
  (check-false (judgment-holds (distinct (L2set 0 1) (L2set 1 3)))))


(define-metafunction esterel-eval
  Lmax* : L-κ L-κ -> L-κ
  [(Lmax* () L-κ) {}]
  [(Lmax* (κ_1 L-κ_r) L-κ)
   (LU ,(Lmap (lambda (x) `(κmax ,x κ_1)) `L-κ)
       (Lmax* L-κ_r L-κ))])
(define-metafunction esterel-eval
  κmax : κ κ -> κ
  [(κmax nothin κ) κ]
  [(κmax paus nothin) paus]
  [(κmax paus κ) κ]
  [(κmax n_1 n_2)
   ,(max `n_1 `n_2)]
  [(κmax n κ) n])

(define (Lmap f L)
  (let loop ([L L])
    (match L
      [(list) (list)]
      [(list x L) (list (f x) (loop L))])))

(define-metafunction esterel-eval
  Lflatten : L -> (any ...)
  [(Lflatten ()) ()]
  [(Lflatten (any L))
   (any any_r ...)
   (where (any_r ...) (Lflatten L))])

(define-metafunction esterel-eval
  Lunflatten : (any ...) -> L
  [(Lunflatten ()) (L0set)]
  [(Lunflatten (any any_r ...))
   (LU (L1set any) (Lunflatten (any_r ...)))])

(module+ test
  (check-equal? (term (Lmax* () ())) (term ()))
  (check-equal? (term (Lmax* (L1set paus) (L2set 0 1)))
                (term (L2set 0 1)))
  (check-equal?  (list->set (term (Lflatten (Lmax* (L2set paus 0) (L2set 0 1)))))
                (set (term 0) (term 1)))
  (check-equal? (list->set (term (Lflatten (Lmax* (L2set 0 1) (L2set paus 0)))))
                (set (term 0) (term 1)))
  (check-equal? (list->set (term (Lflatten (Lmax* (L2set 2 nothin) (L2set 0 1)))))
                (set (term 0) (term 1) (term 2)))
  (check-equal?  (list->set (term (Lflatten (Lmax* (L2set 0 1) (L2set 2 nothin)))))
                (set (term 0) (term 1) (term 2))))

(define-metafunction esterel-eval
  Lharp... : L-κ -> L-κ
  [(Lharp... ()) ()]
  [(Lharp... (κ L)) ((↓ κ) (Lharp... L))])

(define-metafunction esterel-eval
  Ldom : θ -> L
  [(Ldom ·) {}]
  [(Ldom {(var· x ev) θ}) {x (Ldom θ)}]
  [(Ldom {(shar s ev shared-status) θ}) {s (Ldom θ)}]
  [(Ldom {(sig S status) θ}) {S (Ldom θ)}])

(define-metafunction esterel-eval
  ;; returns a set containing only `x` and `s`s
  LFV/e : e -> L
  [(LFV/e (f)) ()]
  [(LFV/e (f x s/l ...)) (x (LFV/e (f s/l ...)))]
  [(LFV/e (f s s/l ...)) (s (LFV/e (f s/l ...)))]
  [(LFV/e (f any s/l ...)) (LFV/e (f s/l ...))])

(module+ test
  (check-equal? (term (LFV/e (+ x s x1 s2 0 1 41 s3 x3)))
                (term (x (s (x1 (s2 (s3 (x3 ())))))))))


(define-metafunction esterel-eval
  Lresort : θ -> θ
  [(Lresort θ) ,(resort (term θ))])


(define-metafunction esterel-eval
  Lget-unknown-signals : θ -> L
  [(Lget-unknown-signals θ)
   (Lget-signals-of-status θ unknown)])

(define-metafunction esterel-eval
  Lget-signals-of-status : θ status -> L
  [(Lget-signals-of-status ((sig S status) θ) status)
   (S (Lget-signals-of-status θ status))]
  [(Lget-signals-of-status ((sig S status_1) θ) status_2)
   (Lset-sub (Lget-signals-of-status θ status_2) (L1set S))]
  [(Lget-signals-of-status (env-v_h θ) status)
   (Lget-signals-of-status θ status)]
  [(Lget-signals-of-status · status)
   ()])

(module+ test
  (check-equal? (term (Lget-unknown-signals ·))
                (term ()))
  (check-equal? (term (Lget-unknown-signals ((sig S unknown) ·)))
                (term (S ())))
  (check-equal? (term (Lget-unknown-signals ((sig S1 unknown)
                                             ((sig S2 absent)
                                              ((sig S3 unknown) ·)))))
                (term (S1 (S3 ()))))
  (check-equal? (term (Lget-unknown-signals ((sig S present) ((sig S unknown) ·))))
                (term ())))

(define-metafunction esterel-eval
  Lget-unready-shared : θ -> L-s
  [(Lget-unready-shared ·) ()]
  [(Lget-unready-shared ((shar s ev old) θ))
   (s (Lget-unready-shared θ))]
  [(Lget-unready-shared ((shar s ev new) θ))
   (s (Lget-unready-shared θ))]
  [(Lget-unready-shared (env-v θ))
   (Lget-unready-shared θ)])

(module+ test
  (check-equal? (term (Lget-unready-shared ·))
                (term (L0set)))
  (check-equal? (term (Lget-unready-shared ((shar s 1 new) ·)))
                (term (L1set s)))
  (check-equal? (term (Lget-unready-shared ((shar s 2 old) ·)))
                (term (L1set s)))
  (check-equal? (term (Lget-unready-shared ((shar s1 4 old)
                                            ((shar s3 6 new)
                                             ·))))
                (term (L2set s1 s3)))
  (check-equal? (term (Lget-unready-shared ((sig S absent)
                                            ((sig S2 present)
                                             ·))))
                (term (L0set)))
  (check-equal? (term (Lget-unready-shared ((sig S absent)
                                                    ((shar s2 8 new)
                                                     ((sig S1 present)
                                                      ·)))))
                (term (L1set s2))))
