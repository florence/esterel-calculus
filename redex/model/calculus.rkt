#lang racket
(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/lset
         esterel-calculus/redex/model/potential-function
         racket/random
         syntax/parse/define)
(provide (all-defined-out))
(module+ test (require rackunit
                       esterel-calculus/redex/rackunit-adaptor))

(define R-base
  (reduction-relation
   esterel-eval #:domain p
   (--> (par p q) (par q p) par-swap)
   (--> (par nothing done) done par-nothing)
   (--> (par (exit n) paused) (exit n) par-1exit)
   (--> (par (exit n_1) (exit n_2)) (exit (max-mf n_1 n_2)) par-2exit)

   (--> (ρ θ (in-hole E (present S p q)))
        (ρ θ (in-hole E p))
        (judgment-holds (θ-ref-S θ S present))
        is-present)

   (--> (ρ θ (in-hole E (present S p q)))
        (ρ θ (in-hole E q))
        (judgment-holds (θ-ref-S θ S absent))
        is-absent)

   (--> (loop p)
        (loop^stop p p)
        loop)

   (--> (seq nothing q) q
        seq-done)

   (--> (seq (exit n) q) (exit n)
        seq-exit)
   
   (--> (loop^stop (exit n) q) (exit n)
        loop^stop-exit)

   (--> (suspend stopped S) stopped
        suspend)

   (--> (trap stopped) (harp stopped)
        trap)

   ;; lifting signals
   (--> (signal S p)
        (ρ (mtθ+S S unknown) p)
        signal)

   ;; shared state
   (-->
    (ρ θ (in-hole E (shared s := e p)))
    (ρ θ (in-hole E (ρ (mtθ+s s ev old) p)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    (where ev (δ e θ))
    shared)
   (-->
    (ρ θ (in-hole E (var x := e p)))
    (ρ θ (in-hole E (ρ (mtθ+x x (δ e θ)) p)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    var)
   (-->
    (ρ θ (in-hole E (:= x e)))
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+x x (δ e θ)))) (in-hole E nothing))
    (judgment-holds (L∈ x (Ldom θ)))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    set-var)
   
   ;; if
   (--> (ρ θ (in-hole E (if x p q)))
        (ρ θ (in-hole E q))
        (judgment-holds (θ-ref-x θ x 0))
        if-false)
   (--> (ρ θ (in-hole E (if x p q)))
        (ρ θ (in-hole E p))
        (judgment-holds (L∈ x (Ldom θ)))
        (judgment-holds (¬θ-ref-x θ x 0))
        if-true)

   ;; progression
   (-->
    (ρ θ p)
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S absent))) p)
    (judgment-holds (L∈-OI S (Ldom θ)))
    (judgment-holds (L¬∈ S (->S (Can-θ (ρ θ p) ·))))
    (judgment-holds (θ-ref-S θ S unknown))
    absence)
   (-->
    (ρ θ p)
    (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s ev ready))) p)
    (judgment-holds (L∈-OI s (Ldom θ)))
    (judgment-holds (L¬∈ s (->sh (Can-θ (ρ θ p) ·))))
    (judgment-holds (θ-ref-s θ s ev shared-status))
    (judgment-holds (L∈ shared-status (L2set old new)))
    readyness)

   (-->
    (ρ θ_1 (in-hole E (ρ θ_2 p)))
    (ρ (id-but-typeset-some-parens (<- θ_1 θ_2)) (in-hole E p))
    merge)))

(define-simple-macro (R-write P)
  (reduction-relation
   esterel-eval #:domain p
   
   (--> (in-hole C (ρ θ (in-hole E (emit S))))
        (in-hole C (ρ (id-but-typeset-some-parens (<- θ (mtθ+S S present))) (in-hole E nothing)))
        (judgment-holds (θ-ref-S-∈ θ S (L2set present unknown)))
        (side-condition (term (P (in-hole C (ρ θ E)) S)))
        emit)
   (-->
    (in-hole C (ρ θ (in-hole E (<= s e))))
    (in-hole C (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (δ e θ) new))) (in-hole E nothing)))
    (judgment-holds (θ-ref-s θ s _ old))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    (side-condition (term (P (in-hole C (ρ θ E)) s)))
    set-old)

   (-->
    (in-hole C (ρ θ (in-hole E (<= s e))))
    (in-hole C (ρ (id-but-typeset-some-parens (<- θ (mtθ+s s (Σ ev (δ e θ)) new))) (in-hole E nothing)))
    (judgment-holds (θ-ref-s θ s ev new))
    (judgment-holds (L⊂ (LFV/e e) (Ldom θ)))
    (side-condition (term (all-ready? (LFV/e e) θ)))
    (side-condition (term (P (in-hole C (ρ θ E)) S)))
    set-new)))


;                                                                                                      
;                                                                                                      
;                                                                            ;;                        
;    ;;;;;                                                                   ;;                        
;    ;   ;;                                                       ;;                                   
;    ;    ;;                                                      ;;                                   
;    ;    ;;   ;;  ;;     ;;;;     ; ;;;      ;;;;     ;;  ;;   ;;;;;;     ;;;;       ;;;;      ;;;;   
;    ;    ;;    ; ; ;    ;;  ;;    ;;  ;;    ;;  ;;     ; ; ;     ;;          ;      ;;  ;;    ;    ;  
;    ;    ;;    ;;  ;   ;;    ;    ;    ;    ;    ;     ;;  ;     ;;          ;      ;    ;    ;       
;    ;   ;;     ;;      ;;    ;    ;    ;   ;;    ;     ;;        ;;          ;     ;;    ;    ;;      
;    ;;;;;      ;       ;;    ;    ;    ;   ;;;;;;;     ;         ;;          ;     ;;;;;;;     ;;;;   
;    ;          ;       ;;    ;    ;    ;   ;;          ;         ;;          ;     ;;             ;;  
;    ;          ;       ;;    ;    ;    ;    ;          ;         ;;          ;      ;              ;  
;    ;          ;        ;;  ;;    ;;  ;;    ;;   ;     ;         ;;  ;       ;      ;;   ;   ;;   ;;  
;    ;         ;;;;       ;;;;     ;;;;;      ;;;;     ;;;;        ;;;;    ;;;;;;     ;;;;     ;;;;;   
;                                  ;                                                                   
;                                  ;                                                                   
;                                  ;                                                                   
;                                                                                                      
;                                                                                                      


(define-metafunction esterel-eval
  empty-C : (in-hole C (ρ θ E)) V -> boolean
  [(empty-C (ρ θ E) _) #t]
  [(empty-C _ _) #f])

(define-metafunction esterel-eval
  closed-C : (in-hole C (ρ θ E)) V -> boolean
  [(closed-C (in-hole C (ρ θ E)) S)
   #t
   (where () (FV (ρ θ (in-hole E (emit S)))))]
  [(closed-C (in-hole C (ρ θ E)) s)
   #t
   (where () (FV (ρ θ (in-hole E (<= s (+ 0))))))]
  [(closed-C _ _) #f])

(define-metafunction esterel-eval
  no-control-C : (in-hole C (ρ θ E)) V -> boolean
  [(no-control-C (in-hole C (ρ θ E)) _)
   (no-control C)])

(define-metafunction esterel-eval
  no-present-C : (in-hole C (ρ θ E)) V -> boolean
  [(no-present-C (in-hole C (ρ θ E)) _)
   (no-present C)])

(define-metafunction esterel-eval
  no-seq-C : (in-hole C (ρ θ E)) V -> boolean
  [(no-seq-C (in-hole C (ρ θ E)) _)
   (no-seq C)])

(define-metafunction esterel-eval
  ;; is C a context which cannot incur a control depencency
  ;; that might gain a data dependency
  no-control : C -> boolean
  [(no-control E) #t]
  [(no-control (signal S C)) (no-control C)]
  [(no-control (loop C)) (no-control C)]
  [(no-control (shared s := e C)) (no-control C)]
  [(no-control (var x := e C)) (no-control C)]
  [(no-control (if x C q)) (no-control C)]
  [(no-control (if x p C)) (no-control C)]
  [(no-control (ρ θ C)) (no-control C)]
  [(no-control _) #f])

(define-metafunction esterel-eval
  ;; like no-control but allows control dependencies of seq
  no-present : C -> boolean
  [(no-present E) #t]
  [(no-present (seq p C)) (no-present C)]
  [(no-present (signal S C)) (no-present C)]
  [(no-present (loop C)) (no-present C)]
  [(no-present (shared s := e C)) (no-present C)]
  [(no-present (var x := e C)) (no-present C)]
  [(no-present (if x C q)) (no-present C)]
  [(no-present (if x p C)) (no-present C)]
  [(no-present (ρ θ C)) (no-present C)]
  [(no-present _) #f])

(define-metafunction esterel-eval
  ;; like no-control but allows control dependencies of present
  no-seq : C -> boolean
  [(no-seq E) #t]
  [(no-seq (seq p C)) (no-seq C)]
  [(no-seq (signal S C)) (no-seq C)]
  [(no-seq (loop C)) (no-seq C)]
  [(no-seq (shared s := e C)) (no-seq C)]
  [(no-seq (var x := e C)) (no-seq C)]
  [(no-seq (if x C q)) (no-seq C)]
  [(no-seq (if x p C)) (no-seq C)]
  [(no-seq (ρ θ C)) (no-seq C)]
  [(no-seq _) #f])

(define-metafunction esterel-eval
  E-C : (in-hole C (ρ θ E)) V -> boolean
  [(E-C (in-hole E (ρ θ E)) _)
   #t]
  [(E-C _ _)
   #f])

;                                                                                                      
;                                                                                                      
;                                                                  ;;                                  
;    ;;;;;                    ;                                    ;;                                  
;    ;   ;;                   ;                         ;;                                             
;    ;    ;                   ;                         ;;                                             
;    ;    ;;    ;;;;      ;;; ;    ;    ;      ;;;    ;;;;;;     ;;;;       ;;;;     ; ;;;      ;;;;   
;    ;    ;    ;;  ;;    ;;  ;;    ;    ;    ;;   ;     ;;          ;      ;;  ;;    ;;  ;;    ;    ;  
;    ;   ;;    ;    ;   ;;    ;    ;    ;    ;          ;;          ;     ;;    ;    ;    ;    ;       
;    ;;;;;    ;;    ;   ;;    ;    ;    ;    ;          ;;          ;     ;;    ;    ;    ;    ;;      
;    ;  ;     ;;;;;;;   ;;    ;    ;    ;   ;;          ;;          ;     ;;    ;    ;    ;     ;;;;   
;    ;  ;;    ;;        ;;    ;    ;    ;    ;          ;;          ;     ;;    ;    ;    ;        ;;  
;    ;   ;;    ;        ;;    ;    ;    ;    ;          ;;          ;     ;;    ;    ;    ;         ;  
;    ;    ;    ;;   ;    ;;  ;;    ;   ;;    ;;   ;     ;;  ;       ;      ;;  ;;    ;    ;   ;;   ;;  
;    ;    ;;    ;;;;      ;;; ;    ;;;; ;     ;;;;       ;;;;    ;;;;;;     ;;;;     ;    ;    ;;;;;   
;                                                                                                      
;                                                                                                      
;                                                                                                      
;                                                                                                      
;                                                                                                      

(define R* (union-reduction-relations R-base (R-write empty-C)))

(define R (compatible-closure R* esterel-eval p))

(define-simple-macro (MR P)
  (union-reduction-relations
   (compatible-closure R-base esterel-eval p)
   (R-write P)))

(define R-empty (MR empty-C))
(define R-closed (MR closed-C))
(define R-no-control (MR no-control-C))
(define R-no-present (MR no-present-C))
(define R-no-seq (MR no-seq-C))
(define R-E (MR E-C))

;                                                    
;                                                    
;                                                    
;   ;;;;;;;;                                         
;      ;                            ;;               
;      ;                            ;;               
;      ;        ;;;;      ;;;;    ;;;;;;      ;;;;   
;      ;       ;;  ;;    ;    ;     ;;       ;    ;  
;      ;       ;    ;    ;          ;;       ;       
;      ;      ;;    ;    ;;         ;;       ;;      
;      ;      ;;;;;;;     ;;;;      ;;        ;;;;   
;      ;      ;;             ;;     ;;           ;;  
;      ;       ;              ;     ;;            ;  
;      ;       ;;   ;   ;;   ;;     ;;  ;   ;;   ;;  
;      ;        ;;;;     ;;;;;       ;;;;    ;;;;;   
;                                                    
;                                                    
;                                                    
;                                                    
;                                                    


(module+ test
  (define-syntax test-relation
    (syntax-parser
      [(_ R:id)
       #`(run-tests-as R (symbol->string 'R))]))
  (define-syntax test-constructive
    (syntax-parser
      [(_ R:id bypasses?:expr)
       #`(run-constructive-tests-for R (symbol->string 'R) (not bypasses?))]))
    
  (define (run-tests-as R name)
    (test-case (format "basic tests for ~a" name)
      (test-->
       R
       (term
        (ρ
         ((sig S1 unknown) ·)
         (loop^stop
          (present S1 pause pause)
          (present S1 pause pause))))
       (term
        (ρ
         ((sig S1 absent) ·)
         (loop^stop
          (present S1 pause pause)
          (present S1 pause pause)))))
      (test-->
       R*
       (term (ρ {(sig S present) ·} pause)))
      (test-->
       R*
       (term (signal S pause))
       (term (ρ {(sig S unknown) ·} pause)))
      (test-->
       R
       (term (ρ · (signal S pause)))
       (term (ρ · (ρ {(sig S unknown) ·} pause))))
      (test-->
       R*
       (term (ρ ((sig S unknown) ·) pause))
       (term (ρ ((sig S absent) ·) pause)))
      (test-->
       R
       (term (ρ ((sig S unknown) ·) pause))
       (term (ρ ((sig S absent) ·) pause)))
      (test-->>∃
       R
       (term (ρ {(sig So unknown) ·} (ρ {(sig Si unknown) ·} (present Si (emit So) nothing))))
       (term (ρ {(sig So absent) ·} (ρ {(sig Si unknown) ·} (present Si (emit So) nothing)))))
      (test-->
       R
       (term (loop^stop pause (loop pause)))
       (term (loop^stop pause (loop^stop pause pause))))
      (test-->>∃
       R
       (term (loop pause))
       (term (loop^stop pause pause)))
      (test-->>∃
       R
       (term (seq pause (loop pause)))
       (term (seq pause (loop^stop pause pause))))
      (test-->>∃
       R
       (term (seq nothing (loop pause)))
       (term (loop^stop pause pause)))
      (test-->>∃
       R
       (term (loop^stop (exit 0) (loop (exit 0))))
       (term (exit 0)))
      (test-->>∃
       R
       (term (loop^stop nothing (loop pause)))
       (term (loop^stop nothing (loop^stop pause pause))))
      (test-->>∃
       R
       (term (ρ {(sig Si unknown) {(sig So unknown) ·}} (present Si (emit So) nothing)))
       (term (ρ {(sig Si unknown) {(sig So absent) ·}} (present Si (emit So) nothing))))))

  (define (run-constructive-tests-for R name bypass?)
    (test-case (format "Does ~a bypass constructiveness?" name)
      (define (complete? p)
        (redex-match? esterel-eval complete p))
      (define not-complete? (negate complete?))
      (define correct-terminus? (if bypass? complete? not-complete?))
      (test--?>
       R
       (term (ρ (mtθ+S S1 unknown)
                (present S1
                         (ρ (mtθ+S S2 unknown)
                            (seq (emit S2)
                                 (present S2
                                          nothing
                                          (emit S1))))
                         nothing)))
       bypass?)
      (test-->>P
       R
       (term
        (signal S1
          (present S1
                   (signal S2
                     (seq (emit S2)
                          (present S2
                                   nothing
                                   (emit S1))))
                   nothing)))
       correct-terminus?)
      (test-->>P
       R
       (term
        (signal S1
          (seq (present S1 pause nothing)
               (signal S2
                 (seq (emit S2)
                      (present S2 nothing (emit S1)))))))
       correct-terminus?)
      (test-->>P
       R
       (term
        (signal S1
          ;; the `nothing nothing` here is meant to demonstrait that
          ;; `Must` might prune a dependency edge from a seq it should not if one is not careful.
          (seq (present S1 nothing nothing)
               (signal S2
                 (seq (emit S2)
                      (present S2 nothing (emit S1)))))))
       correct-terminus?)))

  (test-relation R)
  (test-relation R-empty)
  (test-relation R-closed)
  (test-relation R-no-control)
  (test-relation R-no-seq)
  (test-relation R-no-present)
  (test-relation R-E)

  (test-constructive R #f)
  (test-constructive R-empty #t)
  (test-constructive R-closed #t)
  (test-constructive R-no-control #t)
  ;; The failure of these two demonstrates that
  ;; both seq and present control dependency checking
  ;; is required to maintain constructiveness.
  (expect-failures (test-constructive R-no-seq #t))
  (expect-failures (test-constructive R-no-present #t))
  (test-constructive R-E #t))
