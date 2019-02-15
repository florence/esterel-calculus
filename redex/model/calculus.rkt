#lang debug racket
(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/lset
         esterel-calculus/redex/model/potential-function
         racket/random
         syntax/parse/define)
(provide (all-defined-out))
(module+ test (require rackunit
                       rackunit/text-ui
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
  control-closed-C : (in-hole C (ρ θ E)) V -> boolean
  [(control-closed-C (in-hole C (ρ θ E)) S)
   (control-closed (ρ θ (in-hole E (emit S))))]
  [(control-closed-C (in-hole C (ρ θ E)) s)
   (control-closed (ρ θ (in-hole E (<= s (+ 0)))))])

(define-metafunction esterel-eval
  control-closed : p -> boolean
  [(control-closed p)
   #t
   (where () (FV p))
   (side-condition
    (subset? 
     (list->set
      (flatten
       (term (Can_K p ·))))
     (set 'nothin 'paus)))]
            
  [(control-closed _) #f])

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
  [(E-C (in-hole E_1 (ρ θ E_2)) _)
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

;; TODO Idea for new relation:
;; run can on the ρ, see if that changes in coming deps from C.

;; these relations are known to work.
(define R-empty (MR empty-C))
(define R-no-control (MR no-control-C))
(define R-E (MR E-C))
(define R-control-closed (MR control-closed-C))

;; these are what seem like reasonable attempts at
;; a valid relation which don't work
(define R-closed (MR closed-C))
(define R-no-present (MR no-present-C))
(define R-no-seq (MR no-seq-C))
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
      [(_ R:id)
       #`(run-constructive-tests-for R (symbol->string 'R))]))
  (define (complete? p)
    (redex-match? esterel-eval complete p))
  (define incomplete? (negate complete?))
  (define (run-tests-as R name)
    (test-suite (format "basic tests for ~a" name)
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
       (term (ρ {(sig Si unknown) {(sig So absent) ·}} (present Si (emit So) nothing))))
     
      (test-->>P
       R
       (term
        (signal S2
          (seq (present S2 nothing nothing)
               (trap
                (seq (signal S1
                       (seq
                        (emit S1)
                        (present S1 nothing (exit 0))))
                     (emit S2))))))
                     
       incomplete?)
      (test-case "In which we demonstrate seq is kind of a read of K_0"
        ;; this test case demonstraits that, in a sense, seq acts as
        ;; a `read` of K_0, which means that is absence gives us information
        ;; without execution. However the only way to "Write" to K_0 is through
        ;; signal propigation, meaning emissions are still the only way to
        ;; expose information to Can.

        ;; But this helps explain why Present and Seq are the only thing that can
        ;; add control dependencies: they really are just data dependencies in the end
        ;; (on propigating K_0).

        ;; (Well its not that seq reads from p's K_0, that would be a cycle.
        ;; Seq causes `q` to read `p`s K_0.

        ;; Interestingly... does this mean that K_0 is the only K which can be
        ;; 'read' in this sense?

        ;; So yeah, Ferrante was right, control and data dependencies are unified.
        (test-->>P
         R
         (term
          (signal S2
            (seq (present S2 nothing nothing)
                 (trap
                  (seq (signal S1
                         (seq
                          (emit S1)
                          (present S1 (exit 0) (exit 0))))
                       (emit S2))))))
                     
         complete?))))

  (define (run-constructive-tests-for -> name)
    
    (define (correct-terminus? p)
      (if (fail-on?)  incomplete? complete?))
    (define fail-on? (make-parameter #f))
    (define-syntax fail-on
      (syntax-parser
        [(fail-on (Rs:id ...) body ...)
         #`(parameterize ([fail-on? (memq -> (list Rs ...))])
             body ...)]))
    (test-suite (format "Does ~a bypass constructiveness?" name)
      (test--?>
       ->
       (term (ρ (mtθ+S S1 unknown)
                (present S1
                         (ρ (mtθ+S S2 unknown)
                            (seq (emit S2)
                                 (present S2
                                          nothing
                                          (emit S1))))
                         nothing)))
       (eq? -> R))
      (fail-on
       (R)
       (test-->>P
        ->
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
        ->
        (term
         (signal S1
           (present S1
                    (signal S2
                      ;; This demonstraits that `seq` isn't necessary
                      ;; to trigger the constructivity issue.
                      (par (emit S2)
                           (present S2
                                    nothing
                                    (emit S1))))
                    nothing)))
        correct-terminus?)
       (test-case "in which we demonstrate that ignoring seq dependencies is unsound"
         (fail-on
          (R-no-seq R-no-present)
          (test-->>P
           ->
           ;; Like the previous test case, but the dependency
           ;; gets carried forward by a `seq`.
           (term
            (signal S1
              (seq (present S1 pause nothing)
                   (signal S2
                     (seq (emit S2)
                          (present S2 nothing (emit S1)))))))
           correct-terminus?)
          (test-->>P
           ->
           (term
            (signal S1
              ;; the `nothing nothing` here is meant to demonstrait that
              ;; `Must` might prune a dependency edge from a seq it should not if one is not careful.
              (seq (present S1 nothing nothing)
                   (signal S2
                     (seq (emit S2)
                          (present S2 nothing (emit S1)))))))
           correct-terminus?)))

      
       ;;Does there exist some test case here where a data dependency isn't
       ;;carried over a seq, but the seq is still important for a cycle?

       ;;also here is a crazy though: does there exist a context C
       ;;where I can put a program P which has a *resolvable*
       ;; cycle into the hole, where resolving the cycle is sound.
       ;; Possible Ps:
       (test-case "In which we demonstrate that closed is unsound"
         (fail-on
          (R-closed)
          #;(signal S1
              (signal S2
                (par
                 (par (present S1 nothing (emit S2))
                      (present S2 nothing (emit S1)))
                 (emit S1))))
          ;; or, without par
          #;(signal S1
              (signal S2
                (seq
                 (emit S1)
                 (seq
                  (present S1 nothing (emit S2))
                  (present S2 nothing (emit S1))))))
          ;; simpler
          #;(signal S1
              (seq
               (emit S1)
               (present S1 nothing (emit S1))))
          ;; with the emit outside of the branch
          #;(signal S1
              (seq
               (emit S1)
               (seq
                (present S1 nothing nothing)
                (emit S1))))
      
          ;; hell maybe even something cycleless will do, like:
          #;(signal S1 (emit S1))

          ;; I'm starting to think this isn't possible without `trap`
          ;; but I don't understand the graph structure of that. But maybe
          #;(signal S1
              (seq
               (emit S1)
               (present S1 nothing (exit 0))))
          ;; since can can't determine the exit condition without
          ;; running the emit. Lets try.
             
      
          (test-->>P
           ->
           (term
            (signal S2
              (seq (present S2 nothing nothing)
                   (trap
                    (seq (signal S1
                           (seq
                            (emit S1)
                            (present S1 (exit 0) nothing)))
                         (emit S2))))))
                     
           correct-terminus?)))
       )))
  (void (run-tests (test-relation R)))
  (void (run-tests (test-relation R-empty)))
  (void (run-tests (test-relation R-closed)))
  (void (run-tests (test-relation R-no-control)))
  (void (run-tests (test-relation R-no-seq)))
  (void (run-tests (test-relation R-no-present)))
  (void (run-tests (test-relation R-E)))
  (void (run-tests (test-relation R-control-closed)))

  (void (run-tests (test-constructive R)))
  (void (run-tests (test-constructive R-empty)))
  (void (run-tests (test-constructive R-closed)))
  (void (run-tests (test-constructive R-no-control)))
  (void (run-tests (test-constructive R-no-seq)))
  (void (run-tests (test-constructive R-no-present)))
  (void (run-tests (test-constructive R-E)))
  (void (run-tests (test-constructive R-control-closed))))
