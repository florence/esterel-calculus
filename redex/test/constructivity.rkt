#lang racket
(require
  racket/require
  esterel-calculus/redex/model/calculus
  esterel-calculus/redex/rackunit-adaptor
  esterel-calculus/redex/test/model-test
  esterel-calculus/redex/model/shared
  (subtract-in redex/reduction-semantics
               esterel-calculus/redex/rackunit-adaptor)
  rackunit
  rackunit/text-ui
  (for-syntax syntax/parse))
(define (complete? p)
  (redex-match? esterel-eval complete p))
(define incomplete? (negate complete?))
(require (prefix-in ru: rackunit))

#;
(define-syntax test-case
  (syntax-parser
    [(_ x body ...)
     #'(ru:test-case x (displayln x) body ...)]))
  
;                                                                                                                
;                                                                                                                
;                                    ;;                                                                          
;    ;;;;;                           ;;                         ;;;;;;;;                                         
;    ;   ;;                                                        ;                            ;;               
;    ;    ;                                                        ;                            ;;               
;    ;    ;    ;;;;;      ;;;;     ;;;;        ;;;                 ;        ;;;;      ;;;;    ;;;;;;      ;;;;   
;    ;   ;;        ;     ;    ;       ;      ;;   ;                ;       ;;  ;;    ;    ;     ;;       ;    ;  
;    ;;;;          ;;    ;            ;      ;                     ;       ;    ;    ;          ;;       ;       
;    ;   ;;     ;;;;;    ;;           ;      ;                     ;      ;;    ;    ;;         ;;       ;;      
;    ;    ;    ;   ;;     ;;;;        ;     ;;                     ;      ;;;;;;;     ;;;;      ;;        ;;;;   
;    ;    ;;  ;;   ;;        ;;       ;      ;                     ;      ;;             ;;     ;;           ;;  
;    ;    ;;  ;;   ;;         ;       ;      ;                     ;       ;              ;     ;;            ;  
;    ;   ;;   ;;  ;;;   ;;   ;;       ;      ;;   ;                ;       ;;   ;   ;;   ;;     ;;  ;   ;;   ;;  
;    ;;;;;     ;;;; ;    ;;;;;     ;;;;;;     ;;;;                 ;        ;;;;     ;;;;;       ;;;;    ;;;;;   
;                                                                                                                
;                                                                                                                
;                                                                                                                
;                                                                                                                
;                                                                                                                

(define (basic-tests R)
  (test-suite "basic tests for ~a"
    (test-->
     R
     (term
      (ρ
       ((sig S1 unknown) ·)
       WAIT
       (loop^stop
        (present S1 pause pause)
        (present S1 pause pause))))
     (term
      (ρ
       ((sig S1 absent) ·)
       WAIT
       (loop^stop
        (present S1 pause pause)
        (present S1 pause pause)))))
    (test-->
     R
     (term (ρ {(sig S present) ·} WAIT pause)))
    (test-->
     R
     (term (signal S pause))
     (term (ρ {(sig S unknown) ·} WAIT pause)))
    (test-->
     R
     (term (ρ · WAIT (signal S pause)))
     (term (ρ · WAIT (ρ {(sig S unknown) ·} WAIT pause))))
    (test-->
     R
     (term (ρ ((sig S unknown) ·) WAIT pause))
     (term (ρ ((sig S absent) ·) WAIT pause)))
    (test-->
     R
     (term (ρ ((sig S unknown) ·) WAIT pause))
     (term (ρ ((sig S absent) ·) WAIT pause)))
    (test-->>∃
     R
     (term (ρ {(sig So unknown) ·} WAIT (ρ {(sig Si unknown) ·} WAIT (present Si (emit So) nothing))))
     (term (ρ {(sig So absent) ·} WAIT (ρ {(sig Si unknown) ·} WAIT (present Si (emit So) nothing)))))
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
     (term (ρ {(sig Si unknown) {(sig So unknown) ·}} WAIT (present Si (emit So) nothing)))
     (term (ρ {(sig Si unknown) {(sig So absent) ·}} WAIT (present Si (emit So) nothing))))
     
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
    (test-case "In which we demonstrate seq is a kind of a read of K_0"
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
        (ρ · GO
           (signal S2
             (seq (present S2 nothing nothing)
                  (trap
                   (seq (signal S1
                          (seq
                           (emit S1)
                           (present S1 (exit 0) (exit 0))))
                        (emit S2)))))))
                     
       complete?))))

;                                                                                                                          
;                                                                                                                          
;                                                                                                ;;                        
;      ;;;;                                                                                      ;;                        
;    ;;   ;;                                  ;;                                      ;;                                   
;    ;                                        ;;                                      ;;                                   
;   ;;          ;;;;     ; ;;;      ;;;;    ;;;;;;     ;;  ;;    ;    ;      ;;;    ;;;;;;     ;;;;     ;;    ;;    ;;;;   
;   ;;         ;;  ;;    ;;  ;;    ;    ;     ;;        ; ; ;    ;    ;    ;;   ;     ;;          ;     ;;    ;    ;;  ;;  
;   ;         ;;    ;    ;    ;    ;          ;;        ;;  ;    ;    ;    ;          ;;          ;      ;   ;;    ;    ;  
;   ;         ;;    ;    ;    ;    ;;         ;;        ;;       ;    ;    ;          ;;          ;      ;;  ;    ;;    ;  
;   ;;        ;;    ;    ;    ;     ;;;;      ;;        ;        ;    ;   ;;          ;;          ;      ;;  ;    ;;;;;;;  
;   ;;        ;;    ;    ;    ;        ;;     ;;        ;        ;    ;    ;          ;;          ;       ;  ;    ;;       
;    ;        ;;    ;    ;    ;         ;     ;;        ;        ;    ;    ;          ;;          ;       ; ;      ;       
;    ;;   ;;   ;;  ;;    ;    ;   ;;   ;;     ;;  ;     ;        ;   ;;    ;;   ;     ;;  ;       ;        ;;      ;;   ;  
;      ;;;;     ;;;;     ;    ;    ;;;;;       ;;;;    ;;;;      ;;;; ;     ;;;;       ;;;;    ;;;;;;      ;;       ;;;;   
;                                                                                                                          
;                                                                                                                          
;                                                                                                                          
;                                                                                                                          
;                                                                                                                          

(define (run-constructive-tests-for ->)
  (parameterize ([current-cache-all? #f])
    
    (define correct-terminus? incomplete?)
    (test-suite "bypass constructiveness?"
      (test-case "original test, one step"
        (test--?>
         ->
         (term (ρ (mtθ+S S1 unknown)
                  WAIT
                  (present S1
                           (ρ (mtθ+S S2 unknown)
                              WAIT
                              (seq (emit S2)
                                   (present S2
                                            nothing
                                            (emit S1))))
                           nothing)))
         #f))
      (test-case "the original case"
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
         correct-terminus?))
      (test-case "in which we demonstrate that `seq` isn't necessary to have the issue"
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
         correct-terminus?))
      (test-case "in which we demonstrate that ignoring seq dependencies is unsound"
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
         correct-terminus?))

      
      (test-case "In which we demonstrate that closed is unsound"
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
         correct-terminus?))
      (test-case "looking at par"
        (test-->>P
         ->
         (term
          (signal S2
            (seq (present S2 nothing nothing)
                 (trap
                  (seq (signal S1
                         (par
                          (emit S1)
                          (present S1 (exit 0) nothing)))
                       (emit S2))))))
         correct-terminus?))
      (test-case "in which we show cycles can be broken indirectly"
        (test-->>P
         ->
         (term
          (signal SO
            (signal SB   
              (present SO
                       (signal SE
                         (seq
                          (seq (emit SE)
                               (present SE nothing (emit SB)))
                          (present SB (emit SO) nothing)))
                       nothing))))
         correct-terminus?))
      (test-case "in which we show that you can't fix things by just lifting signals
(Because its not sound to lift a signal out of a loop, even with renaming)"
        (test-->>P
         ->
         (term
          (signal S1
            (present S1
                     (loop
                      (seq
                       (signal S2
                         (seq (emit S2)
                              (present S2
                                       nothing
                                       (emit S1))))
                       pause))
                     nothing)))
         correct-terminus?))
      ;; this test "fails" because
      ;; par-swap causes a cycle in the reduction graph.
      #;
      (test-case "could we have confluence issues?"
        (parameterize ([current-cache-all? #t])
          (test-->>P*
           ->
           (term
            (signal S1
              (present S1
                       (par
                        (signal S2
                          (seq (emit S2)
                               (present S2
                                        nothing
                                        (emit S1))))
                        (signal S3
                          (seq (emit S3)
                               (present S3
                                        nothing
                                        (emit S1)))))
                       nothing)))
           (lambda (x)
             (and
              (= (length x) 1)
              (correct-terminus? (first x))))))))))


;                                              
;                                              
;                                              
;                                              
;   ;;;;;;                                     
;   ;;   ;;                  ;                 
;   ;;    ;;                 ;                 
;   ;;     ;;   ;;;;;     ;;;;;;;     ;;;;;    
;   ;;     ;;   ;   ;;       ;        ;   ;;   
;   ;;     ;;        ;;      ;             ;;  
;   ;;     ;;        ;;      ;             ;;  
;   ;;     ;;    ;;;;;;      ;         ;;;;;;  
;   ;;     ;;   ;;   ;;      ;        ;;   ;;  
;   ;;     ;;  ;;    ;;      ;       ;;    ;;  
;   ;;    ;;   ;;    ;;      ;       ;;    ;;  
;   ;;   ;;     ;;  ;;;      ;;  ;    ;;  ;;;  
;   ;;;;;;      ;;;;  ;       ;;;;    ;;;;  ;  
;                                              
;                                              
;                                              
;                                              
;                                              


(define (run-data-constructive-tests-for ->)
  (parameterize ([current-cache-all? #f])
    
    (define correct-terminus? incomplete?)
    (test-suite "bypass constructiveness on data values?"
      (test-case "original test, one step"
        (test--?>
         ->
         (term (ρ (mtθ+s s1 0 old)
                  WAIT
                  (var x := (+ s1)
                       (ρ (mtθ+s s2 0 old)
                          WAIT
                          (seq (<= s2 (+ 0))
                               (<= s1 (+ s2)))))))
         #f)
        (test--?>
         ->
         (term (ρ (mtθ+s s1 0 old)
                  GO
                  (var x := (+ s1)
                       (ρ (mtθ+s s2 0 old)
                          WAIT
                          (seq (<= s2 (+ 0))
                               (<= s1 (+ s2)))))))
         #f)
        (test--?>
         ->
         (term (ρ (mtθ+s s1 0 old)
                  WAIT
                  (var x := (+ s1)
                       (ρ (mtθ+s s2 0 old)
                          GO
                          (seq (<= s2 (+ 0))
                               (<= s1 (+ s2)))))))
         #t))
      (test-case "the original case"
        (test-->>P
         ->
         (term
          (shared s1 := (+ 0)
            (var x := (+ s1)
                 (shared s2 := (+ 0)
                   (seq (<= s2 (+ 0))
                        (<= s1 (+ s2)))))))
         correct-terminus?))
      (test-case "in which we demonstrate that `seq` isn't necessary to have the issue"
        (test-->>P
         ->
         (term
          (shared s1 := (+ 0)
            (var x := (+ s1)
                 (shared s2 := (+ 0)
                   (par (<= s2 (+ 0))
                        (<= s1 (+ s2)))))))
         correct-terminus?))
      (test-case "in which we demonstrate that ignoring seq dependencies is unsound"
        (test-->>P
         ->
         (term
          (shared s1 := (+ 0)
            (seq (var x := (+ s1) nothing)
                 (shared s2 := (+ 0)
                   (seq (<= s2 (+ 0))
                        (<= s1 (+ s2)))))))
         correct-terminus?))

      
      (test-case "In which we demonstrate that closed is unsound"
        (test-->>P
         ->
         (term
          (shared s2 := (+ 0)
            (seq (var x := (+ s2) nothing)
                 (trap
                  (seq (shared s1 := (+ 0)
                         (seq
                          (<= s1 (+ 0))
                          (var x := (+ s1)
                               (if x (exit 0) nothing))))
                       (<= s2 (+ 0)))))))
         correct-terminus?))
      (test-case "looking at par"
        (test-->>P
         ->
         (term
          (shared s2 := (+ 0)
            (seq (var x := (+ s2) nothing)
                 (trap
                  (seq (shared s1 := (+ 0)
                         (par
                          (<= s1 (+ 0))
                          (var x := (+ s1)
                               (if x (exit 0) nothing))))
                       (<= s2 (+ 0)))))))
         correct-terminus?)
        (test-->>P
         ->
         (term
          (shared s2 := (+ 0)
            (seq (var x := (+ s2) nothing)
                 (trap
                  (par (shared s1 := (+ 0)
                         (par
                          (<= s1 (+ 0))
                          (var x := (+ s1)
                               (if x (exit 0) nothing))))
                       (<= s2 (+ 0)))))))
         correct-terminus?)
        (test-->>P
         ->
         (term
          (shared s2 := (+ 0)
            (seq (var x := (+ s2) nothing)
                 (trap
                  (par (shared s1 := (+ 0)
                         (seq
                          (<= s1 (+ 0))
                          (var x := (+ s1)
                               (if x (exit 0) nothing))))
                       (<= s2 (+ 0)))))))
         correct-terminus?))
      (test-case "in which we show cycles can be broken indirectly"
        (test-->>P
         ->
         (term
          (shared sO := (+ 0)
            (shared sB := (+ 0)
              (var x := (+ sO)
                   (signal SE
                     (seq
                      (seq (emit SE)
                           (present SE nothing (<= sB (+ 0))))
                      (<= sO (+ sB))))))))
         correct-terminus?))
      (test-case "in which we show that you can't fix things by just lifting variables
(Because its not sound to lift a signal out of a loop, even with renaming)"
        (test-->>P
         ->
         (term
          (shared s1 := (+ 0)
            (var x := (+ s1)
                 (loop
                  (seq
                   (signal S2
                     (seq (emit S2)
                          (present S2
                                   nothing
                                   (<= s1 (+ 0)))))
                   pause)))))
         correct-terminus?)))))


;                                                                    
;                                                                    
;                                                                    
;                                               ;;;;;                
;     ;;;;                                         ;;                
;    ;;   ;;                                       ;;                
;    ;     ;                                       ;;                
;   ;;     ;;   ;;; ;;;;   ;;;;;        ;;;;       ;;         ;;;;   
;   ;;     ;;    ;;;; ;    ;   ;;      ;;  ;;      ;;       ;;   ;;  
;   ;;     ;;    ;;;  ;         ;;    ;;           ;;       ;     ;  
;   ;      ;;    ;;             ;;    ;            ;;       ;     ;  
;   ;;     ;;    ;;         ;;;;;;    ;            ;;      ;;;;;;;;  
;   ;;     ;;    ;;        ;;   ;;    ;            ;;      ;;        
;   ;;     ;;    ;;       ;;    ;;    ;            ;;       ;        
;    ;     ;     ;;       ;;    ;;    ;;           ;;       ;;       
;    ;;   ;;     ;;        ;;  ;;;     ;;  ;;      ;;  ;    ;;;  ;;  
;     ;;;;      ;;;;;      ;;;;  ;      ;;;;        ;;;;      ;;;;   
;                                                                    
;                                                                    
;                                                                    
;                                                                    
;                                                                    


(define (test-oracle)
  (define (test-against-oracle p)
    (execute-test
     p
     '()
     '()
     '(() () () () () ())
     #:debug? #f #:limits? #f #:external? #t
     #:memory-limits? #f))
  (test-suite "run all of the constructivity tests against the external evaluators"
    (test-case "the original cases"
      (test-against-oracle
       (term
        (signal S1
          (present S1
                   (signal S2
                     (seq (emit S2)
                          (present S2
                                   nothing
                                   (emit S1))))
                   nothing))))
      (test-against-oracle
       (term
        (shared s1 := (+ 0)
          (var x := (+ s1)
               (shared s2 := (+ 0)
                 (seq (<= s2 (+ 0))
                      (<= s1 (+ s2)))))))))
    (test-case "in which we demonstrate that `seq` isn't necessary to have the issue"
      (test-against-oracle
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
                   nothing))))
      (test-against-oracle
       (term
        (shared s1 := (+ 0)
          (var x := (+ s1)
               (shared s2 := (+ 0)
                 (par (<= s2 (+ 0))
                      (<= s1 (+ s2)))))))))
    (test-case "in which we demonstrate that ignoring seq dependencies is unsound"
      (test-against-oracle
       (term
        (signal S1
          (seq (present S1 pause nothing)
               (signal S2
                 (seq (emit S2)
                      (present S2 nothing (emit S1))))))))
      (test-against-oracle
       (term
        (signal S1
          (seq (present S1 nothing nothing)
               (signal S2
                 (seq (emit S2)
                      (present S2 nothing (emit S1))))))))
      (test-against-oracle
       (term
        (shared s1 := (+ 0)
          (seq (var x := (+ s1) nothing)
               (shared s2 := (+ 0)
                 (seq (<= s2 (+ 0))
                      (<= s1 (+ s2)))))))))

      
    (test-case "In which we demonstrate that closed is unsound"
      (test-against-oracle
       (term
        (signal S2
          (seq (present S2 nothing nothing)
               (trap
                (seq (signal S1
                       (seq
                        (emit S1)
                        (present S1 (exit 0) nothing)))
                     (emit S2)))))))
      (test-against-oracle
       (term
        (shared s2 := (+ 0)
          (seq (var x := (+ s2) nothing)
               (trap
                (seq (shared s1 := (+ 0)
                       (seq
                        (<= s1 (+ 0))
                        (var x := (+ s1)
                             (if x (exit 0) nothing))))
                     (<= s2 (+ 0)))))))))
    (test-case "looking at par"
      (test-against-oracle
       (term
        (signal S2
          (seq (present S2 nothing nothing)
               (trap
                (seq (signal S1
                       (par
                        (emit S1)
                        (present S1 (exit 0) nothing)))
                     (emit S2)))))))
      (test-against-oracle
       (term
        (shared s2 := (+ 0)
          (seq (var x := (+ s2) nothing)
               (trap
                (seq (shared s1 := (+ 0)
                       (par
                        (<= s1 (+ 0))
                        (var x := (+ s1)
                             (if x (exit 0) nothing))))
                     (<= s2 (+ 0))))))))
      (test-against-oracle
       (term
        (shared s2 := (+ 0)
          (seq (var x := (+ s2) nothing)
               (trap
                (par (shared s1 := (+ 0)
                       (par
                        (<= s1 (+ 0))
                        (var x := (+ s1)
                             (if x (exit 0) nothing))))
                     (<= s2 (+ 0))))))))
      (test-against-oracle
       (term
        (shared s2 := (+ 0)
          (seq (var x := (+ s2) nothing)
               (trap
                (par (shared s1 := (+ 0)
                       (seq
                        (<= s1 (+ 0))
                        (var x := (+ s1)
                             (if x (exit 0) nothing))))
                     (<= s2 (+ 0)))))))))
    (test-case "in which we show cycles can be broken indirectly"
      (test-against-oracle
       (term
        (signal SO
          (signal SB   
            (present SO
                     (signal SE
                       (seq
                        (seq (emit SE)
                             (present SE nothing (emit SB)))
                        (present SB (emit SO) nothing)))
                     nothing)))))
      (test-against-oracle
       (term
        (shared sO := (+ 0)
          (shared sB := (+ 0)
            (var x := (+ sO)
                 (signal SE
                   (seq
                    (seq (emit SE)
                         (present SE nothing (<= sB (+ 0))))
                    (<= sO (+ sB))))))))))
    (test-case "in which we show that you can't fix things by just lifting signals
(Because its not sound to lift a signal out of a loop, even with renaming)"
      (test-against-oracle
       (term
        (signal S1
          (present S1
                   (loop
                    (seq
                     (signal S2
                       (seq (emit S2)
                            (present S2
                                     nothing
                                     (emit S1))))
                     pause))
                   nothing))))
      (test-against-oracle
       (term
        (shared s1 := (+ 0)
          (var x := (+ s1)
               (loop
                (seq
                 (signal S2
                   (seq (emit S2)
                        (present S2
                                 nothing
                                 (<= s1 (+ 0)))))
                 pause)))))))
    (test-case "testing against confluence"
      (test-against-oracle
       (term
        (signal S1
          (present S1
                   (par
                    (signal S2
                      (seq (emit S2)
                           (present S2
                                    nothing
                                    (emit S1))))
                    (signal S3
                      (seq (emit S3)
                           (present S3
                                    nothing
                                    (emit S1)))))
                   nothing)))))))
  
;                                                                        
;                                                                        
;                                                                        
;    ;;;;;;                                                              
;    ;                                                  ;;               
;    ;                                                  ;;               
;    ;        ;;   ;;     ;;;;       ;;;     ;    ;   ;;;;;;      ;;;;   
;    ;         ;;  ;     ;;  ;;    ;;   ;    ;    ;     ;;       ;;  ;;  
;    ;          ; ;;     ;    ;    ;         ;    ;     ;;       ;    ;  
;    ;;;;;       ;;     ;;    ;    ;         ;    ;     ;;      ;;    ;  
;    ;           ;;     ;;;;;;;   ;;         ;    ;     ;;      ;;;;;;;  
;    ;          ;;;     ;;         ;         ;    ;     ;;      ;;       
;    ;          ;  ;     ;         ;         ;    ;     ;;       ;       
;    ;         ;   ;;    ;;   ;    ;;   ;    ;   ;;     ;;  ;    ;;   ;  
;    ;;;;;;   ;;    ;;    ;;;;      ;;;;     ;;;; ;      ;;;;     ;;;;   
;                                                                        
;                                                                        
;                                                                        
;                                                                        
;                                                                        

(module+ test
  (void
   (run-tests
    (make-test-suite
     "all"
     (list (make-test-suite "test-relation" (list (basic-tests ⟶)))
           (make-test-suite
            "test-constructive"
            (list
             (run-constructive-tests-for ⟶)
             (run-data-constructive-tests-for ⟶)
             (test-oracle))))))))