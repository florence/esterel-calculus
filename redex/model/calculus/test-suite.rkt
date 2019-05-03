#lang racket
(require
  racket/require
  (multi-in esterel-calculus/redex/model/calculus/variants
            (base closed-and-control graph control))
  esterel-calculus/redex/model/calculus/define
  esterel-calculus/redex/rackunit-adaptor
  esterel-calculus/redex/model/shared
  (subtract-in redex/reduction-semantics
               esterel-calculus/redex/rackunit-adaptor)
  rackunit
  rackunit/text-ui
  (for-syntax syntax/parse))
(define-syntax test-relation
  (syntax-parser
    [(_ R:id)
     #`(run-tests-as R (symbol->string 'R))]))
(define-syntax test-constructive
  (syntax-parser
    [(_ R:id good bad errored)
     #`(run-constructive-tests-for R (symbol->string 'R)  good bad errored)]))
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

(define (run-tests-as R name)
  (test-suite (format "basic tests for ~a" name)
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

(define (run-constructive-tests-for -> name good bad errored [prepair values])
  (define is-good? #t)
  (define errored? #f)
  (define old-handle (current-check-handler))
  (parameterize ([current-cache-all? #f]
                 [use-fast-par-swap? #t]
                 [current-check-handler
                  (lambda (x)
                    (set! errored? #t)
                    (old-handle x))])
    
    (define (correct-terminus? p)
      ((if (fail-on?) complete? incomplete?) p))
    (define fail-on? (make-parameter #f))
    (define-syntax fail-on
      (syntax-parser
        [(fail-on (Rs:id ...) body ...)
         #`(begin
             (when (memq -> (list Rs ...))
               (set! is-good? #f))
             (parameterize ([fail-on? (memq -> (list Rs ...))])
               body ...))]))
    (test-suite (format "Does ~a bypass constructiveness?" name)
      #:after
      (lambda ()
        (define (box-cons! a b)
          (set-box! b (cons a (unbox b))))
        (cond
          [errored? (box-cons! name errored)]
          [is-good? (box-cons! name good)]
          [else (box-cons! name bad)]))
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
         (eq? -> R)))
      (test-case "the original case"
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
          correct-terminus?)))
      (test-case "in which we demonstrate that `seq` isn't necessary to have the issue"
        (fail-on
         (R R-no-seq R-no-present)
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
          correct-terminus?)))
      (test-case "in which we demonstrate that ignoring seq dependencies is unsound"
        (fail-on
         (R R-no-seq R-no-present)
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

      
      (test-case "In which we demonstrate that closed is unsound"
        (fail-on
         (R R-closed R-no-present R-no-seq)
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
      (test-case "looking at par"
        (fail-on
         (R R-no-present R-closed R-no-seq)
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
          correct-terminus?)))
      (test-case "in which we show cycles can be broken indirectly"
        (fail-on
         (R R-safe-after-reduction)
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
          correct-terminus?)))
      (test-case "in which we show that you can't fix things by just lifting signals
(Because its not sound to lift a signal out of a loop, even with renaming)"
        (fail-on
         (R)
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
          correct-terminus?)))
      #;
      (test-case "could we have confluence issues?"
        (fail-on
         (R)
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
               (correct-terminus? (first x)))))))))))
  
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
(define all-relations
  (list
   R
   R-empty
   R-closed
   R-no-control
   R-no-seq
   R-no-present
   R-E
   R-control-closed
   R-safe-after-reduction
   ⟶))

(module+ test
  (define good (box empty))
  (define bad (box empty))
  (define errored (box empty))
  (void
   (run-tests
    (make-test-suite
     "all"
     (list (make-test-suite "test-relation" (list (test-relation ⟶)))
           (make-test-suite
            "test-constructive"
            (list
             (test-constructive  ⟶ good bad errored))
            #:after
            (lambda ()
              (printf "The reduction variants broke down into:\n good: ~a\n bad ~a\n errored: ~a\n"
                      (unbox good)
                      (unbox bad)
                      (unbox errored)))))))))