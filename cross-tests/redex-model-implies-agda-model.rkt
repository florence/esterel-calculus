#lang racket

;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require "../redex/model/calculus.rkt"
         "../redex/test/generator.rkt"
         (only-in "../redex/model/shared.rkt" #;quasiquote) ;; don't import quasiquote!
         "send-lib.rkt"
         "send-steps.rkt"
         "send-std.rkt"
         "send-can.rkt"
         "send-cb.rkt"
         "send-complete.rkt"
         "send-blocked.rkt"
         "send-basics.rkt"
         (only-in "../redex/test/binding.rkt" esterel-L CB FV BV)
         "../redex/model/lset.rkt"
         racket/os
         redex/reduction-semantics)

(define do-random-tests? #f)
(define working-on-new-stuff? #f)
(define rand-iterations 100)
(command-line
 #:once-each
 [("--working-on-new-stuff") "working on new things mode" (set! working-on-new-stuff? #t)]
 [("--random" "-r") "run in random mode" (set! do-random-tests? #t)]
 [("--count" "-c") n "number of random iterations to run"
                   (begin
                     (set! rand-iterations (string->number n))
                     (unless (exact-positive-integer? rand-iterations)
                       (raise-user-error
                        (format "expected a positive integer number of iterations, got ~a"
                                n))))])

(define (main)
  (cond
    [working-on-new-stuff?
     (void)]
    [do-random-tests?
     (define uniq (getpid))
     (for ([i (in-range rand-iterations)])
       (set! filename-counter 0)
       (printf "\n===========================================================\nloop iteration ~a for ~a\n\n"
               i
               uniq)
       (flush-output)
       (define random-examples 100)
       (for ([x (in-range random-examples)])
         (establish-context
          (format "~a-scratch~a.agda" uniq x)
          (define p+source
            (case (random 3)
              [(0) (list 'R* (generate-term #:source R* 5))]
              [(1) (list 'p (generate-term esterel-L p 5))]
              [(2) (for/or ([i (in-range 10)])
                     ;; try 10 times to generate a term
                     (generate-term esterel-L #:satisfying (CB p) 5))]))

          (when p+source ;; if generation fails, just give up
            (define p (list-ref p+source 1))
            (define clean-p (clean-up-p p))
            (when (zero? (random 2))
              (set! clean-p
                    (clean-up-p
                     (term (fix (ρ ((shar sintroduced1 0 ready)
                                    ((shar sintroduced2 1 old)
                                     ((shar sintroduced3 9876543210 new)
                                      ((var· xintroduced1 0)
                                       ((var· xintroduced2 1)
                                        ·)))))
                                   ,clean-p)
                                (SINPUT) (SOUTPUT) () () () 0)))))
            (test-p/no-context clean-p #:can-θ (random-θ clean-p)))))
       (report-log)
       (build-scratch-all random-examples uniq)
       (run-agda (format "~ascratch-all.agda" uniq)))]
    [else (do-basic-tests)]))

;; tests meant to get basic coverage of `p` and the reduction relation
(define (do-basic-tests)
  (test-p (term (loop pause)))
  (test-p (term (loop^stop (exit 3) (loop pause))))
  (test-p (term (loop^stop pause (loop pause))))
  (test-p (term (loop^stop (seq nothing pause) (loop (seq nothing pause)))))
  (test-p (term (ρ ((sig S absent) ·) GO (present S pause nothing))))
  (test-p (term (ρ ((sig S absent) ·) WAIT (present S pause nothing))))
  (test-p (term (seq (seq (seq (exit 0) nothing) nothing) nothing)))
  (test-p (term (par nothing pause)))
  (test-p (term (par pause nothing)))
  (test-p (term (par nothing nothing)))
  (test-p (term (ρ ((sig S unknown) ·) GO (suspend (exit 4) S))))
  (test-p (term (ρ ((sig S unknown) ·) WAIT (suspend (exit 4) S))))
  (test-p (term (ρ ((sig S unknown) ·) GO (trap (exit 4)))))
  (test-p (term (ρ ((sig S unknown) ·) WAIT (trap (exit 4)))))
  (test-p (term (par (trap (exit 0)) (trap nothing))))
  (test-p (term (par (exit 1) (exit 2))))
  (test-p (term (par (exit 2) (exit 1))))
  (test-p (term (par (exit 1) pause)))
  (test-p (term (par (exit 1) nothing)))
  (test-p (term (par pause (exit 1))))
  (test-p (term (par nothing (exit 1))))
  (test-p (term (signal S (seq (emit S) (present S pause nothing)))))
  (test-p (term (ρ ((sig S unknown) ·) GO (seq (emit S) (present S pause nothing)))))
  (test-p (term (ρ ((sig S unknown) ·) WAIT (seq (emit S) (present S pause nothing)))))
  (test-p (term (ρ ((sig S1 unknown) ((sig S2 unknown) ·)) GO
                   (seq (emit S2) (emit S1)))))
  (test-p (term (ρ ((sig S1 unknown) ((sig S2 unknown) ·)) WAIT
                   (seq (emit S2) (emit S1)))))
  (test-p (term (ρ ((sig S present) ·) GO (seq nothing (present S pause nothing)))))
  (test-p (term (ρ ((sig S present) ·) WAIT (seq nothing (present S pause nothing)))))
  (test-p (term (ρ ((sig S present) ·) GO (present S pause nothing))))
  (test-p (term (ρ ((sig S present) ·) WAIT (present S pause nothing))))
  (test-p (term (par pause nothing)))
  (test-p (term (loop pause)))
  (test-p (term (ρ ((shar s1 1 new) ((shar s2 2 old) ·)) GO pause)))
  (test-p (term (ρ ((shar s1 1 new) ((shar s2 2 old) ·)) WAIT pause)))
  (test-p (term (ρ ((shar s1 2 ready) ((shar s2 2 ready) ·)) GO (shared s1 := (+ 1 s2) pause))))
  (test-p (term (ρ ((shar s1 2 old) ((shar s2 2 ready) ·)) GO (shared s1 := (+ 1 s2) pause))))
  (test-p (term (ρ ((shar s1 2 ready) ((shar s2 2 ready) ·)) WAIT (shared s1 := (+ 1 s2) pause))))
  (test-p (term (ρ ((shar s1 2 old) ((shar s2 2 ready) ·)) WAIT (shared s1 := (+ 1 s2) pause))))
  (test-p (term (ρ ((shar s1 2 old) ((shar s2 3 ready) ·)) GO (<= s1 (+ 4 s2)))))
  (test-p (term (ρ ((shar s1 2 new) ((shar s2 3 ready) ·)) GO (<= s1 (+ 4 s2)))))
  (test-p (term (ρ ((shar s1 2 old) ((shar s2 3 ready) ·)) WAIT (<= s1 (+ 4 s2)))))
  (test-p (term (ρ ((shar s1 2 new) ((shar s2 3 ready) ·)) WAIT (<= s1 (+ 4 s2)))))
  (test-p (term (ρ ((var· x 123) ·) GO (seq (var x := (+ 414 x) pause) nothing))))
  (test-p (term (ρ ((var· x 123) ·) WAIT (seq (var x := (+ 414 x) pause) nothing))))
  (test-p (term (ρ ((var· x 123) ·) GO (seq (:= x (+ 132)) nothing))))
  (test-p (term (ρ ((var· x 123) ·) WAIT (seq (:= x (+ 132)) nothing))))
  (test-p (term (ρ ((var· x 0) ·) GO (if x pause nothing))))
  (test-p (term (ρ ((var· x 0) ·) WAIT (if x pause nothing))))
  (test-p (term (ρ ((var· x 123) ·) GO (if x pause nothing))))
  (test-p (term (ρ ((var· x 123) ·) WAIT (if x pause nothing))))
  (test-p (term (ρ ((shar s1 2 ready) ((shar s2 2 ready) ·)) GO (ρ ((shar s1 3 new) ·) GO pause))))
  (test-p (term (ρ ((shar s1 2 ready) ((shar s2 2 ready) ·)) GO (ρ ((shar s1 3 new) ·) WAIT pause))))
  (test-p (term (ρ ((shar s1 2 ready) ((shar s2 2 ready) ·)) WAIT (ρ ((shar s1 3 new) ·) GO pause))))
  (test-p (term (ρ ((shar s1 2 ready) ((shar s2 2 ready) ·)) WAIT (ρ ((shar s1 3 new) ·) WAIT pause))))
  

  ;; tests inspired by looking at the definition of CorrectBinding
  (test-p `(emit S))
  (test-p `(signal S (emit S)))
  (test-p `(signal S1 (emit S2)))
  (test-p `(present S (signal S (emit S2)) (signal S (emit S2))))
  (test-p `(present S nothing pause))

  (test-p `(par (signal S pause) (signal S pause)))
  (test-p `(par (signal S pause) (emit S)))
  (test-p `(par (emit S) (signal S pause)))
  (test-p `(par (emit S) (emit S)))
  (test-p `(par (signal S1 pause) (emit S2)))
  (test-p `(par (emit S2) (signal S1 pause)))
  (test-p `(par (signal S2 pause) (signal S1 pause)))
  (test-p `(par (var x := (+) (:= x (+ x1)))
                (var x := (+) (:= x (+ x2)))))
  (test-p `(par (var x := (+) (:= x (+ x1)))
                (var x := (+) (:= x (+ x1)))))
  (test-p `(par (var x := (+) (:= x (+ x1)))
                (var x := (+) (:= x1 (+ x2)))))
  (test-p `(par (var x1 := (+) (:= x1 (+ x1)))
                (var x2 := (+) (:= x2 (+ x2)))))
  (test-p `(par (var x1 := (+) (:= x1 (+ x3)))
                (var x2 := (+) (:= x2 (+ x2)))))
  (test-p `(par (var x2 := (+) (:= x2 (+ x2)))
                (var x1 := (+) (:= x1 (+ x3)))))
  (test-p `(par (var x2 := (+) (:= x2 (+ x3)))
                (var x1 := (+) (:= x1 (+ x3)))))
  (test-p `(loop (signal SS (emit SQ))))
  (test-p `(loop (signal SC (emit SQ))))
  (test-p `(loop (signal SI (emit SQ))))
  (test-p `(loop (signal SS (emit SI))))
  (test-p `(loop (signal SS (emit SC))))
  (test-p `(seq (signal S1 (emit S2)) (signal S3 (emit S4))))
  (test-p `(seq (signal S4 (emit S2)) (signal S3 (emit S4))))
  (test-p `(suspend (signal S1 (emit S2)) S3))
  (test-p `(suspend (signal S3 (emit S2)) S3))
  (test-p `(exit 11))
  (test-p `(trap (signal S3 (emit S2))))
  (test-p `(shared s := (+) pause))
  (test-p `(shared s := (+) (present S nothing pause)))
  (test-p `(shared s := (+ s1) (<= s (+ s2))))
  (test-p `(shared s := (+ s1) (<= s2 (+ s))))
  (test-p `(var x := (+) pause))
  (test-p `(var x := (+) (present S nothing pause)))
  (test-p `(var x := (+ x1) (:= x (+ x2))))
  (test-p `(var x := (+ x1) (:= x2 (+ x))))
  (test-p `(var x := (+ 11) (if x (signal S1 (emit S2)) (signal S3 (emit S4)))))
  (test-p `(if x (signal S1 (emit S2)) (signal S3 (emit S4))))
  (test-p `(ρ ((sig S present) ((var· x 123) ((shar s2 2 ready) ·))) GO nothing))
  (test-p `(ρ ((sig S present) ((var· x 123) ((shar s2 2 ready) ·))) WAIT nothing))
  (test-p `(ρ ((sig S present) ((var· x 123) ((shar s2 2 ready) ·))) GO
              (seq (emit S)
                   (seq (:= x (+))
                        (<= s (+))))))
  (test-p `(ρ ((sig S present) ((var· x 123) ((shar s2 2 ready) ·))) WAIT
              (seq (emit S)
                   (seq (:= x (+))
                        (<= s (+))))))
  (test-p `(ρ ((sig S present) ((var· x 123) ((shar s2 2 ready) ·))) GO
              (signal S pause)))
  (test-p `(ρ ((sig S present) ((var· x 123) ((shar s2 2 ready) ·))) WAIT
              (signal S pause)))

  ;; Can-inspired tests
  (test-p `(present S nothing (emit S)) #:can-θ `·)
  (test-p `(present S nothing (emit S)) #:can-θ `((sig S present) ·))
  (test-p `(present S nothing (emit S)) #:can-θ `((sig S absent) ·))
  (test-p `(present S nothing (emit S)) #:can-θ `((sig S unknown) ·))
  (test-p `(present S (emit S) nothing) #:can-θ `((sig S present) ·))
  (test-p `(present S (emit S) nothing) #:can-θ `((sig S absent) ·))
  (test-p `(present S (emit S) nothing) #:can-θ `((sig S unknown) ·))
  (test-p `(seq pause (emit S)) #:can-θ `·)
  (test-p `(seq nothing (emit S)) #:can-θ `·)
  (test-p `(seq (emit S1) (emit S2)) #:can-θ `·)
  (test-p `(seq (exit 11) (emit S2)) #:can-θ `·)
  (test-p `(seq pause (emit S2)) #:can-θ `·)
  (test-p `(par (exit 3) (exit 47)) #:can-θ `·)
  (test-p `(par (exit 3) pause) #:can-θ `·)
  (test-p `(par pause (exit 3)) #:can-θ `·)
  (test-p `(par pause nothing) #:can-θ `·)
  (test-p `(par nothing pause) #:can-θ `·)
  (test-p `(par (emit S1) (emit S2)) #:can-θ `·)
  (test-p `(signal S (present S (signal S2 (present S2 (emit S) nothing)) nothing)))
  (test-p `(signal SC (signal Si (seq (present SC nothing nothing)
                                      (present Si (emit SC) nothing)))))
     
  (test-p `(par (seq pause (emit SI))
                (seq (present SI nothing (emit SC))
                     (present SC (emit SC) nothing)))
          #:can-θ
          `((sig SI unknown)
            ((sig SC unknown)
             ·)))
  (test-p `(par (present SS (exit 0) nothing)
                nothing)
          #:can-θ
          `{(sig SS unknown) ·})
  (test-p `(seq
            (ρ {(sig S_I unknown) ((sig S_C unknown) ·)} GO
               (par (seq nothing (emit S_I))
                    (seq
                     (seq
                      (present S_I nothing (emit S_C))
                      (present S_C (emit S_C) nothing))
                     pause)))
            (loop nothing)))
  (test-p `(seq
            (ρ {(sig S_I unknown) ((sig S_C unknown) ·)} WAIT
               (par (seq nothing (emit S_I))
                    (seq
                     (seq
                      (present S_I nothing (emit S_C))
                      (present S_C (emit S_C) nothing))
                     pause)))
            (loop nothing)))

  ;; tests gathered/simplified from random test case failures
  (test-p (term (seq (ρ ((sig SI unknown) ((sig SC unknown) ·)) GO
                        (par (seq pause (emit SI))
                             (seq (present SI nothing (emit SC))
                                  (present SC (emit SC) nothing))))
                     (loop pause))))
  (test-p (term (seq (ρ ((sig SI unknown) ((sig SC unknown) ·)) WAIT
                        (par (seq pause (emit SI))
                             (seq (present SI nothing (emit SC))
                                  (present SC (emit SC) nothing))))
                     (loop pause))))
  (test-p (term (ρ ((shar sS 1 old) ((var· xs 0) ((sig Sq unknown) ·))) GO
                   (present
                    SF
                    (suspend
                     (par (signal SN (var xM := (+) (present SP nothing nothing)))
                          (par (:= xp (+)) nothing)) SJ)
                    (if xI
                        (ρ · GO (trap (signal Se (var xT := (+) nothing))))
                        (emit SSi))))))
  (test-p (term (ρ ((shar sS 1 old) ((var· xs 0) ((sig Sq unknown) ·))) GO
                   (present
                    SF
                    (suspend
                     (par (signal SN (var xM := (+) (present SP nothing nothing)))
                          (par (:= xp (+)) nothing)) SJ)
                    (if xI
                        (ρ · WAIT (trap (signal Se (var xT := (+) nothing))))
                        (emit SSi))))))
  (test-p (term (ρ ((shar sS 1 old) ((var· xs 0) ((sig Sq unknown) ·))) WAIT
                   (present
                    SF
                    (suspend
                     (par (signal SN (var xM := (+) (present SP nothing nothing)))
                          (par (:= xp (+)) nothing)) SJ)
                    (if xI
                        (ρ · GO (trap (signal Se (var xT := (+) nothing))))
                        (emit SSi))))))
  (test-p (term (ρ ((shar sS 1 old) ((var· xs 0) ((sig Sq unknown) ·))) WAIT
                   (present
                    SF
                    (suspend
                     (par (signal SN (var xM := (+) (present SP nothing nothing)))
                          (par (:= xp (+)) nothing)) SJ)
                    (if xI
                        (ρ · WAIT (trap (signal Se (var xT := (+) nothing))))
                        (emit SSi))))))
  (test-p (term (ρ ((shar sk 1 old) ·) GO
                   (ρ ((shar sz 1 old) ·) GO
                      (<= sz (+))))))
  (test-p (term (ρ ((shar sk 1 old) ·) GO
                   (ρ ((shar sz 1 old) ·) WAIT
                      (<= sz (+))))))
  (test-p (term (ρ ((shar sk 1 old) ·) WAIT
                   (ρ ((shar sz 1 old) ·) GO
                      (<= sz (+))))))
  (test-p (term (ρ ((shar sk 1 old) ·) WAIT
                   (ρ ((shar sz 1 old) ·) WAIT
                      (<= sz (+))))))
  (test-p (term (suspend (ρ · GO (exit 0)) S)))
  (test-p (term (suspend (ρ · WAIT (exit 0)) S)))
  (test-p (term
           (ρ ((shar sW 4 ready) ((sig Sm unknown) ·)) GO
              (seq (suspend
                    (trap
                     (par
                      (par (present Sm (exit 0) (ρ · GO nothing))
                           (emit SOUTPUT))
                      (ρ ((var· x5537 1) ·) GO pause)))
                    SINPUT)
                   (emit SOUTPUT)))))
  (test-p (term
           (ρ ((shar sW 4 ready) ((sig Sm unknown) ·)) WAIT
              (seq (suspend
                    (trap
                     (par
                      (par (present Sm (exit 0) (ρ · GO nothing))
                           (emit SOUTPUT))
                      (ρ ((var· x5537 1) ·) GO pause)))
                    SINPUT)
                   (emit SOUTPUT)))))
  (test-p (term
           (ρ ((shar sW 4 ready) ((sig Sm unknown) ·)) GO
              (seq (suspend
                    (trap
                     (par
                      (par (present Sm (exit 0) (ρ · GO nothing))
                           (emit SOUTPUT))
                      (ρ ((var· x5537 1) ·) WAIT pause)))
                    SINPUT)
                   (emit SOUTPUT)))))
  (test-p (term
           (ρ ((shar sW 4 ready) ((sig Sm unknown) ·)) GO
              (seq (suspend
                    (trap
                     (par
                      (par (present Sm (exit 0) (ρ · WAIT nothing))
                           (emit SOUTPUT))
                      (ρ ((var· x5537 1) ·) GO pause)))
                    SINPUT)
                   (emit SOUTPUT)))))
  (test-p (term
           (ρ ((shar sW 4 ready) ((sig Sm unknown) ·)) WAIT
              (seq (suspend
                    (trap
                     (par
                      (par (present Sm (exit 0) (ρ · WAIT nothing))
                           (emit SOUTPUT))
                      (ρ ((var· x5537 1) ·) WAIT pause)))
                    SINPUT)
                   (emit SOUTPUT)))))
  (test-p (term
           (ρ ((shar sW 4 ready) ((sig Sm unknown) ·)) GO
              (seq (suspend
                    (trap
                     (par
                      (par (present Sm (exit 0) (ρ · WAIT nothing))
                           (emit SOUTPUT))
                      (ρ ((var· x5537 1) ·) WAIT pause)))
                    SINPUT)
                   (emit SOUTPUT)))))
  (test-p
   (term
    (loop^stop (par (seq (suspend (suspend pause SA) SNIpx)
                         (loop^stop (:= xF (+ 0)) pause))
                    (loop^stop (seq (par pause pause) (par nothing nothing))
                               (loop (loop^stop pause nothing))))
               (emit Sq))))
  (test-p
   (term
    (loop (par (ρ ((shar sB 0 ready) ((var· xL 0) ·)) GO
                  (suspend (signal Sm (exit 0)) SY))
               (if xl (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1)))) (signal Si (trap (emit Sp))))))))
  (test-p
   (term
    (loop (par (ρ ((shar sB 0 ready) ((var· xL 0) ·)) WAIT
                  (suspend (signal Sm (exit 0)) SY))
               (if xl (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1)))) (signal Si (trap (emit Sp))))))))
  (test-p
   (term
    (loop
     (par
      (ρ ((shar sB 0 ready) ((var· xL 0) ·)) GO
         (suspend (signal Sm (exit 0)) SY))
      (if xl
          (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1))))
          (signal Si (trap (emit Sp))))))))
  (test-p
   (term
    (loop
     (par
      (ρ ((shar sB 0 ready) ((var· xL 0) ·)) WAIT
         (suspend (signal Sm (exit 0)) SY))
      (if xl
          (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1))))
          (signal Si (trap (emit Sp))))))))
  (test-p
   (term
    (shared s1
      :=
      (+ 19)
      (seq
       (<= s1 (+))
       (var x1 := (+ s1) (if x1 (emit SO) nothing))))))

  (report-log)
  (build-scratch-all filename-counter)
  (run-agda "scratch-all.agda"))

(define (build-scratch-all count [extra ""])
  (call-with-output-file (build-path scratch-directory (format "~ascratch-all.agda" extra))
    (λ (port)
      (fprintf port "module _ where\n")
      (for ([i (in-range count)])
        (fprintf port "import scratch~a\n" i)))
    #:exists 'truncate))

(define filename-counter 0)
(define (test-p _p #:can-θ [can-θ `·])
  (with-handlers ([void (lambda (x) (displayln `(error while testing ,_p ,can-θ)) (raise x))])
    (define filename (format "scratch~a.agda" filename-counter))
    (set! filename-counter (+ filename-counter 1))
    (establish-context
     filename

     (test-p/no-context _p #:can-θ can-θ))))

(define (test-p/no-context _p #:can-θ can-θ)
  (define p (clean-up-p _p))
  (send-steps p)
  (send-can p can-θ)
  (send-CB p)
  ;(send-complete p)
  (send-blocked can-θ p)
  (send-std p))

(define/contract (random-θ p)
  (-> p? θ?)
  (define L (term (LU (FV ,p) (BV ,p))))
  (clean-up-θ
   (let loop ([L L])
     (match L
       [`{} `·]
       [`(,var ,L)
        (define env-v
          (match var
            [(? S? S) `(sig ,S ,(generate-term esterel-L status 5))]
            [(? s? s) `(shar ,s ,(gen-ev 5) ,(gen-shared-status 5))]
            [(? x? x) `(var· ,x ,(gen-ev 5))]))
        `{,env-v ,(loop L)}]))))
(define gen-status (generate-term esterel-L status))
(define gen-ev (generate-term esterel-L ev))
(define gen-shared-status (generate-term esterel-L shared-status))

(module+ main (main))
