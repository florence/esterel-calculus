#lang racket
(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/potential-function
         esterel-calculus/redex/model/instant
         esterel-calculus/redex/model/calculus
         (prefix-in standard: esterel-calculus/redex/model/reduction)
         (prefix-in cos: esterel-calculus/redex/cos/model)
         esterel-calculus/circuits/compiler
         "generator.rkt"
         racket/sandbox
         unstable/error
         rackunit
         racket/random
         (prefix-in r: racket)
         racket/logging)

(module+ test
  (require (submod esterel-calculus/redex/model/reduction test)))

(define-logger eval-test)

(define-syntax quasiquote (make-rename-transformer #'term))

(provide (all-defined-out))

;; single point of control for all tests
(define (do-test #:limits? [limits? #f]
                 #:count [attempts 10000]
                 #:debug [d #f]
                 #:continue-on-fail? [c? #t]
                 #:external [external #f]
                 #:memory-limits? [memory-limits? #f])
  (define test-count 0)
  (define start-time (current-seconds))

  (redex-check
   esterel-check
   (p-check (name i (S_!_g S_!_g ...)) (name o (S_!_g S_!_g ...)) ((S_1 ...) (S ...) ...))
   (redex-let
    esterel-eval
    ([(S_i ...) `i]
     [(S_o ...) `o])
    (begin
      (set! test-count (add1 test-count))
      (when (zero? (modulo test-count 100))
        (printf "running test ~a\n" test-count)
        (printf "has been running for ~a seconds\n" (- (current-seconds) start-time))
        (flush-output))
      (log-eval-test-debug (list `test-reduction ``p-check ``i ``o ``((S_1 ...) (S ...) ...) '#:limits? limits? '#:memory-limits? memory-limits?))
      (with-handlers ([exn:fail?
                       (lambda (e)
                         (error-display e)
                         #f)])
        (execute-test `p-check `i `o `((S_1 ...) (S ...) ...) #:limits? limits? #:debug? d #:external? external #:memory-limits? memory-limits?))))
   #:prepare fixup
   #:attempts attempts
   #:keep-going? c?))

(define (warn-about-uninstalled-hiphop)
  (printf "\n\nWARNING: hiphop is not installed; skipping some tests\n\n\n")
  (set! warn-about-uninstalled-hiphop void))
(define (execute-test p i o Ss
                      #:limits? limits?
                      #:debug? debug?
                      #:external? external?
                      #:memory-limits? memory-limits?)
  (define res (and external? (esterel-oracle p i o Ss)))
  (define res2 (and external? (hiphop-oracle p i o Ss)))
  (define circuit-res
    (if (redex-match? esterel-check p-pure p)
        (run/circuit p i o Ss)
        #f))
  (cond
    [(equal? res 'not-installed)
     (warn-about-uninstalled-esterel)]
    [(equal? res2 'not-installed)
     (warn-about-uninstalled-hiphop)]
    [else
     (unless (equal? res res2)
       (fprintf (current-error-port)
                "BAD: Esterelv5 and Hiphop behave differently on (~a ~a ~a ~a)\nV5: ~a\nHH: ~a\n\n" p i o Ss res res2))])
  (test-calculus p i o Ss #:limits? limits? #:debug? debug?
                 #:oracle (if (eq? res 'not-installed) #f res)
                 #:memory-limits? memory-limits?
                 #:other-sequences (and circuit-res
                                        (list (list 'circuits circuit-res)))))

(define (test-reduction p-check i o s #:limits? limits? #:debug? [debug? #f] #:oracle [oracle #f]
                        #:memory-limits? memory-limits?
                        #:other-sequences [os #f])
  (with-logging-to-port
   (current-output-port)
   (lambda ()
     (relate `((convert ,p-check) ())
             `(add-extra-syms ,p-check ,(append i o))
             s
             i
             o
             #:limits? limits?
             #:memory-limits? memory-limits?
             #:debug? debug?
             #:oracle oracle
             #:other-sequences os))
   #:logger (if debug? (current-logger) (make-logger))
   'debug
   'eval-test))

(define (test-calculus p-check i o s #:limits? limits? #:debug? [debug? #f]
                       #:memory-limits? memory-limits?
                       #:oracle [oracle #f]
                       #:other-sequences [os #f])
  ;; boundary signals shouldnt be used in reductions
  ;; output might be okay, input is not
  (define-values (p* extras) (calc-shuffle p-check))
  (define p `(add-extra-syms
              ,p*
              ,(append i o)))
  (define r  `((convert ,p-check) ()))
  (log-eval-test-debug
    (format "testing: ~a\n derived from ~a\n"
            `(relate `,r
                     `,p
                     `,s
                     `,i
                     `,o
                     #:limits? ,limits?
                     #:memory-limits? ,memory-limits?
                     #:debug? ,debug?
                     #:other-sequences ,os
                     #:oracle ,oracle)
            `(add-extra-syms ,p-check ,(append i o))))
  (relate r
          p
          s
          i
          o
          #:limits? limits?
          #:debug? debug?
          #:extras extras
          #:memory-limits? memory-limits?
          #:other-sequences os
          #:oracle oracle))

(define (relate pp qp ins in out #:limits? [limits? #f] #:debug? [debug? #f] #:extras [extras ""]
                #:oracle [oracle #f]
                ;; (nonempty-listof (list/c symbol? (listof (or/c #f (setof symbol)))))) or #f
                ;; length of inner list must be equal to length of ins
                #:other-sequences [os #f]
                #:memory-limits? [memory-limits? #f])
  (define (remove-not-outs l)
    (filter (lambda (x) (member x out)) l))
  ;;TODO update to check which instant had the non-constructive behavior
  (define olist (if (list? oracle) oracle (build-list (length ins) (lambda (_) #f))))
  (define other-sequence-lists
    (if os
        (apply map
               (lambda x
                 (map list (map first os) x))
               (map second os))
         (build-list (length ins) (lambda (_) empty))))
           
  (log-eval-test-debug "using oracle: ~a\n" olist)
  (log-eval-test-debug "using ins: ~a\n" ins)
  (for/fold ([p pp]
             [q qp])
            ([i (in-list ins)]
             [t (in-list olist)]
             [others other-sequence-lists]
             #:break
             (or
              ;; program was non constructive
              (and (not p) (not q) (implies oracle (symbol? oracle))
                   (log-eval-test-debug "breaking due to non-constructiveness"))
              ;; the COS model is done and we have no oracle data
              (and (cos:done? p)
                   (not oracle)
                   (empty? others)
                   (standard:done? q)
                   (log-eval-test-debug "breaking due to program completion and lack of oracle or other sequences"))))
    (log-eval-test-debug "running:\np:")
    (log-eval-test-debug (pretty-format p))
    (log-eval-test-debug  "q:")
    (log-eval-test-debug (pretty-format q))
    (log-eval-test-debug "i:")
    (log-eval-test-debug (pretty-format i))
    (log-eval-test-debug "current others:")
    (log-eval-test-debug (pretty-format others))
    (with-handlers ([(lambda (x) (and (exn:fail:resource? x)
                                      (memq (exn:fail:resource-resource x)
                                            '(time memory))))
                     (lambda (_)
                       (log-eval-test-warning "timeout")
                       (log-eval-test-debug "program was: ~a" p)
                       (values #f #f))])
      (with-limits (and limits? 120) (and memory-limits? 512)
                   (log-eval-test-debug "running instant\n")
                   (log-eval-test-debug (pretty-format (list 'instant q (setup-r-env i in))))

        (define new-reduction/standard `(instant ,q ,(setup-r-env i in)))

       
        (log-eval-test-debug "running c->>\n")
        (log-eval-test-debug
         (pretty-format
          (list 'c->> `(machine ,(first p) ,(second p))
                (setup-*-env i in)
                '(machine pbar data_*) '(S ...) 'k)))

        (define constructive-reduction
          (cond [(and (cos:done? p) (standard:done? q))
                 ;; in this case the COS semantics disagree's with the
                 ;; esterel implementation. To handle this, just disregard what the COS does
                 ;; (Valid because the semantics doesn't really describe what happens post termination)
                 'ignore]
                [else
                 (judgment-holds
                  (cos:c->> (machine ,(first p) ,(second p))
                            ,(setup-*-env i in)
                            (machine pbar data_*) (S ...) k)
                  (pbar data_* (S ...)))]))
        (log-eval-test-debug "cos results:")
        (log-eval-test-debug (pretty-format constructive-reduction))

        (match* (constructive-reduction new-reduction/standard oracle)
          [('ignore (list q2 qouts) _)
           (define qset (list->set (remove-not-outs qouts)))
           (define tset (and t (list->set t)))
           (unless (and (implies t (equal? qset tset))
                        (andmap (lambda (x) (equal? qset (second x))) others))
             (error 'test
                    (string-append "VERY BAD: programs were <terminated>\n"
                                   "~a -> (~a ~a)\n"
                                   "exec: ~a\n"
                                   "others: ~a\n"
                                   "under ~a\nThe original call was ~a\n"
                                   extras)
                    q
                    q2
                    qset
                    tset
                    others
                    i
                    (list 'relate pp qp ins in out)))
           (values p q2)]
          [(`((,p2 ,data ,(and pouts b1))
              (,_ ,_ ,b2s) ...)
            (list q2 qouts)
            _)
           #:when (andmap (lambda (x) (equal? (list->set b1) (list->set x)))
                          b2s)
           (define pset (list->set (remove-not-outs pouts)))
           (define qset (list->set (remove-not-outs qouts)))
           (define tset (and t (list->set t)))
           (unless (and (equal? pset qset)
                        (andmap (lambda (x) (equal? pset (second x))) others)
                        (implies t (equal? qset tset)))
             (error 'test
                    (string-append "VERY BAD: programs were ~a -> (~a ~a)\n"
                                   "~a -> (~a ~a)\n"
                                   "exec: ~a\n"
                                   "others: ~a\n"
                                   "under ~a\nThe original call was ~a\n"
                                   extras)
                    p
                    p2
                    pset
                    q
                    q2
                    qset
                    tset
                    others
                    i
                    (list 'relate pp qp ins in out '#:oracle oracle)))
           (values (list p2 data) q2)]
          [((list) #f (or 'non-constructive #f))
           (unless (andmap (lambda (x) (not (second x))) others)
             (error
              'test
              (string-append "VERY BAD: programs were ~a\n"
                             "~a\n"
                             "others: ~a\n"
                             "under ~a\nThe original call was ~a\n"
                             extras)
              p
              q
              others
              i
              (list 'relate pp qp ins in out '#:oracle oracle)))
           (values #f #f)]
          [(done paused t)
           (error 'test
                  (string-append "VERY BAD: inconsistent output states:\n programs were ~a -> ~a\n"
                                 "~a -> ~a\n"
                                 "exec : ~a\n"
                                 "others: ~a\n"
                                 "under ~a\nThe original call was ~a\n"
                                 extras)
                  p
                  done
                  q
                  paused
                  i
                  others
                  oracle
                  (list 'relate pp qp ins in out '#:oracle oracle))]))))
  #t)

(define (cos:done? p)
  (redex-match? cos:esterel-eval p (first p)))

(define (standard:done? q)
  (or (redex-match? standard:esterel-standard nothing q)
      (redex-match? standard:esterel-standard (ρ θ A nothing) q)))



(define (calc-shuffle p [times 10])
  (define-values (app p*)
    (for/fold ([applied empty] [p p])
              ([i (in-range times)])
      (define-values (t p-next) (apply-reduction-relation/pick ⟶ p))
      (values (cons (list t p-next) applied)
              p-next)))
  (values p* (format "calculus equasions applied: ~a\n" (reverse app))))

(define (apply-reduction-relation/pick R p)
  (match (apply-reduction-relation/tag-with-names R p)
    [(list) (values #f p)]
    [(list* r)
     (match-define (list tag p) (random-ref r))
     (values tag p)]))

(define (generate-all-instants prog signals)
  (define progs
    (reverse
     (for/fold ([prog (list prog)])
               ([s signals]
                #:break (not (first prog)))
       (define x `(instant ,(first prog) ,s))
       (cons
        (and x (first x))
        prog))))
  (for/list ([p progs]
             [s signals])
    (list p s)))


;                                                         
;                                                         
;                                                         
;                                                         
;   ;;;;;;;;;                                             
;       ;                               ;                 
;       ;                               ;                 
;       ;         ;;;;      ;;;;;    ;;;;;;;      ;;;;;   
;       ;       ;;   ;;    ;;   ;;      ;        ;;   ;;  
;       ;       ;     ;    ;            ;        ;        
;       ;       ;     ;    ;;           ;        ;;       
;       ;      ;;;;;;;;     ;;;;        ;         ;;;;    
;       ;      ;;             ;;;       ;           ;;;   
;       ;       ;               ;;      ;             ;;  
;       ;       ;;              ;;      ;             ;;  
;       ;       ;;;  ;;    ;;  ;;;      ;;  ;    ;;  ;;;  
;       ;         ;;;;    ; ;;;;         ;;;;   ; ;;;;    
;                                                         
;                                                         
;                                                         
;                                                         
;                                                         


(module+ test
  (test-case "negative tests"
    ;; negative tests to make sure the test harness is working
    (check-exn
     #rx"programs were <terminated>.*exec: #<set: S>"
     (lambda ()
       (test-reduction
        `nothing
        '() '() '(() ())
        #:limits? #f
        #:memory-limits? #f
        #:oracle '(() (S)))))
    (check-exn
     #rx"programs were (?!<terminated>).*exec: #<set: S>"
     (lambda ()
       (test-reduction
        `(loop pause)
        '() '() '(() ())
        #:limits? #f
        #:memory-limits? #f
        #:oracle '(() (S)))))
    (check-exn
     #rx"programs were (?!<terminated>)"
     (lambda ()
       (relate (list '(loop pause) '())
               '(ρ {(sig S unknown) ·} GO (emit S))
               '(())
               '()
               '(S))))
    (check-exn
     #rx"inconsistent output states"
     (lambda ()
       (relate (list '(loop nothing) '())
               '(ρ · GO (loop pause))
               '(())
               '()
               '(S))))
    (check-exn
     #rx"VERY BAD"
     (lambda ()
       (test-reduction #:limits? #f
                       #:memory-limits? #f
                       #:other-sequences (list (list 'circuit (list (set 'S))))
                       `nothing
                       `() `() `(()))))
    (check-exn
     #rx"VERY BAD"
     (lambda ()
       (test-reduction #:limits? #f
                       #:memory-limits? #f
                       #:other-sequences (list (list 'circuit (list 'done)))
                       `nothing
                       `() `() `(()))))
    (check-exn
     #rx"VERY BAD"
     (lambda ()
       (test-reduction #:limits? #f
                       #:memory-limits? #f
                       #:other-sequences (list (list 'circuit (list #f)))
                       `nothing
                       `() `() `(())))))
  
  
  (test-begin
    (check-equal?
     ;; absence
     (apply-reduction-relation
      standard:R
      `(ρ ((sig SS present) ((sig SA unknown) ·)) GO
          (par (suspend (seq pause nothing) SS)
               (present SA pause pause))))
     (list
      `(ρ ((sig SA absent) ((sig SS present) ·))
          GO
          (par (suspend (seq pause nothing) SS)
               (present SA pause pause)))))
    (check-equal?
     ;; raise-shared
     (apply-reduction-relation
      standard:R
      `(ρ · GO (shared ss := (+) pause)))
     (list `(ρ · GO (ρ ((shar ss 0 old) ·) WAIT pause))))

    (check-equal?
     (apply-reduction-relation*
      standard:R
      `(ρ · GO
          (seq (shared s1 := (+) (var x1 := (+ s1) nothing))
               (ρ ((shar s1 0 old) ·) WAIT (<= s1 (+))))))
     (list `(ρ ((shar s1 0 ready) ((var· x1 0) ·)) GO nothing)))
    
    (check-equal?
     ;; merge
     (apply-reduction-relation
      standard:R
      `(ρ · GO (ρ ((shar ss 1 new) ·) WAIT pause)))
     (list `(ρ ((shar ss 1 new) ·) GO pause)))
    (check-equal?
     ;; merge
     (apply-reduction-relation
      standard:R
      `(ρ ((shar ss 2 old) ·) GO (ρ ((shar ss 1 new) ·) WAIT pause)))
     (list `(ρ ((shar ss 1 new) ·) GO pause)))
    (check-equal?
     ;; set-old
     (apply-reduction-relation
      standard:R
      `(ρ ((shar ss 1 old) ·) GO (<= ss (+ 5))))
     (list `(ρ ((shar ss 5 new) ·) GO nothing)))

    (check-equal?
     ;; set-new
     (apply-reduction-relation
      standard:R
      `(ρ ((shar ss 1 new) ·) GO (<= ss (+ 5))))
     (list `(ρ ((shar ss 6 new) ·) GO nothing)))

    (check-equal?
     ;; readyness
     (apply-reduction-relation
      standard:R
      `(ρ ((shar ss 1 new) ·) GO (shared s2 := (+ ss) pause)))
     (list `(ρ ((shar ss 1 ready) ·) GO (shared s2 := (+ ss) pause))))

    (check-equal?
     ;; raise-shared
     (apply-reduction-relation
      standard:R
      `(ρ ((shar ss 1 ready) ·) GO (shared s2 := (+ ss) pause)))
     (list `(ρ ((shar ss 1 ready) ·) GO (ρ ((shar s2 1 old) ·) WAIT pause))))
    (check-equal?
     ;; raise-shared
     (apply-reduction-relation
      standard:R
      `(ρ ((shar ss 1 ready) ·) GO (shared s2 := (+ 1) pause)))
     (list `(ρ ((shar ss 1 ready) ·) GO (ρ ((shar s2 1 old) ·) WAIT pause))))


    (check-equal?
     ;; raise-shared
     (apply-reduction-relation
      standard:R
      `(ρ · GO
          (shared s2 := (+ 1 0)
                  pause)))
     (list `(ρ · GO
               (ρ ((shar s2 1 old) ·)
                  WAIT
                  pause))))

    (check-equal?
     ;; par-right
     (apply-reduction-relation
      standard:R
      `(ρ · GO (seq (par (exit 3) (seq pause nothing)) nothing)))
     (list `(ρ · GO (seq (exit 3) nothing))))

    (check-equal?
     ;; par-left
     (apply-reduction-relation
      standard:R
      `(ρ · GO (par nothing (par (seq pause nothing) nothing))))
     (list `(ρ · GO (par nothing (seq pause nothing)))))

    (check-equal?
     ;; is-present
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S present) ·) GO (present S nothing pause)))
     (list `(ρ ((sig S present) ·) GO nothing)))

    (check-equal?
     ;; is-absent
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S absent) ·) GO (par (seq (present S nothing pause) nothing)
                                  nothing)))
     (list `(ρ ((sig S absent) ·) GO (par (seq pause nothing) nothing))))

    (check-equal?
     ;; emit unknown
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S unknown) ·) GO (trap (emit S))))
     (list `(ρ ((sig S present) ·) GO (trap nothing))))

    (check-equal?
     ;; emit present
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S present) ·) GO (trap (emit S))))
     (list `(ρ ((sig S present) ·) GO (trap nothing))))

    (check-equal?
     ;; loop
     (apply-reduction-relation
      standard:R
      `(ρ · GO (trap (loop pause))))
     (list `(ρ
             · GO
             (trap
              (loop^stop
               pause
               pause)))))

    (check-equal?
     ;; seq-done
     (apply-reduction-relation
      standard:R
      `(ρ · GO (suspend (suspend (seq nothing (par (exit 33) (exit 44))) S1) S2)))
     (list `(ρ · GO (suspend (suspend (par (exit 33) (exit 44)) S1) S2))))

    (check-equal?
     ;; seq-exit
     (apply-reduction-relation
      standard:R
      `(ρ · GO (suspend (suspend (seq (exit 55) (par (exit 33) (exit 44))) S1) S2)))
     (list `(ρ · GO (suspend (suspend (exit 55) S1) S2))))

    (check-equal?
     ;; suspend
     (apply-reduction-relation
      standard:R
      `(ρ · GO (seq (suspend (suspend nothing S) S) (emit S2))))
     (list `(ρ · GO (seq (suspend nothing S) (emit S2)))))

    (check-equal?
     ;; trap
     (apply-reduction-relation
      standard:R
      `(ρ · GO (trap (exit 0))))
     (list `(ρ · GO nothing)))

    (check-equal?
     ;; trap
     (apply-reduction-relation
      standard:R
      `(ρ · GO (trap (exit 1))))
     (list `(ρ · GO (exit 0))))

    (check-equal?
     ;; trap
     (apply-reduction-relation
      standard:R
      `(ρ · GO (trap (exit 11))))
     (list `(ρ · GO (exit 10))))

    (check-equal?
     ;; trap
     (apply-reduction-relation
      standard:R
      `(ρ · GO (trap nothing)))
     (list `(ρ · GO nothing)))

    (check-equal?
     ;; trap
     (apply-reduction-relation
      standard:R
      `(ρ · GO (trap pause)))
     ;; no reductions
     (list))

    (check-equal?
     ;; signal
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S absent) ·) GO (trap (signal S2 (emit S2)))))
     (list `(ρ ((sig S absent) ·) GO (trap (ρ ((sig S2 unknown) ·) WAIT (emit S2))))))

    (check-equal?
     ;; raise-var
     (apply-reduction-relation
      standard:R
      `(ρ · GO (seq (var x := (+ 0) (if x pause nothing)) nothing)))
     (list `(ρ · GO (seq (ρ ((var· x 0) ·) WAIT (if x pause nothing)) nothing))))

    (check-equal?
     ;; set-var
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S absent) ((var· x 0) ((sig S2 present) ·)))
           GO
          (trap (:= x (+ x 2)))))
     (list `(ρ ((sig S absent) ((sig S2 present) ((var· x 2) ·)))
                GO
               (trap nothing))))
    (check-equal?
     ;; set-var
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S absent) ((var· x 2) ((sig S2 present) ·)))
           GO
          (trap (:= x (dec x)))))
     (list `(ρ ((sig S absent) ((sig S2 present) ((var· x 1) ·)))
               GO
               (trap nothing))))
    (check-equal?
     ;; set-var
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S absent) ((var· x 0) ((sig S2 present) ·)))
          GO
          (trap (:= x (dec x)))))
     (list `(ρ ((sig S absent) ((sig S2 present) ((var· x 0) ·)))
               GO
               (trap nothing))))
    (check-equal?
     ;; set-var
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S absent) ((var· x 0) ((sig S2 present) ·)))
          GO
          (:= x (+ s 2))))
     ;; doesn't reduce because `s` isn't in the environment
     (list))

    (check-equal?
     ;; if-false
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S absent) ((var· x 0) ((sig S2 present) ·)))
          GO
          (trap (par (suspend (if x pause nothing) S3)
                     (suspend (if x pause nothing) S4)))))
     (list `(ρ
             ((sig S absent) ((var· x 0) ((sig S2 present) ·)))
             GO
             (trap (par (suspend nothing S3) (suspend (if x pause nothing) S4))))))

    (check-equal?
     ;; if-false
     (apply-reduction-relation
      standard:R
      `(ρ ((var· x (rvalue #f)) ·) GO (if x pause nothing)))
     (list `(ρ ((var· x (rvalue #f)) ·) GO nothing)))

    (check-equal?
     ;; if-true
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S absent) ((var· x 1232) ((sig S2 present) ·)))
          GO
          (trap (par (suspend (if x pause nothing) S3)
                     (suspend (if x pause nothing) S4)))))
     (list `(ρ
             ((sig S absent) ((var· x 1232) ((sig S2 present) ·)))
             GO
             (trap (par (suspend pause S3) (suspend (if x pause nothing) S4))))))

    (check-equal?
     ;; if-true
     (apply-reduction-relation
      standard:R
      `(ρ ((var· x (rvalue "this is some random thing that is not #f")) ·) GO (if x pause nothing)))
     (list `(ρ ((var· x (rvalue "this is some random thing that is not #f")) ·) GO pause)))

    (check-equal?
     ;; absence
     (apply-reduction-relation
      standard:R
      `(ρ ((sig S absent) ((var· x 1232) ((sig S2 unknown) ·)))
          GO
          (trap (par (suspend (present S2 nothing pause) S3)
                     (suspend pause S4)))))
     (list `(ρ ((sig S absent) ((sig S2 absent) ((var· x 1232) ·)))
               GO
               (trap (par (suspend (present S2 nothing pause) S3) (suspend pause S4))))))



    
    (check-true
     (test-reduction `(signal Srandom-signal14877
                              (seq (par nothing (suspend pause Srandom-signal14877)) (emit Srandom-signal14877)))
                     `(Sz Sh SJ Sv)
                     `(Sf Sg Sy Sw SS SE So Si)
                     `(() () () () () () () () () () () () () () () () () () ())
                     #:limits? #f
                     #:memory-limits? #f))
    (check-true
     (test-reduction `(signal SS
                        (trap
                         (seq
                          (par (present SS (exit 0) (seq (emit SO) nothing))
                               nothing)
                          (emit SS))))
                     `()
                     `(SO)
                     `(())
                     #:limits? #f
                     #:memory-limits? #f))
    (check-true
     (test-reduction (quasiquote (seq (trap (par (exit 0) pause)) (emit SrX)))
                     (quasiquote (Sx SQ Sb))
                     (quasiquote (SUU SrX SD |S,| SrF Sd))
                     (quasiquote ((Sb SQ)))
                     #:limits? #f
                     #:memory-limits? #f))
    (check-equal?
     1
     (length
      (apply-reduction-relation*
       standard:R
       `(ρ ((sig SE present)
            ((sig SC unknown)
             ((sig SdB unknown)
              ((sig SEW unknown)
               ((sig Sb unknown)
                ((sig S- unknown)
                 ((sig SDI unknown) ·)))))))
           GO
           (seq (par nothing
                     (trap (par (trap (suspend (seq (present SE pause nothing) nothing) SE)) nothing)))
                (loop
                      (present SC
                               (par pause
                                    (trap (par (trap (suspend pause SE))
                                               pause)))
                               (par
                                (par
                                 (par pause nothing)
                                 (seq pause pause))
                                (emit S-)))))))))
    (check-equal?
     (apply-reduction-relation*
      standard:R
      `(ρ
        ((var· x 1) ·)
        GO
        (seq
         (seq nothing (:= x (+ x)))
         (loop (var x := (+ 0) (seq (:= x (+ 1)) (seq pause (:= x (+ x)))))))))
     `((ρ
        ((var· x 1)
           ·)
        GO
        (loop^stop
         (seq pause (:= x (+ x)))
         (var x := (+ 0) (seq (:= x (+ 1)) (seq pause (:= x (+ x)))))))))
    (check-true
     (test-reduction #:limits? #f
                     #:memory-limits? #f
                     `(signal S
                              (seq
                               (present S nothing nothing)
                               (seq
                                (loop
                                      (var x := (+ 0);;false
                                           (if x
                                               nothing
                                               pause)))
                                (emit S))))
                     `() `() `(() () () () () () () () () () () ())))

    (check-not-false
     (test-reduction
      (term
       (var x := (+ 2)
            (seq (seq (if x nothing (emit SO))
                      pause)
                 (seq (:= x (+ 0))
                      (if x nothing (emit SO))))))
      '()
      '(SO)
      '(() ())
      #:limits? #f 
      #:memory-limits? #f
      #:debug? #f
      #:oracle '(() (SO))))
    (test-case "example discovered during investigation of circuits"
      (check-not-false
       (execute-test
        (term
         (loop (trap (seq pause (seq (emit S) (exit 0))))))
        '()
        '(S)
        '(() () () ())
        #:limits? #f 
        #:memory-limits? #f
        #:debug? #f
        #:external? #t)))
        

    (check-not-false
     (execute-test
      (term
       (var x := (+ 2)
            (seq (seq (if x nothing (emit SO))
                      pause)
                 (seq (:= x (+ 0))
                      (if x nothing (emit SO))))))
      '()
      '(SO)
      '(() ())
      #:limits? #f 
      #:memory-limits? #f
      #:debug? #f
      #:external? #t))
    (check-not-false
     (execute-test
      '(signal SC (seq (present SC nothing nothing) (signal Si (present Si (emit SC) nothing))))
      '()
      '()
      '(()) #:debug? #f #:external? #t #:limits? #f
      #:memory-limits? #f))
    (check-not-false
     (execute-test
      '(signal SC (signal Si (seq (present SC nothing nothing) (present Si (emit SC) nothing))))
      '()
      '()
      '(()) #:debug? #f #:external? #t #:limits? #f
      #:memory-limits? #f))
    (check-not-false
     (execute-test
      '(signal SC
               (seq (present SC nothing nothing)
                    (signal Si
                            (seq (present SC nothing nothing)
                                 (present Si (emit SC) nothing)))))
      '()
      '()
      '(()) #:debug? #f #:external? #t #:limits? #f
      #:memory-limits? #f))

    ;; adapted from  The constructive semantics of pure Esterel, page 138
    (check-not-false
     (test-reduction
      (term
       (loop
        (trap
         (signal
          S1
          (par
           (seq pause (seq (emit S1) (exit 0)))
           (loop
            (trap
             (signal
              S2
              (par
               (seq pause (seq (emit S2) (exit 0)))
               (loop
                (seq (present S1
                              (present S2 (emit S1_and_S2) (emit S1_and_not_S2))
                              (present S2 (emit Snot_S1_and_S2) (emit Snot_S1_and_not_S2)))
                     pause)))))))))))
      '()
      '(S1_and_S2 S1_and_not_S2 Snot_S1_and_S2 Snot_S1_and_not_S2)
      '(() ())
      #:limits? #f #:debug? #f
      #:memory-limits? #f
      #:oracle
      '((Snot_S1_and_not_S2) (S1_and_S2 S1_and_not_S2 Snot_S1_and_not_S2))))

    (execute-test
     (term (signal
            S5
            (seq
             (seq
              (trap (present S5 nothing (exit 0)))
              pause)
             (emit S5))))
     '()
     '()
     '(() () () () () () () () () () () () ())
     #:limits? #f #:debug? #f #:external? #t
     #:memory-limits? #f)

    (execute-test
     (term (signal
            S5
            (seq
             (seq
              (trap (present S5 nothing (exit 0)))
              (seq pause nothing))
             (emit S5))))
     '()
     '()
     '(() () () () () () () () () () () () ())
     #:limits? #f #:debug? #f #:external? #t
     #:memory-limits? #f)

    (check-not-false
     (execute-test
      (term
       (loop
        (trap
         (signal
          Sa
          (par
           (seq pause (seq (emit Sa) (exit 0)))
           (loop
            (trap
             (signal
              Sb
              (par
               (seq pause (seq (emit Sb) (exit 0)))
               (loop
                (seq (present Sa
                              (present Sb (emit Sa_and_Sb) (emit Sa_and_not_Sb))
                              (present Sb (emit Snot_Sa_and_Sb) (emit Snot_Sa_and_not_Sb)))
                     pause)))))))))))
      '()
      '(Sa_and_Sb Sa_and_not_Sb Snot_Sa_and_Sb Snot_Sa_and_not_Sb)
      '(() ())
      #:limits? #f #:debug? #f
      #:memory-limits? #f
      #:external? #t))
    (check-true
     (execute-test
      `(seq (suspend pause SI) (emit SO))
      `(SI)
      `(SO)
      `((SI) (SI) (SI))
      #:limits? #f
      #:memory-limits? #f
      #:debug? #f
      #:external? #f))
    (execute-test '(signal
                    S1
                    (var
                     x
                     :=
                     (+)
                     (loop
                      (if x (emit S1) (present S1 nothing pause)))))
                  '()
                  '()
                  '(()) #:debug? #f #:limits? #t #:external? #f
                  #:memory-limits? #f)
    (execute-test '(signal
                    S
                    (seq (loop (present S nothing pause))
                         (emit S)))
                  '()
                  '()
                  '(()) #:debug? #f #:limits? #f #:external? #t
                  #:memory-limits? #f)

    (test-reduction
     `(shared s1
        :=
        (+ 19)
        (seq
         (<= s1 (+))
         (var x1 := (+ s1) (if x1 (emit SO) nothing))))
     `()
     `(SO)
     `(())
     #:limits? #f
     #:memory-limits? #f)
    (execute-test `(shared s1
                     :=
                     (+ 19)
                     (seq
                      (<= s1 (+))
                      (var x1 := (+ s1) (if x1 (emit SO) nothing))))
                  `()
                  `(SO)
                  `(())
                  #:debug? #f #:limits? #f #:external? #t
                  #:memory-limits? #f)
    (execute-test
     (term (signal S
             (loop (seq (emit S)
                        (seq (present SI pause nothing)
                             (seq (present S (emit ST) nothing)
                                  (present SI pause nothing)))))))
     '(SI)
     '(ST)
     '(() () () ())
     #:debug? #f #:limits? #f #:external? #t
                  #:memory-limits? #f)
    (execute-test
     (term (signal S
             (loop (seq (emit S)
                        (seq (present SI pause nothing)
                             (seq (present S (emit ST) nothing)
                                  (present SI pause nothing)))))))
     '(SI)
     '(ST)
     '((SI) (SI) (SI) (SI))
     #:debug? #f #:limits? #f #:external? #t
                  #:memory-limits? #f)
    (execute-test
     (term (signal S
             (loop (seq (emit S)
                        (seq (present SI pause nothing)
                             (seq (present S (emit ST) nothing)
                                  (present SI pause nothing)))))))
     '(SI)
     '(ST)
     '((SI) () (SI) ())
     #:debug? #f #:limits? #f #:external? #t
     #:memory-limits? #f)
    (execute-test
     (term (signal S
             (loop (seq (emit S)
                        (seq (present SI pause nothing)
                             (seq (present S (emit ST) nothing)
                                  (present SI pause nothing)))))))
     '(SI)
     '(ST)
     '(() (SI) () (SI))
     #:debug? #f #:limits? #f #:external? #t
     #:memory-limits? #f)

    (time
     (test-case "external"
       (do-test #:limits? #f #:count 100 #:external #t
                #:memory-limits? #f)))
    (test-case "random"
      (do-test #:limits? #f #:count 1000
               #:memory-limits? #f))))
