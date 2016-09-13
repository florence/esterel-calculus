#lang racket
(require redex/reduction-semantics "reduction.rkt" (except-in "shared.rkt" esterel-eval)
         ;(prefix-in calculus: "calculus.rkt")
         (only-in (submod esterel/cos-model test) cc->>)
         (prefix-in cos: esterel/cos-model)
         racket/sandbox
         rackunit
         racket/random
         (prefix-in r: racket))

(define-syntax quasiquote (make-rename-transformer #'term))

(define-union-language esterel-eval* esterel-eval (cos: cos:esterel-eval))
(define-metafunction esterel-eval*
  convert : p -> cos:p
  [(convert nothing) nothing]
  [(convert pause) pause]
  [(convert (seq p q))
   (seq (convert p) (convert q))]
  [(convert (signal S p))
   (signal S (convert p))]
  [(convert (par p q))
   (par (convert p) (convert q))]
  [(convert (loop p))
   (loop (convert p))]
  [(convert (present S p q))
   (present S (convert p) (convert q))]
  [(convert (emit S)) (emit S)]
  [(convert (suspend p S))
   (suspend (convert p) S)]
  [(convert (trap p))
   (trap (convert p))]
  [(convert (exit n))
   (exit (cos:to-nat ,(+ 2 `n)))]
  [(convert (shared s := e p))
   (shared s := e (convert p))]
  [(convert (<= s e)) (<= s e)]
  [(convert (var x := e p))
   (var x := e (convert p))]
  [(convert (:= x e)) (:= x e)]
  [(convert (if e p q))
   (if e (convert p) (convert q))])


(define-extended-language esterel-check esterel-eval*
  (p-check
   nothing
   pause
   (seq p-check p-check)
   (par p-check p-check)
   (trap p-check)
   (exit n)
   (signal S p-check)
   (suspend p-check S)
   (present S p-check p-check)
   (emit S)
   (loop p-check-pause)
   (shared s := e-check p-check)
   (<= s e-check)
   (var x := e-check p-check)
   (:= x e-check)
   (if x p-check p-check))
  (p-check-pause
   pause
   (seq p-check-pause p-check)
   ;(seq p-check-pause p-check-pause)
   (seq p-check p-check-pause)
   (par p-check-pause p-check)
   (par p-check p-check-pause)
   ;(par p-check-pause p-check-pause)
   (seq (trap p-check-pause) pause)
   (seq pause (trap p-check-pause))
   (par pause (trap p-check-pause))
   (par (trap p-check-pause) pause)
   (signal S p-check-pause)
   (suspend p-check-pause S)
   (present S p-check-pause p-check-pause)
   (loop p-check-pause)
   (shared s := e-check p-check-pause)
   (var x := e-check p-check-pause)
   (if x p-check-pause p-check-pause))


  (e-check ::= s x (+ e-check ...) n))

(define (relate pp qp ins in out #:limits? [limits? #f] #:debug? [debug? #f])
  (define (remove-not-outs l)
    (filter (lambda (x) (member x out)) l))
  (for/fold ([p pp]
             [q qp]
             #;
             [qc qp])
            ([i (in-list ins)]
             #:break (or
                      (not p)
                      (not p)
                      (and
                       (redex-match cos:esterel-eval p (first p))
                       (redex-match esterel-eval (in-hole A nothing) q))))
    (when debug?
      (printf "running:\np:")
      (pretty-print pp)
      (printf "q:")
      (pretty-print qp)
      (printf "i:")
      (pretty-print i))
    (with-handlers ([(lambda (x) (and (exn:fail:resource? x)
                                      (eq? 'time (exn:fail:resource-resource x))))
                     (lambda (_) (values #f #f))])
      (with-limits (and limits? (r:* 10 60)) #f
        (when debug?
          (printf "running instant\n")
          (pretty-print (list 'instant q i)))
        (define new-reduction `(instant ,q ,(setup-r-env i in)))
        ;(define calc-reduction `(calculus:instant ,q ,(setup-r-env i in)))
        (when debug?
          (printf "running c->>\n")
          (pretty-print
           (list 'c->> `(machine ,(first p) ,(second p))
                 (setup-*-env i in)
                 '(machine pbar data_*) '(S ...) 'k)))
        (define constructive-reduction
          (judgment-holds
           (cos:c->> (machine ,(first p) ,(second p))
                     ,(setup-*-env i in)
                     (machine pbar data_*) (S ...) k)
           (pbar data_* (S ...))))
        ;; TODO finish testing calculus
        (match* (constructive-reduction new-reduction)
          [(`((,p2 ,data ,(and pouts (list-no-order b ...)))
              (,_ ,_ ,(list-no-order b ...)) ...)
            (list q2 qouts))
           (unless #;(judgment-holds (~ (,p2 ,pouts) ,a ,out))
             (equal? (list->set (remove-not-outs pouts))
                     (list->set (remove-not-outs qouts)))
             (error 'test
                    "programs were ~a -> (~a ~a)\n ~a -> ~a\n under ~a\nThe origional call was ~a"
                    p
                    p2
                    pouts
                    q
                    q2
                    i
                    (list 'relate pp qp ins in out)))
           (values (list p2 data) q2)]
          [((list) #f)
           (values #f #f)]
          [(v v*)
           (error 'test
                  "inconsitent output states:\n programs were ~a -> ~a\n ~a -> ~a\n under ~a\nThe origional call was ~a"
                  p
                  v
                  q
                  v*
                  i
                  (list 'relate pp qp ins in out))]))))
  #t)

(define (setup-*-env ins in)
  (for/list ([i in])
    (if (member i ins)
        `(,i (Succ zero))
        `(,i zero))))

(define (setup-r-env ins in)
  (for/list ([i in])
    (if (member i ins)
        `(sig ,i present)
        `(sig ,i absent))))

(define (fixup e)
  (redex-let
   esterel
   ([(p (S_i ...) (S_o ...) ((S ...) ...)) e])
   (let ()
     (define low-signals? (< (random) 1/8))
     (define signals (build-list (add1 (random 2)) (lambda (_) (gensym 'random-signal))))
     (define shareds (build-list (add1 (random 2)) (lambda (_) (gensym 'random-shared))))
     (define SI (remove-duplicates `(S_i ...)))
     (define SO (remove-duplicates `(S_o ...)))
     (define (wrap p signals shareds)
       (match* (signals shareds)
         [((cons s r) _)
          `(signal ,s ,(wrap p r shareds))]
         [(n (cons s r))
          `(shared ,s := 0 ,(wrap p n r))]
         [(_ _) p]))
     (if low-signals?
         (list
          (wrap
           `(fix/low-signals p
                             ,signals
                             ,shareds
                             ()
                             0)
           signals
           shareds)
          SI
          SO
          `(generate-inputs ()))
         (list
          `(fix p ,SI ,SO () () () 0)
          SI
          SO
          `(generate-inputs ,SI))))))

(define-metafunction esterel-eval
  fix/low-signals : p (S ...) (s ...) (x ...) n -> p
  [(fix/low-signals nothing (S ...) (s ...) (x ...) n)
   nothing]
  [(fix/low-signals pause (S ...) (s ...) (x ...) n)
   pause]
  [(fix/low-signals (exit n) (S ...) (s ...) (x ...) n_max)
   ,(if (zero? `n_max)
        `nothing
        `(exit ,(random `n_max)))]
  [(fix/low-signals (emit any) (S ...) (s ...) (x ...) n_max)
   (emit ,(random-ref `(S ...)))]
  [(fix/low-signals (signal any p) (S ...) (s ...) (x ...) n_max)
   (fix/low-signals p (S ...) (s ...) (x ...) n_max)]
  [(fix/low-signals (present any p q) (S ...) (s ...) (x ...) n_max)
   (present ,(random-ref `(S ...))
            (fix/low-signals p (S ...) (s ...) (x ...) n_max)
            (fix/low-signals q (S ...) (s ...) (x ...) n_max))]
  [(fix/low-signals (par p q) (S ...) (s ...) (x ...) n_max)
   (par
    (fix/low-signals p (S ...) (s ...) (x ...) n_max)
    (fix/low-signals q (S ...) (s ...) (x ...) n_max))]
  [(fix/low-signals (seq p q) (S ...) (s ...) (x ...) n_max)
   (seq
    (fix/low-signals p (S ...) (s ...) (x ...) n_max)
    (fix/low-signals q (S ...) (s ...) (x ...) n_max))]
  [(fix/low-signals (loop p) (S ...) (s ...) (x ...) n_max)
   (loop
    (fix/low-signals p (S ...) (s ...) (x ...) n_max))]
  [(fix/low-signals (suspend p any) (S ...) (s ...) (x ...) n_max)
   (suspend
    (fix/low-signals p (S ...) (s ...) (x ...) n_max)
    ,(random-ref `(S ...)))]
  [(fix/low-signals (trap p) (S ...) (s ...) (x ...) n_max)
   (trap
    (fix/low-signals p (S ...) (s ...) (x ...) ,(add1 `n_max)))]
  [(fix/low-signals (shared s_d := e p) (S ...) (s ...) (x ...) n_max)
   (fix/low-signals p (S ...) (s ...) (x ...) n_max)]
  [(fix/low-signals (<= s_d e) (S ...) (s ...) (x ...) n_max)
   (<= ,(random-ref `(s ...)) (fix/e e (s ... x ...)))]
  [(fix/low-signals (var x_d := e p) (S ...) (s ...) (x ...) n_max)
   (var x_n := (fix/e e (s ... x ...))
        (fix/low-signals p (S ...) (s ...) (x_n x ...) n_max))
   (where x_n ,(gensym 'random-var))]
  [(fix/low-signals (:= x_d e) (S ...) (s ...) (x ...) n_max)
   ,(if (null? `(x ...))
        `nothing
        `(:= ,(random-ref `(x ...))
             (fix/e e (s ... x ...))))]
  [(fix/low-signals (if e p q) (S ...) (s ...) (x ...) n_max)
   ,(if (null? `(x ...))
        `(fix/low-signals p (S ...) (s ...) (x ...) n_max)
        `(if
          (fix/e e (x ...))
          (fix/low-signals p (S ...) (s ...) (x ...) n_max)
          (fix/low-signals q (S ...) (s ...) (x ...) n_max)))])

(define-metafunction esterel-eval
  fix : p (S ...) (S ...) (S ...) (s ...) (x ...) n -> p
  [(fix nothing (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   nothing]
  [(fix pause (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   pause]
  [(fix (exit n) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   ,(if (zero? `n_max)
        `nothing
        `(exit ,(random `n_max)))]
  [(fix (emit S) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (emit ,(random-ref `(S_o ... S_b ...)))]
  [(fix (signal S_d p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (signal S (fix p (S_i ...) (S_o ...) (S S_b ...) (s ...) (x ...) n_max))
   (where S ,(gensym))
   (where #t ,(<= (length `(S_b ...)) 3))]
  [(fix (signal S_d p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (where #t ,(> (length `(S_b ...)) 3))]
  [(fix (present S p q) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (present ,(random-ref `(S_i ... S_b ...))
            (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
            (fix q (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max))]
  [(fix (par p q) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (par
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
    (fix q (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max))]
  [(fix (seq p q) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (seq
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
    (fix q (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max))]
  [(fix (loop p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (loop
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max))]
  [(fix (suspend p S) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (suspend
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
    ,(random-ref `(S_i ... S_b ...)))]
  [(fix (trap p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (trap
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) ,(add1 `n_max)))]
  [(fix (shared s_d := e p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (shared s_n := (fix/e e (s ... x ...))
           (fix p (S_i ...) (S_o ...) (S_b ...) (s_n s ...) (x ...) n_max))
   (where s_n ,(gensym))]
  [(fix (<= s_d e) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   ,(if (null? `(s ...))
        `nothing
        `(<= ,(random-ref `(s ...))
             (fix/e e (s ... x ...))))]

  [(fix (var x_d := e p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (var x_n := (fix/e e (s ... x ...))
        (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x_n x ...) n_max))
   (where x_n ,(gensym))]
  [(fix (:= x_d e) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   ,(if (null? `(x ...))
        `nothing
        `(:= ,(random-ref `(x ...))
             (fix/e e (s ... x ...))))]
  [(fix (if e p q) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   ,(if (null? `(x ...))
        `(fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
        `(if
          (fix/e e (x ...))
          (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
          (fix q (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)))])

(define-metafunction esterel-eval
  fix/e : e (s ...) -> e
  [(fix/e n (s ...)) n]
  [(fix/e s ()) 0]
  [(fix/e s (s_s ...)) ,(random-ref `(s_s ...))]
  [(fix/e (f e ...) (s ...))
   (f (fix/e e (s ...)) ...)])

(define-metafunction esterel-eval
  generate-inputs : (S ...) -> ((S ...) ...)
  [(generate-inputs (S ...))
   ,(for/list ([_ (random 20)])
      (random-sample `(S ...)
                     (random (add1 (length `(S ...))))
                     #:replacement? #f))])

(define-metafunction esterel-eval
  add-extra-syms : p (S ...) -> p
  [(add-extra-syms p (S ...))
   (env ((sig S unknown) ...)
        ,(for/fold ([p `p])
                   ([S (in-list `(S ...))])
           `(substitute* ,p ,S (sig ,S unknown))))])

(provide do-test)
(define (do-test [print #f] #:limits? [limits? #f])
  (redex-check
   esterel-check
   (p-check (name i (S_!_g S_!_g ...)) (name o (S_!_g S_!_g ...)) ((S ...) ...))
   ;#:ad-hoc
   (redex-let
    esterel-eval
    ([(S_i ...) `i]
     [(S_o ...) `o])
    (begin
      (when print
        (displayln (list `~f ``p-check ``i ``o ``((S ...) ...) '#:limits? limits?))
        #;
        (displayln `(p-check in: i out: o instants: ((S ...) ...)))))
    (~f `p-check `i `o `((S ...) ...) #:limits? limits?)
    #;
    (relate `((convert p-check) ())
            `(add-extra-syms p-check ,(append `i `o))
            `((S ...) ...)
            `(S_i ...)
            `(S_o ...)
            #:limits? limits?))
   #:prepare fixup
   #:attempts 10000))

(provide ~f)
(define (~f p-check i o s #:limits? limits? #:debug? [debug? #f])
  (relate `((convert ,p-check) ())
          `(add-extra-syms ,p-check ,(append i o))
          s
          i
          o
          #:limits? limits?
          #:debug? debug?))

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

(test-begin
  (check-equal?
   (apply-reduction-relation
    R*
    `(env ((sig S present) (sig A unknown))
          (par (suspend^ nothing (sig S present))
               (present (sig A unknown) pause pause))))
   (list
    `(env ((sig S present) (sig A absent))
          (par (suspend^ nothing (sig S present))
               (present (sig A absent) pause pause)))))
  (check-true
   (redex-match?
    esterel-eval
    ((env ((shar s 1 new))
          pause))
    (apply-reduction-relation
     R*
     `(env ()
           (shared s := 1
                   pause)))))
  (check-true
   (redex-match?
    esterel-eval
    ((env ((shar s 5 new))
          nothing))
    (apply-reduction-relation
     R*
     `(env ((shar s 1 old))
           (<= s 5)))))

  (check-true
   (redex-match?
    esterel-eval
    ((env ((shar s 6 new))
          nothing))
    (apply-reduction-relation
     R*
     `(env ((shar s 1 new))
           (<= s 5)))))

  (check-true
   (redex-match?
    esterel-eval
    ((env ((shar s 1 ready))
          (shared s_2 := (shar s 1 ready)
                  pause)))
    (apply-reduction-relation
     R*
     `(env ((shar s 1 new))
           (shared s2 := (shar s 1 new)
                   pause)))))

  (check-true
   (redex-match?
    esterel-eval
    ((env ((shar s 1 ready))
          (shared s2 := 1
                  pause)))
    (apply-reduction-relation
     R*
     `(env ((shar s 1 ready))
           (shared s2 := (shar s 1 ready)
                   pause)))))

  (check-true
   (redex-match?
    esterel-eval
    ((env ()
          (shared s2 := 1
                  pause)))
    (apply-reduction-relation
     R*
     `(env ()
           (shared s2 := (+ 1 0)
                   pause)))))
  (check-true
   (~f `(signal random-signal14877
                (seq (par nothing (suspend pause random-signal14877)) (emit random-signal14877)))
       `(z h J v)
       `(f g y w S E o i)
       `(() () () () () () () () () () () () () () () () () () ())
       #:limits? #f))
  (check-equal?
   `(Can_K (trap (exit 0)))
   `(0))
  (check-equal?
   `(Can_K (trap (par (exit 0) pause)))
   `(0))
  (check-true
   (~f (quasiquote (seq (trap (par (exit 0) pause)) (emit rX)))
       (quasiquote (x Q b))
       (quasiquote (UU rX D |,| rF d))
       (quasiquote ((b Q)))
       #:limits? #f))
  (check-equal?
   1
   (length
    (apply-reduction-relation*
     R*
     `(substitute*
       (env ((sig E unknown) (sig C unknown) (sig dB unknown)
             (sig EW unknown) (sig b unknown) (sig - unknown)
             (sig DI unknown))
            (seq (par nothing
                      (trap (par (trap (suspend^ nothing (sig E unknown))) nothing)))
                 (loop
                  (present (sig C unknown)
                           (par pause
                                (trap (par (trap (suspend pause (sig E unknown)))
                                           pause)))
                           (par
                            (par
                             (par pause nothing)
                             (seq pause pause))
                            (emit (sig - unknown)))))))
       (sig E unknown) (sig E present)))))
  (check-equal?
   (apply-reduction-relation*
    R*
    `(env
     ((var· x 1))
     (seq
      (seq nothing (:= x (var· x 1)))
      (loop (var x := 0 (seq (:= x 1) (seq pause (:= x x))))))))
   `((env
       ((var· x 1))
       (seq
        (seq pause (:= x (var· x 1)))
        (loop (var x := 0 (seq (:= x 1) (seq pause (:= x x)))))))))
  (test-case "random"
    (do-test #t)))
