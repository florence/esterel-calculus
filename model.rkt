#lang debug racket
(require redex)
(require esterel/cos-model
         racket/random
         (prefix-in r: racket)
         rackunit
         racket/sandbox
         (only-in (submod esterel/cos-model test) cc->>)
         (prefix-in cos: esterel/cos-model))

(define-syntax quasiquote (make-rename-transformer #'term))


(define-language esterel
  ((p q)
   nothing
   (signal Sdat p)
   (present Sdat p q)
   (emit Sdat)
   (par p q)
   (loop p)
   pause
   pause^
   (seq p q)
   (suspend p Sdat)
   (trap p)
   (exit n))
  (Sdat ::= S)
  (S ::= variable-not-otherwise-mentioned)
  (n ::= natural))

(define-extended-language esterel-eval esterel
  (p q ::= .... (signal (Sdat ...) p))
  (status ::= present absent unknown)
  (dat ::= (S present) (S absent))
  (Sdat ::= .... dat)
  ;; list of evaluated exprers, lists of paused exprs, environment, emitted signals

  ;; values and answers
  (a ::= ap a*)
  (ap ::= (in-hole A vp))
  (a* ::= (in-hole A v*))
  (v ::= vp v*)
  (vp ::= nothing (exit n))
  (v* ::=
      pause
      (seq v* q)
      (par v* v*)
      (suspend (in-hole P pause^) (S present))
      (suspend v* Sdat)
      (trap v*))

  (A ::=
     (signal (Sdat ...) hole))
  (P* Q* ::= (in-hole A P))
  (P^* Q^* ::= (in-hole A P^))
  ;; evaluation contexts
  (P Q ::=
     hole
     (seq P q)
     (par P q)
     (par p Q)
     (suspend P Sdat)
     (trap P))
  (P^ Q^ ::=
      hole
      (seq P^ q)
      (par P^ q)
      (par p Q^)
      (trap P^)
      (suspend P^ (S absent))))

(define-metafunction esterel-eval
  substitute* : any S Sdat -> any
  [(substitute* (signal S p) S Sdat)
   (signal S p)]
  [(substitute* (any ...) S Sdat)
   ((substitute* any S Sdat) ...)]
  [(substitute* S S Sdat) Sdat]
  [(substitute* any S Sdat) any])

(define-metafunction esterel-eval
  set : any S Sdat -> any
  [(set (any ...) S Sdat)
   ((set any S Sdat) ...)]
  [(set S S Sdat) Sdat]
  [(set any S Sdat) any])

(define-extended-language wrn esterel-eval
  #:binding-forms
  (signal S p #:refers-to S))
(define-metafunction wrn
  alpha-rename : p -> p
  [(alpha-rename p)
   (substitute p ,(gensym) ,(gensym))])

(define-extended-language wrn* wrn
  #:binding-forms
  (S status) #:exports S
  (signal (Sdat ...) p #:refers-to (shadow Sdat ...)))


(define R
  ;; ASSUMPTIONS:
  ;; program is loop safe
  (reduction-relation
   esterel-eval #:domain p
   (--> (in-hole P* (par vp v)) (in-hole P* (value-max vp v))
        par-done-right)
   (--> (in-hole P* (par v vp)) (in-hole P* (value-max v vp))
        par-done-left)
   (--> (in-hole P* (present (S present) p q)) (in-hole P* p)
    is-present)
   (--> (in-hole P* (present (S absent) p q)) (in-hole P* q)
    is-absent)
   (-->
    (signal (Sdat_1 ... S Sdat_2 ...) (in-hole P (emit S)))
    (signal (Sdat_1 ... (S present) Sdat_2 ...)
            (substitute* (in-hole P nothing) S (S present)))
    emit-unknown)
   (-->
    (signal (Sdat_1 ... (S present) Sdat_2 ...) (in-hole P (emit (S present))))
    (signal (Sdat_1 ... (S present) Sdat_2 ...) (in-hole P nothing))
    emit-present)

   (-->
    (signal (Sdat_1 ... S Sdat_2 ...) p)
    (signal (Sdat_1 ... (S absent) Sdat_2 ...) (substitute* p S (S absent)))
    (where #t (∉ S (Can_S p)))
    ;; only here to make things run with decent speed
    (judgment-holds (stuck? p (S_1 ... S S_2 ...)))
    absence)

   (--> (in-hole P* (loop p)) (in-hole P* (seq p (loop p)))
    loop)
   (--> (in-hole P^* pause^) (in-hole P^* nothing)
        hatted-pause)
   (--> (in-hole P* (seq nothing q)) (in-hole P* q)
    seq-done)
   (--> (in-hole P* (seq (exit n) q)) (in-hole P* (exit n))
    seq-exit)
   (--> (in-hole P* (suspend vp Sdat)) (in-hole P* vp)
    suspend-value)
   ;; traps
   (--> (in-hole P* (trap vp)) (in-hole P* (harp vp))
        trap-done)
   ;; lifting signals
   (--> (signal (Sdat ...) (in-hole P (signal S p)))
        (signal (insert-signal S_* (Sdat ...)) (in-hole P_* p_*))
        (where (in-hole P_* (signal S_* p_*)) (alpha-rename (in-hole P (signal S p))))
        raise-signal)))

#;
(define-judgment-form esterel-eval
  #:mode (I* I O)
  #:contract (I* (p ((S ...) ...)) (p ((S ...) ...)))
  [(R p p_*)
   --------------
   (I* (p ((S ...) ...))
       (p_* ((S ...) ...)))]
  [--------------
   (I* (a ((S_i ...) (S ...) ...))
       ((setup (add-hats (clear-up-signals p)) (S_i ...))
        ((S ...) ...)))])
(define I*
  (reduction-relation
   esterel-eval
   #:domain (p ((S ...) ...))
   (--> (p ((S ...) ...))
        (p_* ((S ...) ...))
        (where (any ... p_* any ...)
               ,(apply-reduction-relation* R `p)))
   (--> (a ((S_i ...) (S ...) ...))
        ((setup (add-hats (clear-up-signals a)) (S_i ...))
         ((S ...) ...)))))

(define-metafunction esterel-eval
  harp : vp -> vp
  [(harp nothing) nothing]
  [(harp (exit 0)) nothing]
  [(harp (exit n)) (exit ,(sub1 `n))])

(define-metafunction esterel-eval
  insert-signal : S (Sdat ...) -> (Sdat ...)
  [(insert-signal S (Sdat ...))
   ,(sort
     `(S Sdat ...)
     symbol<?
     #:key (lambda (x) (if (cons? x) (first x) x)))])

(define-metafunction esterel-eval
  value-max : v v -> v
  [(value-max nothing v) v]
  [(value-max v nothing) v]
  [(value-max (exit n_1) (exit n_2)) (exit ,(max `n_1 `n_2))]
  [(value-max (exit n) v*) (exit n)]
  [(value-max v* (exit n)) (exit n)])

(define-judgment-form esterel-eval
  #:mode (stuck? I O)
  #:contract (stuck? p (S ...))
  [------------
   (stuck? v ())]

  [-----------
   (stuck? (present S p q) (S))]

  [(stuck? p (S ...))
   -----------
   (stuck? (seq p q) (S ...))]

  [(stuck? p (S_1 ...))
   (stuck? q (S_2 ...))
   -----------
   (stuck? (par p q) (S_1 ... S_2 ...))]

  [(stuck? p (S ...))
   ----------
   (stuck? (suspend p Sdat) (S ...))]

  [(stuck? p (S ...))
   ----------
   (stuck? (trap p) (S ...))]

  [(stuck? p (S ...))
   ----------
   (stuck? (signal (Sdat ...) p) (S ...))]

  [-----------
   (stuck? (suspend (in-hole P pause^) S) (S))])

(define-metafunction esterel-eval
  instant : p (S ...) -> (p (S ...)) or #f
  [(instant p (S ...))
   ((add-hats (clear-up-signals a))
    (get-signals a))
   (where (a a_r ...) ,(apply-reduction-relation* R `(setup p (S ...))))
   (where (#t ...) ,(map (lambda (x) (alpha-equivalent? wrn* `a x)) `(a_r ...)))]
  [(instant p (S ...))
   #f
   (where (p_* ...) ,(apply-reduction-relation* R `(setup p (S ...))))])

(define-metafunction esterel-eval
  setup : p (S ...) -> p
  [(setup p
          (S S_2 ...))
   (setup (set p S (S present))
          (S_2 ...))]
  [(setup p ()) p])

(define-metafunction esterel-eval
  get-signals : p -> (S ...)
  [(get-signals (signal ((S present) Sdat ...) p))
   (S S_r ...)
   (where (S_r ...) (get-signals (signal (Sdat ...) p)))]
  [(get-signals (signal (Sdat Sdat_r ...) p))
   (get-signals (signal (Sdat_r ...) p))]
  [(get-signals (signal () p))
   ()])

(define-metafunction esterel-eval
  add-hats : p -> p
  [(add-hats pause) pause^]
  [(add-hats pause^) pause^]
  [(add-hats nothing) nothing]
  [(add-hats (signal (S ...) p)) (signal (S ...) (add-hats p))]
  [(add-hats (seq p q)) (seq (add-hats p) q)]
  [(add-hats (par p q)) (par (add-hats p) (add-hats q))]
  [(add-hats (suspend p S)) (suspend (add-hats p) S)]
  [(add-hats (trap p)) (trap (add-hats p))])

(define-metafunction esterel-eval
  clear-up-signals : p -> p
  [(clear-up-signals (signal (Sdat ...) p))
   (signal (S ...) (clear-up-signals p))
   (where (S ...)
          ,(map (lambda (x) (if (list? x) (first x) x)) `(Sdat ...)))]
  [(clear-up-signals nothing) nothing]
  [(clear-up-signals pause) pause]
  [(clear-up-signals pause^) pause^]
  [(clear-up-signals (signal S p))
   (signal S (clear-up-signals p))]
  [(clear-up-signals (present (S status) p q))
   (present S (clear-up-signals p) (clear-up-signals q))]
  [(clear-up-signals (present S p q))
   (present S (clear-up-signals p) (clear-up-signals q))]
  [(clear-up-signals (emit (S status)))
   (emit S)]
  [(clear-up-signals (emit S))
   (emit S)]
  [(clear-up-signals (par p q))
   (par (clear-up-signals p) (clear-up-signals q))]
  [(clear-up-signals (seq p q))
   (seq (clear-up-signals p) (clear-up-signals q))]
  [(clear-up-signals (loop p))
   (loop (clear-up-signals p))]
  [(clear-up-signals (suspend p (S status)))
   (suspend (clear-up-signals p) S)]
  [(clear-up-signals (suspend p S))
   (suspend (clear-up-signals p) S)]
  [(clear-up-signals (trap p))
   (trap (clear-up-signals p))]
  [(clear-up-signals (exit n)) (exit n)])


(module+ traces
  (require redex)
  (define (highlight-done! sexp term-node [rec #t])
    #;
    (when rec
      (for ([t (term-node-parents term-node)])
        (highlight-done! (term-node-expr t) t #f)))
    (cond [(cons? (term-node-children term-node))
           "white"
           (term-node-set-color! term-node "white")]
          #;
          [(not (judgment-holds (contradiction? ,sexp)))
           "blue"
           #;
           (term-node-set-color! term-node "blue")]
          [else
           "pink"
           #;
           (term-node-set-color! term-node "pink")]))
  (define p
    `(signal
      K
      (signal
       O
       (signal
        S
        (par
         (par
          (present K (seq pause (emit S)) (emit O))
          (trap (seq (exit 0) (emit S))))
         (suspend (present S nothing (loop (seq (emit K) pause)))
                  O))))))

  #;
  (traces R p #:pred highlight-done!)
  (define pp `(instant ,p ()))
  (traces R (first pp) #:pred highlight-done!))

(module+ random-test

  (define-union-language esterel-eval* esterel-eval (cos: cos:esterel-eval))
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
     (loop p-check-pause))
    (p-check-pause
     pause
     (seq p-check-pause p-check)
     (seq p-check-pause p-check-pause)
     (seq p-check p-check-pause)
     (par p-check-pause p-check)
     (par p-check p-check-pause)
     (par p-check-pause p-check-pause)
     (seq (trap p-check-pause) pause)
     (seq pause (trap p-check-pause))
     (par pause (trap p-check-pause))
     (par (trap p-check-pause) pause)
     (signal S p-check-pause)
     (suspend p-check-pause S)
     (present S p-check-pause p-check-pause)
     (loop p-check-pause)))

  (define (relate pp qp ins in out)
    (define (remove-not-outs l)
      (filter (lambda (x) (member x out)) l))
    (for/fold ([p pp]
               [q qp])
              ([i (in-list ins)]
               #:break (or
                        (not p)
                        (not p)
                        (and
                         (redex-match cos:esterel-eval p (first p))
                         (redex-match esterel-eval (in-hole A nothing) q))))
      (with-handlers ([(lambda (x) (and (exn:fail:resource? x)
                                        (eq? 'time (exn:fail:resource-resource x))))
                       (lambda (_) (values #f #f))])
        (with-limits (r:* 10 60) #f
          (define new-reduction `(instant ,q ,i))
          (define constructive-reduction
            (judgment-holds
             (c->> (machine ,(first p) ,(second p))
                   ,(setup-*-env i in)
                   (machine pbar data_*) (S ...) k)
             (pbar data_* (S ...))))
          (match constructive-reduction
            [`((,p2 ,data ,(and pouts (list-no-order a ...)))
               (,_ ,_ ,(list-no-order a ...)) ...)
             (match-define (list q2 qouts) new-reduction)
             (unless (equal? (list->set (remove-not-outs pouts))
                             (list->set (remove-not-outs qouts)))
               (error 'test
                      "programs were ~a -> ~a\n ~a -> ~a\n under ~a\nThe origional call was ~a"
                      p
                      (list->set (remove-not-outs pouts))
                      q
                      (list->set (remove-not-outs qouts))
                      i
                      (list 'relate pp qp ins in out)))
             (values (list p2 data) q2)]
            [v
             (match new-reduction
               ;; both stuck, is fine
               [#f (values #f #f)]
               [v*
                (error 'test
                       "inconsitent output states:\n programs were ~a -> ~a\n ~a -> ~a\n under ~a\nThe origional call was ~a"
                       p
                       v
                       q
                       v*
                       i
                       (list 'relate pp qp ins in out))])]))))
    #t)

  (define (setup-*-env ins in)
    (for/list ([i in])
      (if (member i ins)
          `(,i one)
          `(,i zero))))

  (define (fixup e)
    (redex-let
     esterel
     ([(p (S_i ...) (S_o ...) ((S ...) ...)) e])
     (let ()
       (define SI (remove-duplicates `(S_i ...)))
       (define SO (remove-duplicates `(S_o ...)))
       (list
        `(fix p ,SI ,SO)
        SI
        SO
        `(generate-inputs ,SI)))))


  (define-metafunction esterel-eval
    ;fix : p (S ...) (S ...) [trap-depth 0] -> p
    [(fix p (S_i ...) (S_o ...))
     (fix p (S_i ...) (S_o ...) () 0)]

    [(fix nothing (S_i ...) (S_o ...) (S_b ...) n_max)
     nothing]
    [(fix pause (S_i ...) (S_o ...) (S_b ...) n_max)
     pause]
    [(fix (exit n) (S_i ...) (S_o ...) (S_b ...) n_max)
     ,(if (zero? `n_max)
          `nothing
          `(exit ,(random `n_max)))]
    [(fix (emit S) (S_i ...) (S_o ...) (S_b ...) n_max)
     (emit ,(random-ref `(S_o ... S_b ...)))]

    [(fix (emit S) (S_i ...) (S_o ...) (S_b ...) n_max)
     (emit ,(random-ref `(S_o ... S_b ...)))]
    [(fix (signal S_d p) (S_i ...) (S_o ...) (S_b ...) n_max)
     (signal S (fix p (S_i ...) (S_o ...) (S S_b ...) n_max))
     (where S ,(gensym))
     (where #t ,(<= (length `(S_b ...)) 3))]
    [(fix (signal S_d p) (S_i ...) (S_o ...) (S_b ...) n_max)
     (fix p (S_i ...) (S_o ...) (S_b ...) n_max)
     (where #t ,(> (length `(S_b ...)) 3))]
    [(fix (present S p q) (S_i ...) (S_o ...) (S_b ...) n_max)
     (present ,(random-ref `(S_i ... S_b ...))
              (fix p (S_i ...) (S_o ...) (S_b ...) n_max)
              (fix q (S_i ...) (S_o ...) (S_b ...) n_max))]
    [(fix (par p q) (S_i ...) (S_o ...) (S_b ...) n_max)
     (par
      (fix p (S_i ...) (S_o ...) (S_b ...) n_max)
      (fix q (S_i ...) (S_o ...) (S_b ...) n_max))]
    [(fix (seq p q) (S_i ...) (S_o ...) (S_b ...) n_max)
     (seq
      (fix p (S_i ...) (S_o ...) (S_b ...) n_max)
      (fix q (S_i ...) (S_o ...) (S_b ...) n_max))]
    [(fix (loop p) (S_i ...) (S_o ...) (S_b ...) n_max)
     (loop
      (fix p (S_i ...) (S_o ...) (S_b ...) n_max))]
    [(fix (suspend p S) (S_i ...) (S_o ...) (S_b ...) n_max)
     (suspend
      (fix p (S_i ...) (S_o ...) (S_b ...) n_max)
      ,(random-ref `(S_i ... S_b ...)))]
    [(fix (trap p) (S_i ...) (S_o ...) (S_b ...) n_max)
     (trap
      (fix p (S_i ...) (S_o ...) (S_b ...) ,(add1 `n_max)))])

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
     (exit (to-nat ,(+ 2 `n)))])

  (define-metafunction esterel-eval
    generate-inputs : (S ...) -> ((S ...) ...)
    [(generate-inputs (S ...))
     ,(for/list ([_ (random 20)])
        (random-sample `(S ...)
                       (random (add1 (length `(S ...))))
                       #:replacement? #f))])

  (define-metafunction esterel-eval
    add-extra-syms : p (S ...) -> p
    [(add-extra-syms p (S ...)) (signal (S ...) p)])

  (provide do-test)
  (define (do-test [print #f])
    (redex-check
     esterel-check
     (p-check (name i (S_!_g S_!_g ...)) (name o (S_!_g S_!_g ...)) ((S ...) ...))
     #:ad-hoc
     (redex-let
      esterel-eval
      ([(S_i ...) `i]
       [(S_o ...) `o])
      (begin
        (when print
          (displayln `(p-check i o))))
        (relate `((convert p-check) ())
                `(add-extra-syms p-check ,(append `i `o))
                `((S ...) ...)
                `(S_i ...)
                `(S_o ...)))
     #:prepare fixup
     #:attempts 10000)))

(module+ test
  (require (submod ".." random-test))
  (test-case "unit"
    )
  (test-case "random"
    (do-test #t)))

(define (render)
  (parameterize ([rule-pict-style 'horizontal])
    (values
     (render-language esterel)
     (render-language esterel-eval)
     (render-reduction-relation R))))

(define-metafunction esterel-eval
  Can : p -> ((S ...) (n ...))


  [(Can nothing) (() (0))]

  [(Can pause) (() (1))]

  [(Can (exit n)) (() (,(+ 2 `n)))]

  [(Can (emit S)) ((S) (0))]
  [(Can (emit (S present))) ((S) (0))]
  [(Can (emit (S absent))) (() ())]

  [(Can (present (S present) p q))
   (Can p)]

  [(Can (present (S absent) p q))
   (Can q)]

  [(Can (present S p q))
   ((U (Can_S p) (Can_S q))
    (U (Can_K p) (Can_K q)))]

  [(Can (suspend (in-hole P p) Sdat))
   (Can (in-hole P p))
   (where #f ,(equal? `p `pause^))]

  [(Can (seq p q))
   (Can p)
   (side-condition `(∉ 0 (Can_K p)))]

  [(Can (seq p q))
   ( (U (Can_S p) (Can_S q))
     (U (without (Can_K p) 0)
        (Can_K q))
      )]

  [(Can (loop p))
   (Can p)]

  [(Can (par p q))
   ( (U (Can_S p) (Can_S q))
     (,(apply max (append `(Can_K p) `(Can_K q))))
     )]

  [(Can (trap p))
   ( (Can_S p)
     (harp... (Can_K p))
      )]

  [(Can (signal dat p))
   (Can p)]

  [(Can (signal S p))
   ((without (S_* ...) S) (n ...))
   (side-condition `(∉ S (Can_S p)))
   (where ((S_* ...) (n ...)) (Can (substitute* p S (S absent))))]

  [(Can (signal S p))
   ((without (S_* ...) S) (n ...))
   (where ((S_* ...) (n ...)) (Can p))]

  [(Can pause^)
   (() (0))]

  [(Can (suspend (in-hole P pause^) (S absent)))
   (Can (in-hole P pause^))]

  [(Can (suspend (in-hole P pause^) (S present)))
   (() (1))]

  [(Can (suspend (in-hole P pause^) S))
   ((S_o ...) (1 n ...))
   (where ((S_o ...) (n ...)) (Can (in-hole P pause^)))])

(define-metafunction esterel-eval
  harp... : (n ...) -> (n ...)
  [(harp... (n ...))
   ((harp* n) ...)])

(define-metafunction esterel-eval
  harp* : n -> n
  [(harp* 0) 0]
  [(harp* 1) 1]
  [(harp* n) ,(sub1 `n)])

(define-metafunction esterel-eval
  Can_S : p -> (S ...)
  [(Can_S p)
   (S ...)
   (where ((S ...) _) (Can p))])

(define-metafunction esterel-eval
  Can_K : p -> (n ...)
  [(Can_K p)
   (n ...)
   (where (_ (n ...)) (Can p))])


(define-metafunction esterel-eval
  ∉ : any (any ...) -> boolean
  [(∉ any_1 (any_2 ...))
   ,(not `(∈ any_1 (any_2 ...)))])
(define-metafunction esterel-eval
  ∈ : any (any ...) -> boolean
  [(∈ any_1 (any_2 ... any_1 any_3 ...))
   #t]
  [(∈ any_1 (any_2 ...))
   #f])

;; needs U and without

(define-metafunction esterel-eval
  U : (any ...) (any ...) -> (any ...)
  [(U (any_1 ...) (any_2 ...))
   (any_1 ... any_2 ...)])

(define-metafunction esterel-eval
  without : (any ...) any -> (any ...)
  [(without (any_1 ... any_2 any_3 ...) any_2)
   (without (any_1 ... any_3 ...) any_2)]
  [(without (any_1 ...) any_2) (any_1 ...)])

(define-metafunction esterel-eval
  meta-max : (n ...) (n ...) -> (n ...)
  [(meta-max () (n_2 ...))
   ()]
  [(meta-max (n_1 ...) ())
   ()]
  [(meta-max (n_1 ...) (n_2 ...))
   (,(apply max `(n_1 ... n_2 ...)))])
