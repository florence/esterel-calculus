#lang debug racket
(require redex/reduction-semantics redex/pict)
(require esterel/cos-model
         racket/random
         rackunit
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
  (n ::= natural)
  ;#:binding-forms
  ;(signal S p #:refers-to S)
  )

(define-extended-language esterel-eval esterel
  ;; there is no "unknown" status. In case of
  ;; unknowns we make assumptions
  (status ::= present absent unknown)
  (dat ::= (S present) (S absent))
  (Sdat ::= .... dat)
  ;; list of evaluated exprers, lists of paused exprs, environment, emitted signals

  ;; "values"
  (v ::= vp v*)
  (vp ::= nothing (exit n))
  (v* ::=
      (in-hole A pause)
      (in-hole A (seq v* q))
      (in-hole A (par v* v*))
      (in-hole A (suspend p (S present)))
      (in-hole A (suspend v* dat))
      (in-hole A (trap v*)))

  (A ::=
     hole
     (signal Sdat A))
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
  substitute : any S Sdat -> any
  [(substitute (signal S p) S Sdat)
   (signal S p)]
  [(substitute (any ...) S Sdat)
   ((substitute any S Sdat) ...)]
  [(substitute S S Sdat) Sdat]
  [(substitute any S Sdat) any])


(define R
  ;; ASSUMPTIONS:
  ;; program has no causality bugs
  ;; program is loop safe
  ;; no nested signal/traps have overlapping names
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
    (in-hole A (signal S (in-hole P* (emit S))))
    (in-hole A
             (signal (S present)
                     (substitute (in-hole P* nothing) S (S present))))
    emit-unknown)
   (-->
    (in-hole A (signal (S present) (in-hole P* (emit (S present)))))
    (in-hole A (signal (S present) (in-hole P* nothing)))
    emit-present)

   (-->
    (in-hole A (signal S p))
    (in-hole A (signal (S absent) (substitute p S (S absent))))
    (where #t (∉ S (Can_S p)))
    (judgment-holds (stuck? p))
    absence)

   (--> (in-hole P* (loop p)) (in-hole P* (seq p (loop p)))
    loop)
   (--> (in-hole P^* pause^) (in-hole P^* nothing)
        hatted-pause)
   (--> (in-hole P* (seq nothing q)) (in-hole P* q)
    seq-done)
   (--> (in-hole P* (seq (exit n) q)) (in-hole P* (exit n))
    seq-exit)
   (--> (in-hole P* (suspend vp dat)) (in-hole P* vp)
    suspend-value)
   ;; traps
   (--> (in-hole P* (trap vp)) (in-hole P* (harp vp))
        trap-done)
   ;; lifting signals
   (--> (in-hole A (in-hole P (signal S p)))
        ;; TODO alpha-rename
        ;; TODO can reduce to self
        (in-hole A (signal S (in-hole P p)))
        raise-signal)))

(define-metafunction esterel-eval
  harp : vp -> vp
  [(harp nothing) nothing]
  [(harp (exit 0)) nothing]
  [(harp (exit n)) (exit ,(sub1 `n))])

(define-metafunction esterel-eval
  value-max : v v -> v
  [(value-max nothing v) v]
  [(value-max v nothing) v]
  [(value-max (exit n_1) (exit n_2)) (exit ,(max `n_1 `n_2))]
  [(value-max (exit n) v*) (exit n)]
  [(value-max v* (exit n)) (exit n)])

(define-judgment-form esterel-eval
  #:mode (stuck? I)
  #:contract (stuck? p)
  [------------
   (stuck? v)]

  [-----------
   (stuck? (present S p q))]

  [(stuck? p)
   -----------
   (stuck? (seq p q))]

  [(stuck? p)
   (stuck? q)
   -----------
   (stuck? (par p q))]

  [(stuck? p)
   ----------
   (stuck? (suspend p Sdat))]

  [(stuck? p)
   ----------
   (stuck? (trap p))]

  [(stuck? p)
   ----------
   (stuck? (signal Sdat p))]

  [-----------
   (stuck? (suspend (in-hole P pause^) S))]

  [-----------
   (stuck? (suspend (in-hole P pause^) (S present)))])

(define-metafunction esterel-eval
  instant : p (S ...) -> (p (S ...))
  [(instant p (S ...))
   ((add-hats (clear-up-signals v))
    (get-signals v))
   (where (v) ,(apply-reduction-relation* R `(setup p (S ...))))]
  [(instant p (S ...))
   ,(error 'instant "got ~a\n from ~a" `(p_* ...) `(setup p (S ...)))
   (where (p_* ...) ,(apply-reduction-relation* R `(setup p (S ...))))])

(define-metafunction esterel-eval
  setup : p (S ...) -> p
  [(setup p
          (S S_2 ...))
   (setup (substitute p S (S present))
          (S_2 ...))]
  [(setup p ()) p])

(define-metafunction esterel-eval
  get-signals : p -> (S ...)
  [(get-signals (signal (S present) p))
   (S S_1 ...)
   (where (S_1 ...) (get-signals p))]
  [(get-signals (signal (S absent) p))
   (get-signals p)]
  [(get-signals p) ()])

(define-metafunction esterel
  add-hats : p -> p
  [(add-hats pause) pause^]
  [(add-hats pause^) pause^]
  [(add-hats nothing) nothing]
  [(add-hats (signal S p)) (signal S (add-hats p))]
  [(add-hats (seq p q)) (seq (add-hats p) q)]
  [(add-hats (par p q)) (par (add-hats p) (add-hats q))]
  [(add-hats (suspend p S)) (suspend (add-hats p) S)]
  [(add-hats (trap p)) (trap (add-hats p))])

(define-metafunction esterel-eval
  clear-up-signals : p -> p
  [(clear-up-signals nothing) nothing]
  [(clear-up-signals pause) pause]
  [(clear-up-signals pause^) pause^]
  [(clear-up-signals (signal S p))
   (signal S (clear-up-signals p))]
  [(clear-up-signals (signal (S status) p))
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
                         (redex-match esterel-eval nothing (first q)))))
      
      (define constructive-reduction
        (judgment-holds
         (c->> (machine (· ,(first p)) ,(second p))
               ,(setup-*-env i in)
               (machine pbar data_*) (S ...) k)
         (pbar data_* (S ...))))
      (match constructive-reduction
        [`((,p2 ,data ,pouts))
         (match-define (list q2 qouts) `(instant* ,q ,i))
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
         ;; non-constructive program
         (raise v)
         (values #f #f)]))
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

  (provide do-test)
  (define (do-test [print #f])
    (redex-check
     esterel-check (p-check (name i (S_!_g S_!_g ...)) (name o (S_!_g S_!_g ...)) ((S ...) ...))
     #:ad-hoc
     (redex-let
      esterel-eval
      ([(S_i ...) `i]
       [(S_o ...) `o])
      (begin
        (when print
          (displayln `(p-check i o))))
        (relate `((convert p-check) ())
                `(p-check ,(for/fold ([E `()])
                                     ([S (in-list `(S_i ... S_o ...))])
                             `(insert-env (,S unknown),E)))
                `((S ...) ...)
                `(S_i ...)
                `(S_o ...)))
     #:prepare fixup
     #:attempts 10000)))

(module+ test
  (require (submod ".." random-test))
  (do-test))

(define (render)
  (parameterize ([rule-pict-style 'horizontal])
    (values
     (render-language esterel)
     (render-language esterel-eval)
     (render-reduction-relation R))))


#;
(define-judgment-form
  esterel
  #:mode     (constructive I I O)
  #:contract (constructive p (S ...))
  [--------------
   (constructive nothing (S ...) (S ...))]
  [--------------
   (constructive pause (S ...) (S ...))]
  [--------------
   (constructive pause^ (S ...) (S ...))]
  [--------------
   (constructive (emit S_n) (S ...) (S_n S ...))]
  [(constructive p (S ...) (S_r ...))
   --------------
   (constructive (signal S p) (S ...) (S_r ...))]
  [(where (S_1 ... S_p S_2 ...) (S ...))
   (constructive p (S ...) (S_r ...))
   (constructive q (S ...) (S_l ...))
   --------------
   (constructive (present S_p p q) (S ...) (U (S_r ...) (S_l ...)))]
  [???
   --------------
   (constructive (par p q) (S ...) (U (S_r ...) (S_l ...)))]
  [(constructive p (S ...) (S_r ...))
   --------------
   (constructive (loop p) (S ...) (S_r ...))]
  [(where (S_1 ... S_p S_2 ...) (S ...))
   (constructive p (S ...) (S_r ...))
   (constructive q (S ...) (S_l ...))
   --------------
   (constructive (present S_p p q) (S ...) (U (S_r ...) (S_l ...)))]
  )


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
   (where ((S_* ...) (n ...)) (Can (substitute p S (S absent))))
   (side-condition `(∉ S (Can_S p)))]

  [(Can (signal S p))
   ((without (S_* ...) S) (n ...))
   (where ((S_* ...) (n ...)) (Can p))]

  [(Can pause^)
   (() (0))]

  [(Can (suspend (in-hole P pause^) (S absent)))
   (Can (in-hole P pause^))]

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
