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
   (signal S p)
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
  ;; there is no "unknown" status. In case of
  ;; unknowns we make assumptions
  (status ::= present absent unknown)
  (dat ::= (S present) (S absent))
  (Sdat ::= .... dat)
  ;; Signal environment
  (E ::= ((S status) ...))
  ;; a machine state
  ;; list of evaluated exprers, lists of paused exprs, environment, emitted signals
  (m ::= (state p E (S ...)))

  ;; "values"
  (v ::= vp v*)
  (vp ::= nothing (exit n))
  (v* ::=
      pause
      (seq v* q)
      (par v* v*)
      (suspend p (S present))
      (suspend v* dat)
      (trap v*))

  ;; evaluation contexts
  (M ::= (state P E (S ...)))
  (M^ ::= (state P^ E (S ...)))

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
   esterel-eval #:domain m
   (--> (in-hole M (par vp v)) (in-hole M (value-max vp v))
        par-done-right)
   (--> (in-hole M (par v vp)) (in-hole M (value-max v vp))
        par-done-left)
   (-->
    (state (in-hole P (signal S p)) E (S_S ...))
    (state (in-hole P p) (insert-env (S unknown) E) (S_S ...))
    signal)
   (--> (in-hole M (present (S present) p q)) (in-hole M p)
    is-present)
   (--> (in-hole M (present (S absent) p q)) (in-hole M q)
    is-absent)

   (-->
    (state (in-hole P (emit S)) E (S_S ...))
    (pick (state (in-hole P nothing) E (insert-signal S (S_S ...))) S present)
    emit-unknown)
   (-->
    (state (in-hole P (emit (S present))) E (S_S ...))
    (state (in-hole P nothing) E (insert-signal S (S_S ...)))
    emit-present)

   (-->
    (state (in-hole P (present S p q)) E (S_S ...))
    (pick (state (in-hole P (present S p q)) E (S_S ...)) S present)
    (judgment-holds (stuck? (in-hole P (present S p q)) E))
    guess-present)
   (-->
    (state (in-hole P (present S p q)) E (S_S ...))
    (pick (state (in-hole P (present S p q)) E (S_S ...)) S absent)
    (judgment-holds (stuck? (in-hole P (present S p q)) E))
    guess-absent)
   (-->
    (state (in-hole P (suspend p S)) E (S_S ...))
    (pick (state (in-hole P (suspend p S)) E (S_S ...)) S absent)
    (judgment-holds (stuck? (in-hole P (suspend p S)) E))
    guess-suspend-absent)

   (--> (in-hole M (loop p)) (in-hole M (seq p (loop p)))
    loop)
   (--> (in-hole M^ pause^) (in-hole M^ nothing)
        hatted-pause)
   (--> (in-hole M (seq nothing q)) (in-hole M q)
    seq-done)
   (--> (in-hole M (seq (exit n) q)) (in-hole M (exit n))
    seq-exit)
   (--> (in-hole M (suspend vp dat)) (in-hole M vp)
    suspend-value)
   ;; traps
   (--> (in-hole M (trap nothing)) (in-hole M nothing)
        trap-nothing)
   (--> (in-hole M (trap (exit 0))) (in-hole M nothing)
        trap-done)
   (--> (in-hole M (trap (exit n))) (in-hole M (exit ,(sub1 `n)))
        (side-condition (not (zero? `n)))
        trap-sub)))

(define-metafunction esterel-eval
  pick : m S status -> m
  [(pick (state p ((S_1 status_1) ... (S unknown) (S_2 status_2) ...) (S_o ...)) S status)
   (state (substitute p S (S status)) ((S_1 status_1) ... (S status) (S_2 status_2) ...) (S_o ...))])

(define-metafunction esterel-eval
  value-max : v v -> v
  [(value-max nothing v) v]
  [(value-max v nothing) v]
  [(value-max (exit n_1) (exit n_2)) (exit ,(max `n_1 `n_2))]
  [(value-max (exit n) v*) (exit n)]
  [(value-max v* (exit n)) (exit n)])

(define-judgment-form esterel-eval
  #:mode (stuck? I I)
  #:contract (stuck? p E)
  [------------
   (stuck? v E)]

  [(where ((S_1 status_1) ... (S unknown) (S_2 status_2) ...) E)
   -----------
   (stuck? (present S p q) E)]

  [(stuck? p E)
   -----------
   (stuck? (seq p q) E)]

  [(stuck? p E)
   (stuck? q E)
   -----------
   (stuck? (par p q) E)]

  [(stuck? p E)
   ----------
   (stuck? (suspend p Sdat) E)]

  [(stuck? p E)
   ----------
   (stuck? (trap p) E)]

  [-----------
   (stuck? (suspend (in-hole P pause^) S) E)]

  [(where ((S_1 status_1) ... (S present) (S_2 status_2) ...) E)
   -----------
   (stuck? (suspend (in-hole P pause^) (S present)) E)])

(define-metafunction esterel-eval
  insert-signal : S (S ...) -> (S ...)
  [(insert-signal S (S_S ...))
   ,(remove-duplicates
     (sort (cons `S `(S_S ...))
           symbol<?))])

(define-metafunction esterel-eval
  insert-env : (S status) E -> E
  [(insert-env (S status) ((S_1 status_1) ... (S status_r) (S_2 status_2) ...))
   ((S_1 status_1) ... (S status) (S_2 status_2) ...)]
  [(insert-env (S status) E)
   ,(sort (cons `(S status) `E)
          symbol<?
          #:key first)])

(define-metafunction esterel-eval
  instant : p (S ...) -> (p E (S ...))
  [(instant p (S ...))
   ((add-hats (clear-up-signals v)) (unknownify E_p) (S_p ...))
   (where (m ...) ,(apply-reduction-relation* R `(state p ((S present) ...) (S ...))))
   (where ((state v E_p (S_p ...))) (uncontradicted (m ...)))]
  [(instant p (S ...))
   ,(error 'instant "got ~a\n from ~a" `(m_p ...) `(m ...))
   (where (m ...) ,(apply-reduction-relation* R `(state p ((S present) ...) (S ...))))
   (where (m_p ...) (uncontradicted (m ...)))])

(define-metafunction esterel-eval
  instant* : p E (S ...) -> (p E (S ...))
  [(instant* p_o E (S_o ...))
   ((add-hats (clear-up-signals v)) (unknownify E_p) (S_p ...))
   (where (S ...)
          ,(for/fold ([i `()])
                     ([S (in-list `(S_o ...))])
             `(insert-signal ,S ,i)))
   (where (p E_i) (setup p_o (S ...) E))
   (where (m ...) ,(apply-reduction-relation* R `(state p E_i (S ...))))
   (where ((state v E_p (S_p ...))) (uncontradicted (m ...)))]
  [(instant* p_o E (S_o ...))
   ,(error 'instant* "got ~a\n from ~a" `(m_p ...) `((m ...) E))
   (where (S ...)
          ,(for/fold ([i `()])
                     ([S (in-list `(S_o ...))])
             `(insert-signal ,S ,i)))
   (where (p E_i) (setup p_o (S ...) E))
   (where (m ...) ,(apply-reduction-relation* R `(state p E_i (S ...))))
   (where (m_p ...) (uncontradicted (m ...)))])

(define-metafunction esterel-eval
  setup : p (S ...) E -> (p E)
  [(setup p
          (S S_2 ...)
          ((S_3 status_3) ... (S unknown) (S_4 status_4) ...))
   (setup (substitute p S (S present))
          (S_2 ...)
          ,`((S_3 status_3) ... (S present) (S_4 status_4) ...))]
  [(setup p () E) (p E)])

(define-metafunction esterel-eval
  uncontradicted : (m ...) -> (m ...)
  [(uncontradicted ()) ()]
  [(uncontradicted (m_1 m_2 ...))
   (m_1 m_o ...)
   (where (m_o ...) (uncontradicted (m_2 ...)))
   (where #f ,(judgment-holds (contradiction? m_1)))]
  [(uncontradicted (m_1 m_2 ...))
   (uncontradicted (m_2 ...))
   (where #t ,(judgment-holds (contradiction? m_1)))])

(define-judgment-form esterel-eval
  #:mode     (contradiction? I)
  #:contract (contradiction? m)
  [(where (any_!_1 any_!_1) ((present-in E) (S ...)))
   ------------ "unemitted present"
   (contradiction? (state p E (S ...)))]
  [(where (in-hole P (emit (S_e absent))) p)
   ------------ "emitted absent"
   (contradiction? (state p
                          E
                          (S ...)))])

(define-metafunction esterel-eval
  present-in : E -> (S ...)
  [(present-in ()) ()]
  [(present-in ((S present) (S_r status) ...))
   (S S_o ...)
   (where (S_o ...) (present-in ((S_r status) ...)))]
  [(present-in ((S status_other) (S_r status) ...))
   (present-in ((S_r status) ...))])

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

(define-metafunction esterel-eval
  unknownify : E -> E
  [(unknownify ((S status) ...))
   ((S unknown) ...)])


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
  (traces R `(state ,p () ()) #:pred highlight-done!)
  (define pp `(instant ,p ()))
  (traces R `(state ,(first pp) ,(second pp) ()) #:pred highlight-done!))

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
               #:break (and
                        (redex-match cos:esterel-eval p (first p))
                        (redex-match esterel-eval nothing (first q))))
      (match-define `((,p2 ,data ,pouts))
        (let ()
          (define v
            (judgment-holds
             (eval->> (machine (· ,(first p)) ,(second p))
                    ,(setup-*-env i in)
                    (machine pbar data_*) (S ...))

             (pbar data_* (S ...))))
          (unless (= (length v) 1)
            (error 'cc->>
                   "got bad reduction, given ~a ~a\n got ~a\nThe origional call was ~a"
                   `(machine ,(first p) ,(second p))
                   (setup-*-env i in)
                   v
                   (list 'relate pp qp ins in out)))
          v))
      (match-define (list q2 E qouts) `(instant* ,(first q) ,(second q) ,i))
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
      (values (list p2 data) (list q2 E)))
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
