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
   (seq p q)
   (suspend p Sdat)
   (trap p)
   (exit n)
   (suspend^ p Sdat))
  (Sdat ::= S)
  (S ::= variable-not-otherwise-mentioned)
  (n ::= natural))

(define-extended-language esterel-eval esterel
  (p q ::= .... (signal (Sdat ...) p))
  (status ::= present absent)
  (dat ::= (S status))
  (Sdat ::= .... dat)

  ;; values and answers
  (a ::= ap a*)
  (ap ::= (signal (Sdat ...) vp))
  (a* ::= (signal (Sdat ...) v*))
  (v ::= vp v*)
  (vp ::= nothing (exit n))
  (v* ::=
      pause
      (seq v* q)
      (par v* v*)
      (suspend^ p (S present))
      (suspend^ v* Sdat)
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
     (suspend^ P (S absent))
     (trap P)))

(define-union-language esterel-eval* esterel-eval (cos: cos:esterel-eval))

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
  freshen-up : p -> p
  [(freshen-up p)
   (substitute p ,(gensym) ,(gensym))])

(define-extended-language wrn* wrn
  #:binding-forms
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
    (where (S_not ...) (Cannot p (S)))
    (where #t (∈ S (S_not ...)))
    ;; these are only here to make things run with decent speed
    (judgment-holds (stuck? p any))
    (where #t (unprogressable (Sdat_1 ...) p))
    absence)

   (--> (in-hole P* (loop p)) (in-hole P* (seq p (loop p)))
    loop)
   (--> (in-hole P* (seq nothing q)) (in-hole P* q)
    seq-done)
   (--> (in-hole P* (seq (exit n) q)) (in-hole P* (exit n))
    seq-exit)
   (--> (in-hole P* (suspend vp Sdat)) (in-hole P* vp)
    suspend-value)
   (--> (in-hole P* (suspend^ vp (S absent))) (in-hole P* vp)
    suspend^-value)
   ;; traps
   (--> (in-hole P* (trap vp)) (in-hole P* (harp vp))
        trap-done)
   ;; lifting signals
   (--> (signal (Sdat ...) (in-hole P (signal S p)))
        (signal (insert-signal S_* (Sdat ...)) (in-hole P_* p_*))
        (where (in-hole P_* (signal S_* p_*)) (freshen-up (in-hole P (signal S p))))
        raise-signal)))

(define-metafunction esterel-eval
  unprogressable : (Sdat ...) p -> boolean
  [(unprogressable () p) #t]
  [(unprogressable (dat Sdat ...) p)
   (unprogressable (Sdat ...) p)]
  [(unprogressable (S Sdat ...) p)
   #t
   (where ⊥ (Cannot p (S)))
   (where #t (unprogressable (Sdat ...) p))]
  [(unprogressable (Sdat ...) p) #f])

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

  [-----------
   (stuck? (present S p q) (S))]

  [(stuck? p (S ...))
   -----------
   (stuck? (seq p q) (S ...))]

  [(stuck? p (S_1 ...))
   (stuck? q (S_2 ...))
   -----------
   (stuck? (par p q) (S_1 ... S_2 ...))]

  [(stuck? q (S ...))
   -----------
   (stuck? (par v q) (S ...))]
  [(stuck? p (S ...))
   -----------
   (stuck? (par p v) (S ...))]

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

  [(stuck? p (S_r ...))
   -----------
   (stuck? (suspend^ p (S absent)) (S_r ...))]
  [-----------
   (stuck? (suspend^ p S) (S))])

(define-metafunction esterel-eval
  instant : p ((S status) ...) -> (p (S ...)) or #f
  [(instant p ((S status) ...))
   (p_*
    (get-signals a))
   (where (a a_r ...) ,(apply-reduction-relation* R `(setup p ((S status) ...))))
   (where (p_* p_r ...) ((add-hats (clear-up-signals a)) (add-hats (clear-up-signals a_r)) ...))
   (where (#t ...) ,(map (lambda (x) (alpha-equivalent? wrn* `p_* x)) `(p_r ...)))]
  [(instant p ((S status) ...))
   #f
   (where (p_* ...) ,(apply-reduction-relation* R `(setup p ((S status) ...))))
   (side-condition (pretty-print `(p_* ...)))])

(define-metafunction esterel-eval
  instant* : p ((S status) ...) -> p or #f
  [(instant* p ((S status) ...))
   a
   (where (a a_r ...) ,(apply-reduction-relation* R `(setup p ((S status) ...))))
   (where (p_* p_r ...) ((add-hats (clear-up-signals a)) (add-hats (clear-up-signals a_r)) ...))
   (where (#t ...) ,(map (lambda (x) (alpha-equivalent? wrn* `p_* x)) `(p_r ...)))]
  [(instant* p ((S status) ...))
   #f
   (where (p_* ...) ,(apply-reduction-relation* R `(setup p ((S status) ...))))
   (side-condition (pretty-print `(p_* ...)))])

(define-metafunction esterel-eval
  setup : p (dat ...) -> p
  [(setup p
          ((S status) dat ...))
   (setup (set p S (S status))
          (dat ...))]
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
  [(add-hats pause) nothing]
  [(add-hats nothing) nothing]
  [(add-hats (signal (S ...) p)) (signal (S ...) (add-hats p))]
  [(add-hats (seq p q)) (seq (add-hats p) q)]
  [(add-hats (par p q)) (par (add-hats p) (add-hats q))]
  [(add-hats (suspend p S)) (suspend^ (add-hats p) S)]
  [(add-hats (suspend^ p S)) (suspend^ (add-hats p) S)]
  [(add-hats (trap p)) (trap (add-hats p))])

(define-metafunction esterel-eval
  clear-up-signals : p -> p
  [(clear-up-signals (signal (Sdat ...) p))
   (signal (S ...) (clear-up-signals p))
   (where (S ...)
          ,(map (lambda (x) (if (list? x) (first x) x)) `(Sdat ...)))]
  [(clear-up-signals nothing) nothing]
  [(clear-up-signals pause) pause]
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
  [(clear-up-signals (suspend^ p (S status)))
   (suspend^ (clear-up-signals p) S)]
  [(clear-up-signals (suspend^ p S))
   (suspend^ (clear-up-signals p) S)]
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
      ()
      (signal
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
                   O)))))))

  (traces R p #:pred highlight-done!)
  #;
  #;
  (define pp `(instant ,p ()))
  (traces R (first pp) #:pred highlight-done!))





(define (render)
  (parameterize ([rule-pict-style 'horizontal])
    (values
     (render-language esterel)
     (render-language esterel-eval)
     (render-reduction-relation R))))

(define-metafunction esterel-eval
  Cannot : p (S ...) -> (S ...) or ⊥
  [(Cannot p (S_o ...))
   (S_1 S_r ...)
   (where ((S ...) (n ...))
          (Can p))
   (where (S_1 S_r ...)
          ,(filter (lambda (s) (not (member s `(S ...)))) `(S_o ...)))]
  [(Cannot p (S ...)) ⊥])

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

  [(Can (suspend p Sdat))
   (Can p)]

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

  #|
  [(Can (signal S p))
   ((without (S_* ...) S) (n ...))
   (side-condition `(∉ S (Can_S p)))
   (where ((S_* ...) (n ...)) (Can (substitute* p S (S absent))))]
  |#

  [(Can (signal S p))
   ((without (S_* ...) S) (n ...))
   (where ((S_* ...) (n ...)) (Can p))]

  [(Can (suspend^ p (S absent)))
   (Can p)]

  [(Can (suspend^ p (S present)))
   (() (1))]

  [(Can (suspend^ p S))
   ((S_o ...) (1 n ...))
   (where ((S_o ...) (n ...)) (Can p))])

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

#|

;; Seems to run forever?
((signal random-signal1238 (signal random-signal1239 (trap nothing))) in: (I tR T X Zi g M Y P Pb Yeq) out: (H V Z C F) instants: (() () () () () () () () () () () () ()))

|#

#|
(define-judgment-form esterel-eval*
  #:mode    (~ I                I I)
  #:contract (~ (cos:pbar (cos:S ...)) p (S ...))
  [(~_S (cos:S ...) (Sdat ...) (S_o ...))
   -----------
   (~ (cos:p (cos:S ...)) (signal (Sdat ...) nothing) (S_o ...))]
  [(~_p cos:pbar p)
   (~_S (cos:S ...) (Sdat ...) (S_o ...))
   -----------
   (~ (cos:pbar (cos:S ...)) (signal (Sdat ...) p) (S_o ...))])

(define-judgment-form esterel-eval*
  #:mode     (~_S I           I          I)
  #:contract (~_S (cos:S ...) (Sdat ...) (S ...))
  [(where (cos:S_o ...)
          (members/cos:S (cos:S ...) (S_o ...)))
   (where (S ...)
          (members/Sdat (Sdat ...) (S_o ...)))
   (subset (S ...) (cos:S_o ...))
   (subset (cos:S_o ...) (S ...))
   -----------
   (~_S (cos:S ...) (Sdat ...) (S_o ...))])

(define-metafunction esterel-eval*
  members/cos:S : (cos:S ...) (S ...) -> (cos:S ...)
  [(members/cos:S () (S ...)) ()]

  [(members/cos:S (cos:S cos:S_r ...) (S_1 ... S S_2 ...))
   (S S_o ...)
   (where cos:S S)
   (where (S_o ...)
          (members/cos:S (cos:S_r ...) (S_1 ... S S_2 ...)))]

  [(members/cos:S (cos:S cos:S_r ...) (S ...))
   (members/cos:S (cos:S_r ...) (S ...))])

(define-metafunction esterel-eval*
  members/Sdat : (Sdat ...) (S ...) -> (S ...)
  [(members/Sdat () (S ...)) ()]

  [(members/Sdat ((S present) Sdat ...) (S_1 ... S S_2 ...))
   (S S_o ...)
   (where (S_o ...)
          (members/Sdat (Sdat ...) (S_1 ... S S_2 ...)))]

  [(members/Sdat (Sdat Sdat_r ...) (S ...))
   (members/Sdat (Sdat_r ...) (S ...))])

(define-judgment-form esterel-eval*
  #:mode     (subset I       I)
  #:contract (subset (S ...) (S ...))
  [--------
   (subset () (S ...))]
  [(subset (S_1 ... S_2 ...)
           (S_3 ... S S_4 ...))
   -------
   (subset (S_1 ... S S_2 ...)
           (S_3 ... S S_4 ...))])

(define-judgment-form esterel-eval*
  #:mode     (~_p I        I)
  #:contract (~_p cos:pbar p)
  [---------
   (~_p (hat pause) pause)]

  [(~_p cos:phat p)
   ----------
   (~_p (present cos:S cos:phat cos:q) p)]

  [(~_p cos:qhat p)
   ----------
   (~_p (present cos:S cos:p cos:qhat) p)]

  [(~_p cos:phat p)
   ----------
   (~_p (seq cos:phat cos:q) p)]

  [(~_p cos:qhat p)
   ----------
   (~_p (seq cos:p cos:qhat) p)]

  [(~_p cos:phat p)
   (~_p cos:qhat q)
   ----------
   (~_p (par cos:phat cos:qhat) (par p q))]

  [(~_p cos:phat p)
   ----------
   (~_p (par cos:phat cos:q) p)]

  [(~_p cos:qhat q)
   ----------
   (~_p (par cos:p cos:qhat) q)]

  [(where S cos:S)
   (~_p cos:phat p)
   ----------
   (~_p (suspend cos:phat cos:S)
        (suspend p S))]

  [(where S cos:S)
   (~_p cos:phat p)
   ----------
   (~_p (suspend cos:phat cos:S)
        (suspend p (S status)))]

  [(where S cos:S)
   (~_p cos:phat p)
   ----------
   (~_p (suspend cos:phat cos:S)
        (suspend^ p S))]

  [(where S cos:S)
   (~_p cos:phat p)
   ----------
   (~_p (suspend cos:phat cos:S)
        (suspend^ p (S staus)))]

  [(~_p cos:phat p)
   ;; TODO equality with exits?
   (where (loop cos:p_*) (remove-selected (loop cos:phat)))
   (where (loop cos:p_*) (convert (loop p_*)))
   ----------
   (~_p (loop cos:phat) (seq p (loop p_*)))]

  [(~_p cos:phat p)
   ---------
   (~_p (trap cos:phat) (trap p))]

  [(~_p cos:phat p)
   ---------
   (~_p (signal cos:S cos:phat) p)]

  [;; TODO equality with exits
   (where cos:p (convert p))
   ---------
   (~_p cos:p p)])
|#

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
(module+ random-test

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
     (loop p-check-pause)))

  (define (relate pp qp ins in out #:limits? [limits? #f] #:debug? [debug? #f])
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
          (when debug?
            (printf "running c->>\n")
            (pretty-print
             (list 'c->> `(machine ,(first p) ,(second p))
                   (setup-*-env i in)
                   '(machine pbar data_*) '(S ...) 'k)))
          (define constructive-reduction
            (judgment-holds
             (c->> (machine ,(first p) ,(second p))
                   ,(setup-*-env i in)
                   (machine pbar data_*) (S ...) k)
             (pbar data_* (S ...))))
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
          `(,i one)
          `(,i zero))))

  (define (setup-r-env ins in)
    (for/list ([i in])
      (if (member i ins)
          `(,i present)
          `(,i absent))))

  (define (fixup e)
    (redex-let
     esterel
     ([(p (S_i ...) (S_o ...) ((S ...) ...)) e])
     (let ()
       (define low-signals? (< (random) 1/8))
       (define signals (build-list (add1 (random 2)) (lambda (_) (gensym 'random-signal))))
       (define SI (remove-duplicates `(S_i ...)))
       (define SO (remove-duplicates `(S_o ...)))
       (define (wrap p signals)
         (match signals
           [(cons s r)
            `(signal ,s ,(wrap p r))]
           [else p]))
       (if low-signals?
           (list
            (wrap
             `(fix/low-signals p
                               ,signals
                               0)
             signals)
            SI
            SO
            `(generate-inputs ()))
           (list
            `(fix p ,SI ,SO)
            SI
            SO
            `(generate-inputs ,SI))))))

  (define-metafunction esterel-eval
    fix/low-signals : p (S ...) n -> p
    [(fix/low-signals nothing (S ...) n)
     nothing]
    [(fix/low-signals pause (S ...) n)
     pause]
    [(fix/low-signals (exit n) (S ...) n_max)
     ,(if (zero? `n_max)
          `nothing
          `(exit ,(random `n_max)))]
    [(fix/low-signals (emit any) (S ...) n_max)
     (emit ,(random-ref `(S ...)))]
    [(fix/low-signals (signal any p) (S ...) n_max)
     (fix/low-signals p (S ...) n_max)]
    [(fix/low-signals (present any p q) (S ...) n_max)
     (present ,(random-ref `(S ...))
              (fix/low-signals p (S ...) n_max)
              (fix/low-signals q (S ...) n_max))]
    [(fix/low-signals (par p q) (S ...) n_max)
     (par
      (fix/low-signals p (S ...) n_max)
      (fix/low-signals q (S ...) n_max))]
    [(fix/low-signals (seq p q) (S ...) n_max)
     (seq
      (fix/low-signals p (S ...) n_max)
      (fix/low-signals q (S ...) n_max))]
    [(fix/low-signals (loop p) (S ...) n_max)
     (loop
      (fix/low-signals p (S ...) n_max))]
    [(fix/low-signals (suspend p any) (S ...) n_max)
     (suspend
      (fix/low-signals p (S ...) n_max)
      ,(random-ref `(S ...)))]
    [(fix/low-signals (trap p) (S ...) n_max)
     (trap
      (fix/low-signals p (S ...) ,(add1 `n_max)))])

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
          (displayln (list `~f `p-check `i `o `((S ...) ...) '#:limits? limits?))
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
      (list p s))))

(module+ test
  #|
  (test-case "unit"
  (check-true
  (judgment-holds (~ ((signal random-signal870 (hat pause)) ())
  (signal ((B absent) M random-signal870«0») pause)
  (M))))
  (check-true
  (judgment-holds (~_p (loop pause)
  (loop pause))))
  (check-true
  (judgment-holds (~ ((loop pause) ())
  (signal () (loop pause))
  ())))
  (check-true
  (judgment-holds (~ ((loop (hat pause)) ())
  (signal () (seq pause (loop pause)))
  ())))
  (check-true
  (judgment-holds (~ ((signal random-signal912 (signal random-signal913 (loop (hat pause)))) ())
  (signal ((a absent) fL random-signal912«0» random-signal913«2») (seq pause (loop pause)))
  (FL))))
  (check-true
  (judgment-holds
  (~ ((seq (suspend pause a) (loop pause)) ())
  (signal (a zI i) (seq (suspend pause a) (loop pause)))
  (zI i))))
  (check-true
  (judgment-holds
  (~_p (suspend (hat pause) a)
  (suspend pause (a present)))))
  (check-true
  (judgment-holds
  (~ ((suspend (hat pause) a)  ())
  (signal ((a present)) (suspend pause (a present)))
  (zI i))))
  (check-true
  (judgment-holds (~_S () ((a present) zI i) (zI i))))
  (check-true
  (judgment-holds
  (~_p (seq (hat pause) (loop pause))
  (seq pause (loop pause)))))
  (check-true
  (judgment-holds
  (~_p (seq (suspend (hat pause) a) (loop pause))
  (seq (suspend pause (a present)) (loop pause)))))
  (check-true
  (judgment-holds
  (~ ((seq (suspend (hat pause) a) (loop pause)) ())
  (signal ((a present) zI i) (seq (suspend pause (a present)) (loop pause)))
  (zI i)))))

  (check-true
  (judgment-holds
  (~ ((signal random-signal912 (signal random-signal913 (loop (hat pause)))) ())
  (signal ((a absent) fL random-signal912«0» random-signal913«2») (seq pause (loop pause)))
  (FL))))
  |#)



(module+ test
  (require (submod ".." random-test))
  (test-case "random"
    (do-test #t)))


(module+ tracing

  (define-syntax-rule (render-derivations r)
    (show-derivations (build-derivations r)))
#;
  (define-judgment-form cos:esterel-eval
    #:mode     (do I I O  O      O)
    #:contract (do M E M (S ...) k)
    [(cos:non-det-> (machine pdotdot data) E
                    (machine pdotdot_* data_*) ⊥ k)
     -----------
     (do (machine pdotdot data) E
       (machine pdotdot_* data_*) () k)]

    [(cos:non-det-> (machine pdotdot data) E
                    (machine pdotdot_* data) S k)
     -----------
     (do (machine pdotdot data) E
       (machine pdotdot_* data) (S) k)]

    [(cos:non-det-> (machine pdotdot data) E
                    (machine pdotdot_* data_*) S ⊥)
     (do (machine pdotdot_* data_*) E
       (machine pdotdot_** data_**) (S_r ...) k)
     -----------
     (do (machine pdotdot data) E
       (machine pdotdot_** data_**) (U (S) (S_r ...)) k)]

    [(cos:non-det-> (machine pdotdot data) E
                    (machine pdotdot_* data_*) ⊥ ⊥)
     (do (machine pdotdot_* data_*) E
       (machine pdotdot_** data_**) (S ...) k)
     -----------
     (do (machine pdotdot data) E
       (machine pdotdot_** data_**) (S ...) k)])

  (define (steps p)
    (traces R `(signal () ,p))
    (render-derivations (cos:→* (machine (· (convert ,p)) ()) () (machine pbar any_1) any_2 any_3))))
