#lang debug racket
(provide (all-defined-out))
(require redex/reduction-semantics)
(require racket/random
         (prefix-in r: racket)
         rackunit
         racket/sandbox)

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
   (seq p q)
   (suspend p Sdat)
   (trap p)
   (exit n)
   (suspend^ p Sdat)
   ;; state
   (shared s := e p)
   (<= s e)
   (var x := e p)
   (:= x e)
   (if e p q))

  (Sdat ::= S)
  (S s x ::= variable-not-otherwise-mentioned)
  (n ::= natural)

  (e ::=
     shareddat
     vardat
     (f e ...)
     n)
  (f ::= + (rfunc any))
  (shareddat ::= s)
  (vardat ::= x))

(define-extended-language esterel-eval esterel
  (p q ::= ....
     (env (env-v ...) p))
  (env-v ::= Sdat shareddat vardat)
  (status ::= present absent unknown)
  (dat ::= (sig S status))
  (Sdat ::= .... dat)

  ;; state
  (shared-status ::= ready old new)
  (shareddat ::= .... (shar s ev shared-status))
  (vardat ::= .... (var· x ev))
  (ev ::= n)

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
      (suspend^ p (sig S present))
      (suspend^ v* Sdat)
      (suspend v* Sdat)
      (trap v*))

  (A ::= (env (env-v ...) hole))
  (P* Q* ::= (in-hole A P))
  (E* ::= (in-hole A (in-hole P E)))

  ;; evaluation contexts
  (P Q ::=
     hole
     (seq P q)
     (par P q)
     (par p Q)
     (suspend P Sdat)
     (suspend^ P (sig S absent))
     (trap P))

  ;; state evaluation context
  (E ::= hole
     (shared s := E p)
     (var x := E p)
     (<= s E)
     (:= x E)
     (if E p q)
     (f ev ... E e ...))


  (p-not-v q-not-v ::=
           (signal S p)
           (present Sdat p q)
           (emit Sdat)
           (shared s := e p)
           (<= s e)
           (var x := e p)
           (:= x e)
           (loop p)
           (if e p q)

           (par p-not-v q)
           (par p q-not-v)
           (seq p-not-v q)
           (suspend p-not-v Sdat)
           (suspend^ p-not-v (sig S absent))
           (trap p-not-v)

           (suspend^ p (sig S unknown))

           (par vp v)
           (par v vp)
           (seq vp q)
           (trap vp)
           (suspend vp Sdat)
           (suspend^ vp (sig S absent))))


(define-metafunction esterel-eval
  substitute* : any_1 any_2 any_3 -> any
  [(substitute* any any any_3) any_3]
  [(substitute* (signal S p) S Sdat)
   (signal S p)]
  [(substitute* (signal S p) (sig S status) Sdat)
   (signal S p)]
  [(substitute* (shared s := e p) s shareddat)
   (shared s := (substitute* e s shareddat) p)]
  [(substitute* (shared s := e p) (shar s ev shared-status) shareddat)
   (shared s := (substitute* e (shar s ev shared-status) shareddat)  p)]
  [(substitute* (var x := e p) x vardat)
   (shared x := (substitute* e x vardat) p)]
  [(substitute* (var x := e p) (var· x ev) vardat)
   (var x := (substitute* e (var· x ev) vardat)  p)]
  [(substitute* (<= s e) any_2 any_3)
   (<= s (substitute* e any_2 any_3))]
  [(substitute* (:= x e) any_2 any_3)
   (:= x (substitute* e any_2 any_3))]
  [(substitute* (any_1 ...) any_2 any_3)
   ((substitute* any_1 any_2 any_3) ...)]
  [(substitute* any_1 any_2 any_3 ) any_1])

(define-extended-language wrn esterel-eval
  #:binding-forms
  (signal S p #:refers-to S)
  (shared s := e p #:refers-to s))

(define-extended-language wrn* wrn
  #:binding-forms
  (signal (Sdat ...) p #:refers-to (shadow Sdat ...))
  (shared (shareddat ...) p #:refers-to (shadow shareddat ...)))


(define R
  ;; ASSUMPTIONS:
  ;; program is loop safe
  (reduction-relation
   esterel-eval #:domain p
   (--> (in-hole P* (par vp v)) (in-hole P* (value-max vp v))
        par-done-right)
   (--> (in-hole P* (par v vp)) (in-hole P* (value-max v vp))
        par-done-left)
   (--> (in-hole P* (present (sig S present) p q)) (in-hole P* p)
    is-present)
   (--> (in-hole P* (present (sig S absent) p q)) (in-hole P* q)
    is-absent)
   (-->
    (in-hole P* (emit (sig S unknown)))
    (substitute* (in-hole P* nothing) (sig S unknown) (sig S present))
    emit-unknown)
   (--> (in-hole P* (emit (sig S present))) (in-hole P* nothing)
        emit-present)
   (-->
    (env (env-v_1 ... (sig S unknown) env-v_2 ...) p)
    (substitute* (env (env-v_1 ... (sig S unknown) env-v_2 ...) p) (sig S unknown) (sig S absent))
    (where (S_not ...) (Cannot p (S)))
    (where #t (∈ S (S_not ...)))
    ;; these are only here to make things run with decent speed
    (judgment-holds (stuck? p))
    (where #t (unprogressable (env-v_1 ...) p))
    absence)

   (--> (in-hole P* (loop p)) (in-hole P* (seq p (loop p)))
    loop)
   (--> (in-hole P* (seq nothing q)) (in-hole P* q)
    seq-done)
   (--> (in-hole P* (seq (exit n) q)) (in-hole P* (exit n))
    seq-exit)
   (--> (in-hole P* (suspend vp Sdat)) (in-hole P* vp)
    suspend-value)
   (--> (in-hole P* (suspend^ vp (sig S absent))) (in-hole P* vp)
    suspend^-value)
   ;; traps
   (--> (in-hole P* (trap vp)) (in-hole P* (harp vp))
        trap-done)
   ;; lifting signals
   (--> (in-hole P* (signal S p))
        (add-new-signal S (in-hole P* p))
        raise-signal)

   ;; shared state
   (-->
    (in-hole P* (shared s := ev p))
    (add-new-shared s ev (in-hole P* p))
    raise-shared)
  (-->
    (env (env-v_1 ... (shar s any old)  env-v_2 ...) (in-hole P (<= s ev)))
    (substitute* (env (env-v_1 ... (shar s any old) env-v_2 ...) (in-hole P nothing))
                 (shar s any old) (shar s ev new))
   set-shared-value-old)

  (-->
   (env (env-v_1 ... (shar s ev_o new) env-v_2 ...) (in-hole P (<= s ev_n)))
   (substitute* (env (env-v_1 ... (shar s ev_o new) env-v_2 ...) (in-hole P nothing))
                (shar s ev_o new) (shar s (δ + ev_o ev_n) new))
   set-value-new)

  (-->
   (env (env-v_1 ... (shar s ev shared-status) env-v_2 ...) p)
   (substitute* (env (env-v_1 ... (shar s ev shared-status) env-v_2 ...) p)
                (shar s ev shared-status) (shar s ev ready))
   (where (s_not ...) (Cannot_shared p (s)))
   (where #t (∈ s (s_not ...)))
   (where #t (∈ shared-status (old new)))
   ;; for speed
   (judgment-holds (stuck? p))
   (where #t (unprogressable (env-v_1 ...) p))
   readyness)

  ;; unshared state
  (-->
   (in-hole P* (var x := ev p))
   (add-new-var x ev (in-hole P* p))
   raise-var)
  (-->
   (env (env-v_1 ... (var· x ev_old) env-v_2 ...) (in-hole P (:= x ev_new)))
   (substitute* (env (env-v_1 ... (var· x ev_old) env-v_2 ...) (in-hole P nothing))
                (var· x ev_old) (var· x ev_new)))
  ;; if
  (--> (in-hole P* (if ev p q))
       (in-hole P* q)
       (side-condition `(∈ ev (#f 0)))
       if-false)
  (--> (in-hole P* (if ev p q))
       (in-hole P* p)
       (side-condition `(∉ ev (#f 0)))
       if-true)
  ;; evaling code
  (--> (in-hole E* (shar s ev ready)) (in-hole E* ev)
       eval-shared)
  (--> (in-hole E* (var· x ev)) (in-hole E* ev)
       eval-var)
  (--> (in-hole E* (f ev ...)) (in-hole E* (δ f ev ...))
       eval-δ)
  ))

(define-metafunction esterel-eval
  unprogressable : (env-v ...) p -> boolean
  [(unprogressable () p) #t]
  [(unprogressable ((var· x ev) env-v ...) p)
   (unprogressable (env-v ...) p)]
  [(unprogressable ((sig S status) env-v ...) p)
   (unprogressable (env-v ...) p)
   (where #t (∈ status (present absent)))]
  [(unprogressable ((sig S unknown) env-v ...) p)
   #t
   (where ⊥ (Cannot p (S)))
   (where #t (unprogressable (env-v ...) p))]
  [(unprogressable ((shar s ev ready) env-v ...) p)
   (unprogressable (env-v ...) p)]
  [(unprogressable ((shar s ev shared-status) env-v ...) p)
   #t
   (where ⊥ (Cannot_shared p (s)))
   (where #t (unprogressable (env-v ...) p))]
  [(unprogressable (env-v ...) p) #f])

(define-metafunction esterel-eval
  δ : f ev ... -> ev
  [(δ + ev ...) ,(apply + `(ev ...))]
  [(δ (rfunc any) ev ...) ,(apply `any `(ev ...))])

(define-metafunction esterel-eval
  harp : vp -> vp
  [(harp nothing) nothing]
  [(harp (exit 0)) nothing]
  [(harp (exit n)) (exit ,(sub1 `n))])

(define-metafunction esterel-eval
  add-new-signal : S p -> p
  [(add-new-signal S (env (env-v_1 ... (sig S status) env-v_2 ...) p))
   (env (env-v_1 ... (sig S unknown) env-v_2 ...)
        (substitute* (substitute* p (sig S status) (sig S unknown))
                     S (sig S unknown)))]
  [(add-new-signal S (env (env-v ...) p))
   (env (insert-into-env (sig S unknown) (env-v ...))
        (substitute* p S (sig S unknown)))])

(define-metafunction esterel-eval
  add-new-shared : s ev p -> p
  [(add-new-shared s ev (env (env-v_1 ... (shar s ev_old shared-status) env-v_2 ...) p))
   (env (env-v_1 ... (shar s ev new) env-v_2 ...)
        (substitute* (substitute* p (shar s ev_old shared-status) (shar s ev new))
                     s (shar s ev new)))]
  [(add-new-shared s ev (env (env-v ...) p))
   (env (insert-into-env (shar s ev new) (env-v ...))
        (substitute* p s (shar s ev new)))])

(define-metafunction esterel-eval
  add-new-var : x ev p -> p
  [(add-new-var x ev (env (env-v_1 ... (var· x ev_old) env-v_2 ...) p))
   (env (env-v_1 ... (var· x ev_old) env-v_2 ...)
        (substitute* (substitute* p (var· x ev_old) (var· x ev))
                     x (var· x ev)))]
  [(add-new-var x ev (env (env-v ...) p))
   (env (insert-into-env (var· x ev) (env-v ...))
        (substitute* p x (var· x ev)))])

(define-metafunction esterel-eval
  insert-into-env : env-v (env-v ...) -> (env-v ...)
  [(insert-into-env env-v (env-v_o ...))
   ,(sort
     `(env-v env-v_o ...)
     symbol<?
     #:key second)])

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
  [----------- "v"
   (stuck? v)]

  [----------- "pu"
   (stuck? (present (sig S unknown) p q))]

  [(stuck? p)
   ----------- "seq"
   (stuck? (seq p q))]

  [(stuck? p-not-v)
   ----------- "parl"
   (stuck? (par p-not-v v))]
  [(stuck? q-not-v)
   ----------- "parr"
   (stuck? (par v q-not-v))]
  [(stuck? p-not-v)
   (stuck? q-not-v)
   ----------- "para"
   (stuck? (par p-not-v q-not-v))]

  [(stuck? p)
   ----------
   (stuck? (suspend p Sdat))]

  [(stuck? p)
   ----------
   (stuck? (trap p))]

  [(stuck? p)
   ----------
   (stuck? (signal (Sdat ...) p))]

  [(stuck? p)
   -----------
   (stuck? (suspend^ p (sig S absent)))]
  [-----------
   (stuck? (suspend^ p (sig S unknown)))]
  [-----------
   (stuck? (suspend^ p (sig S present)))]

  [(stuck-e? e)
   ----------
   (stuck? (shared s := e p))]

  [(stuck-e? e)
   ----------
   (stuck? (<= s e))]

  [(stuck-e? e)
   ----------
   (stuck? (var x := e p))]

  [(stuck-e? e)
   ----------
   (stuck? (:= x e))]

  [(stuck-e? e)
   ----------
   (stuck? (if e p q))])

(define-judgment-form esterel-eval
  #:mode     (stuck-e? I)
  #:contract (stuck-e? e)
  [-----------
   (stuck-e? (shar s ev old))]
  [-----------
   (stuck-e? (shar s ev new))]
  [(stuck-e? e)
   ----------
   (stuck-e? (f ev ... e e_r ...))])

(define-metafunction esterel-eval
  instant : p (env-v ...) -> (p (any ...)) or #f
  [(instant p (env-v ...))
   (p_*
    (get-signals a))
   (where (a) ,(apply-reduction-relation* R `(setup p (env-v ...))))
   (where p_* (add-hats (clear-up-values a)))]
  [(instant p (env-v ...))
   #f
   (where (p_* ...) ,(apply-reduction-relation* R `(setup p (env-v ...))))
   (side-condition (pretty-print `(p_* ...)))])

(define-metafunction esterel-eval
  setup : p (env-v ...) -> p
  [(setup p
          ((sig S status) env-v ...))
   (setup (substitute* p (sig S unknown) (sig S status))
          (env-v ...))]
  [(setup p
          ((shar s ev shared-status) env-v ...))
   (setup (substitute* p (shar s ev_old old) (shar s ev shared-status))
          (env-v ...))
   (where
    (env (env-v_1 ... (shar s ev_old old) env-v_2 ...) p_*)
    p)]
  [(setup p ()) p])

(define-metafunction esterel-eval
  get-signals : p -> (S ...)
  [(get-signals (env ((sig S present) env-v ...) p))
   (S S_r ...)
   (where (S_r ...) (get-signals (env (env-v ...) p)))]
  [(get-signals (env (env-v env-v_r ...) p))
   (get-signals (env (env-v_r ...) p))]
  [(get-signals (env () p)) ()])

(define-metafunction esterel-eval
  add-hats : p -> p
  [(add-hats pause) nothing]
  [(add-hats nothing) nothing]
  [(add-hats (env (env-v ...) p)) (env (env-v ...) (add-hats p))]
  [(add-hats (seq p q)) (seq (add-hats p) q)]
  [(add-hats (par p q)) (par (add-hats p) (add-hats q))]
  [(add-hats (suspend p Sdat)) (suspend^ (add-hats p) Sdat)]
  [(add-hats (suspend^ p Sdat)) (suspend^ (add-hats p) Sdat)]
  [(add-hats (trap p)) (trap (add-hats p))]
  [(add-hats (exit n)) (exit n)])

(define-metafunction esterel-eval
  clear-up-values : p -> p
  [(clear-up-values (env (env-v ...) p))
   (env ((clear-up-env env-v) ...)
     (clear-up-values p))]
  [(clear-up-values nothing) nothing]
  [(clear-up-values pause) pause]
  [(clear-up-values (signal S p))
   (signal S (clear-up-values p))]
  [(clear-up-values (present Sdat p q))
   (present (clear-up-env Sdat) (clear-up-values p) (clear-up-values q))]
  [(clear-up-values (emit Sdat))
   (emit (clear-up-env Sdat))]
  [(clear-up-values (par p q))
   (par (clear-up-values p) (clear-up-values q))]
  [(clear-up-values (seq p q))
   (seq (clear-up-values p) (clear-up-values q))]
  [(clear-up-values (loop p))
   (loop (clear-up-values p))]
  [(clear-up-values (suspend p Sdat))
   (suspend (clear-up-values p) (clear-up-env Sdat))]
  [(clear-up-values (suspend^ p Sdat))
   (suspend^ (clear-up-values p) (clear-up-env Sdat))]
  [(clear-up-values (trap p))
   (trap (clear-up-values p))]
  [(clear-up-values (exit n)) (exit n)]
  [(clear-up-values (shared s := e p))
   (shared s := (clear-up-data e) (clear-up-values p))]
  [(clear-up-values (<= s e)) (<= s (clear-up-data e))]
  [(clear-up-values (var x := e p))
   (var x := (clear-up-data e) (clear-up-values p))]
  [(clear-up-values (:= x e)) (:= x (clear-up-data e))]
  [(clear-up-values (if e p q))
   (if (clear-up-data e)
       (clear-up-values p)
       (clear-up-values q))])

(define-metafunction esterel-eval
  clear-up-data : e -> e
  [(clear-up-data s) s]
  [(clear-up-data env-v)
   (clear-up-env env-v)]
  [(clear-up-data (f e ...))
   (f (clear-up-data e) ...)]
  [(clear-up-data x) x]
  [(clear-up-data natural) natural])

(define-metafunction esterel-eval
  ;clear-up-env : env-v -> env-v
  ;clear-up-env : S -> S
  [(clear-up-env S) S]
  [(clear-up-env (sig S status)) (sig S unknown)]
  [(clear-up-env (shar s ev shared-status)) (shar s ev old)]
  [(clear-up-env (var· x ev)) (var· x ev)])



(define-metafunction esterel-eval
  Cannot : p (S ...) -> (S ...) or ⊥
  [(Cannot p (S_o ...))
   (S_1 S_r ...)
   (where ((S ...) (n ...) (s ...))
          (Can p))
   (where (S_1 S_r ...)
          ,(filter (lambda (s) (not (member s `(S ...)))) `(S_o ...)))]
  [(Cannot p (S ...)) ⊥])

(define-metafunction esterel-eval
  Cannot_shared : p (s ...) -> (S ...) or ⊥
  [(Cannot_shared p (s_o ...))
   (s_1 s_r ...)
   (where ((S ...) (n ...) (s ...))
          (Can p))
   (where (s_1 s_r ...)
          ,(filter (lambda (x) (not (member x `(s ...)))) `(s_o ...)))]
  [(Cannot_shared p (s ...)) ⊥])

(define-metafunction esterel-eval
  Can : p -> ((S ...) (n ...) (s ...))

  [(Can nothing) (() (0) ())]

  [(Can pause) (() (1) ())]

  [(Can (exit n)) (() (,(+ 2 `n)) ())]

  [(Can (emit (sig S present))) ((S) (0) ())]
  [(Can (emit (sig S absent))) (() () ())]
  [(Can (emit (sig S unknown))) ((S) (0) ())]
  [(Can (emit S)) ((S) (0) ())]

  [(Can (present (sig S present) p q))
   (Can p)]

  [(Can (present (sig S absent) p q))
   (Can q)]

  [(Can (present Sdat p q))
   ((U (Can_S p) (Can_S q))
    (U (Can_K p) (Can_K q))
    (U (Can_shared p) (Can_shared q)))]

  [(Can (suspend p Sdat))
   (Can p)]

  [(Can (seq p q))
   (Can p)
   (side-condition `(∉ 0 (Can_K p)))]

  [(Can (seq p q))
   ( (U (Can_S p) (Can_S q))
     (U (without (Can_K p) 0)
        (Can_K q))
      (U (Can_shared p) (Can_shared q)))]

  [(Can (loop p))
   (Can p)]

  [(Can (par p q))
   ( (U (Can_S p) (Can_S q))
     (,(apply max (append `(Can_K p) `(Can_K q))))
     (U (Can_shared p) (Can_shared q)))]

  [(Can (trap p))
   ( (Can_S p)
     (harp... (Can_K p))
      (Can_shared p))]

  [(Can (signal S p))
   ((without (S_* ...) S) (n ...) (s ...))
   (where ((S_* ...) (n ...) (s ...)) (Can p))]

  [(Can (suspend^ p (S absent)))
   (Can p)]

  [(Can (suspend^ p (S present)))
   (() (1) ())]

  [(Can (suspend^ p Sdat))
   ((S_o ...) (1 n ...) (s ...))
   (where ((S_o ...) (n ...) (s ...)) (Can p))]

  [(Can (shared s := e p))
   ((Can_S p)
    (Can_K p)
    (without (Can_shared p) s))]
  [(Can (<= s e))
   (() (0) (s))]

  [(Can (var x := e p))
   (Can p)]
  [(Can (:= x e))
   (() (0) ())]
  [(Can (if e p q))
   ((U (Can_S p) (Can_S q))
    (U (Can_K p) (Can_K q))
    (U (Can_shared p) (Can_shared q)))])

(define-metafunction esterel-eval
  harp... : (n ...) -> (n ...)
  [(harp... (n ...))
   ((harp* n) ...)])

(define-metafunction esterel-eval
  harp* : n -> n
  [(harp* 0) 0]
  [(harp* 1) 1]
  [(harp* 2) 0]
  [(harp* n) ,(sub1 `n)])

(define-metafunction esterel-eval
  Can_S : p -> (S ...)
  [(Can_S p)
   (S ...)
   (where ((S ...) any_1 any_2) (Can p))])

(define-metafunction esterel-eval
  Can_K : p -> (n ...)
  [(Can_K p)
   (n ...)
   (where (any_1 (n ...) any_2) (Can p))])

(define-metafunction esterel-eval
  Can_shared : p -> (s ...)
  [(Can_shared p)
   (s ...)
   (where (any_1 any_2 (s ...)) (Can p))])

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
   ,(set->list
     (for*/set ([n1 (in-list `(n_1 ...))]
                [n2 (in-list `(n_2 ...))])
       (max n1 n2)))])

(module+ random-test
  (require
   (only-in (submod esterel/cos-model test) cc->>)
   (prefix-in cos: esterel/cos-model))

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
             (cos:c->> (machine ,(first p) ,(second p))
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
      (list p s))))

(module+ test
  (require (submod ".." random-test))
  (test-begin
    (check-equal?
     (apply-reduction-relation
      R
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
       R
       `(env ()
         (shared s := 1
                 pause)))))
    (check-true
     (redex-match?
      esterel-eval
      ((env ((shar s 5 new))
         nothing))
      (apply-reduction-relation
       R
       `(env ((shar s 1 old))
         (<= s 5)))))

    (check-true
     (redex-match?
      esterel-eval
      ((env ((shar s 6 new))
         nothing))
      (apply-reduction-relation
       R
       `(env ((shar s 1 new))
         (<= s 5)))))

    (check-true
     (redex-match?
      esterel-eval
      ((env ((shar s 1 ready))
         (shared s_2 := (shar s 1 ready)
                 pause)))
      (apply-reduction-relation
       R
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
       R
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
       R
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
       R
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
    (check-true
     (redex-match?
      esterel-eval p-not-v
      `(trap
        (suspend^ (seq nothing (loop pause)) (sig random-signal8013 unknown)))))
    (check-true
     (redex-match?
      esterel-eval p-not-v
      `(par (suspend^ nothing (sig random-signal15682 unknown)) nothing)))
    (test-case "random"
      (do-test #t))))

(module+ tracing
  (require redex
           (prefix-in cos: esterel/cos-model))
  (define-syntax-rule (render-derivations r)
    (show-derivations (build-derivations r)))
  (define (steps p)
    (traces R `(env () ,p))
    (render-derivations
     (cos:→* (machine (· (convert ,p)) ()) () (machine pbar any_1) any_2 any_3))))

#;
(define (render)
  #|
  (local-require unstable/gui/redex slideshow/text pict)
  (define (shar-rw lws)
    (match lws
      [(list open _ name value status close)
       (match* (name value status)
         [((lw n a b c d e f)
           (lw v _ _ _ _ _ _)
           (lw s _ _ _ _ _ _))
          (render-lw
           esterel-eval
           (lw
            (string->symbol (format "~a_~a^~a" v s n))
            a b c d e f))])]))
  #;
  (define (sig-rw lws)
    (match lws
      [(list open _ name status close)
       ]))
  (add-compound-rewriters!
   'shar shar-rw
   ;'sig  sig-rw
   )
  |#
  (parameterize ([rule-pict-style 'horizontal])
    (values
     (render-language esterel)
     (render-language esterel-eval)
     (render-reduction-relation R))))
