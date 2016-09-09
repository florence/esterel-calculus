#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))

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
     n
     ;; racket value
     any)
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
  (ev ::= n (rvalue any))

  ;; Values and answers
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
     (f ev ... E e ...)))


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

(define-metafunction esterel-eval
  setup : p (env-v ...) -> p
  [(setup p
          ((sig S status) env-v ...))
   (setup (substitute* p (sig S unknown) (sig S status))
          (env-v ...))]
  [(setup p
          ((shar s ev shared-status) env-v ...))
   (setup (substitute* p (shar s ev_old shared-status_old) (shar s ev shared-status))
          (env-v ...))
   (where
    (env (env-v_1 ... (shar s ev_old shared-status_old) env-v_2 ...) p_*)
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



(define-metafunction esterel-eval
  δ : f ev ... -> ev
  [(δ + ev ...) ,(apply + `(ev ...))]
  [(δ (rfunc any) ev ...) (rvalue ,(apply `any `(ev ...)))])

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

