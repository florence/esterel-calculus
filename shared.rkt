#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))
(module+ test (require rackunit))

(define-syntax quasiquote (make-rename-transformer #'term))

(define-language esterel
  ((p q)
   nothing
   (signal S p)
   (present S p q)
   (emit S)
   (par p q)
   (loop p)
   pause
   (seq p q)
   (suspend p S)
   (trap p)
   (exit n)
   ;; state
   (shared s := e p)
   (<= s e)
   (var x := e p)
   (:= x e)
   (if e p q))

  (S s x ::= variable-not-otherwise-mentioned)
  (n ::= natural)

  (e ::=
     (f e ...)
     n
     s x
     ;; racket value
     (rvalue any))
  (f ::= + (rfunc any)))

(define-extended-language esterel-eval esterel
  (p q ::= ....
     (ρ θ. p))
  (θ. (env-v ...))
  (env-v ::= Sdat shareddat vardat)
  (status ::= present absent unknown)
  (Sdat ::= (sig S status))

  ;; state
  (shared-status ::= ready old new)
  (shareddat ::= (shar s ev shared-status))
  (vardat ::= (var· x ev))
  (ev ::= n (rvalue any))

  ;; Values and answers
  (complete ::= done (ρ θ./c done))
  (θ./c ::=
        (env-v/c ...))
  (env-v/c ::=
           vardat
           (shar s ev ready)
           (sig S present)
           (sig S absent))
  (done ::= halted paused)
  (halted ::= nothing (exit n))
  (paused ::=
      pause
      (seq paused q)
      (par paused paused)

      (suspend paused S)
      (trap paused))

  (C ::=
     hole

     (ρ θ. C)

     (seq C q)
     (seq q C)
     (par C q)
     (par p C)
     (suspend C S)
     (trap C)
     (present S C q)
     (present S p C)

     (shared s := C p)
     (shared s := e C)
     (var x := C p)
     (var x := e C)
     (<= s C)
     (:= x C)
     (if C p q)
     (if e C q)
     (if e p C)
     (f e ... C e ...))

  ;; evaluation contexts
  (E ::=
       hole
       (seq E q)
       (par E q)
       (par p E)
       (suspend E S)
       (trap E)
       (shared s := E p)
       (var x := E p)
       (<= s E)
       (:= x E)
       (if E p q)
       (f ev ... E e ...)))

#;
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
  (ap ::= (in-hole A halted))
  (a* ::= (in-hole A paused))
  (v ::= halted paused)
  (halted ::= nothing (exit n))
  (paused ::=
      pause
      (seq paused q)
      (par paused paused)
      (suspend^ p (sig S present))
      (suspend^ paused Sdat)
      (suspend paused Sdat)
      (trap paused))

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
   value-max : done done -> done
  [(value-max nothing done) done]
  [(value-max done nothing) done]
  [(value-max (exit n_1) (exit n_2)) (exit ,(max `n_1 `n_2))]
  [(value-max (exit n) paused) (exit n)]
  [(value-max paused (exit n)) (exit n)])

(define-metafunction esterel-eval
  setup : p θ. -> p
  [(setup (ρ θ. p)
          θ._2)
   (ρ (<- θ. θ._2) p)])

(define-metafunction esterel-eval
  add-hats : p -> p
  [(add-hats pause) nothing]
  [(add-hats nothing) nothing]
  [(add-hats (ρ θ. p)) (ρ θ. (add-hats p))]
  [(add-hats (seq p q)) (seq (add-hats p) q)]
  [(add-hats (par p q)) (par (add-hats p) (add-hats q))]
  [(add-hats (suspend p S)) (suspend (seq (present S pause nothing) (add-hats p)) S)]
  [(add-hats (trap p)) (trap (add-hats p))]
  [(add-hats (exit n)) (exit n)])

(define-metafunction esterel-eval
  clear-up-values : p -> p
  [(clear-up-values (ρ θ. p))
   (ρ (clear-up-enpaused θ.) (clear-up-values p))]
  [(clear-up-values nothing) nothing]
  [(clear-up-values pause) pause]
  [(clear-up-values (signal S p))
   (signal S (clear-up-values p))]
  [(clear-up-values (present S p q))
   (present S (clear-up-values p) (clear-up-values q))]
  [(clear-up-values (emit S))
   (emit S)]
  [(clear-up-values (par p q))
   (par (clear-up-values p) (clear-up-values q))]
  [(clear-up-values (seq p q))
   (seq (clear-up-values p) (clear-up-values q))]
  [(clear-up-values (loop p))
   (loop (clear-up-values p))]
  [(clear-up-values (suspend p S))
   (suspend (clear-up-values p) S)]
  [(clear-up-values (trap p))
   (trap (clear-up-values p))]
  [(clear-up-values (exit n)) (exit n)]
  [(clear-up-values (shared s := e p))
   (shared s := e (clear-up-values p))]
  [(clear-up-values (<= s e)) (<= s e)]
  [(clear-up-values (var x := e p))
   (var x := e (clear-up-values p))]
  [(clear-up-values (:= x e)) (:= x e)]
  [(clear-up-values (if e p q))
   (if e
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
  clear-up-enpaused : θ. -> θ.
  [(clear-up-enpaused (env-v ...))
   ((clear-up-env env-v) ...)])

(define-metafunction esterel-eval
  clear-up-env : env-v -> env-v
  [(clear-up-env S) S]
  [(clear-up-env (sig S status)) (sig S unknown)]
  [(clear-up-env (shar s ev shared-status)) (shar s ev old)]
  [(clear-up-env (var· x ev)) (var· x ev)])

(define-metafunction esterel-eval
  Cannot : p (S ...) -> (S ...) or ⊥
  [(Cannot p (S_o ...))
   (S_1 S_r ...)
   (where ((S ...) (n ...) (s ...))
          (Can p ()))
   (where (S_1 S_r ...)
          ,(filter (lambda (s) (not (member s `(S ...)))) `(S_o ...)))]
  [(Cannot p (S ...)) ⊥])

(define-metafunction esterel-eval
  Cannot_shared : p (s ...) -> (S ...) or ⊥
  [(Cannot_shared p (s_o ...))
   (s_1 s_r ...)
   (where ((S ...) (n ...) (s ...))
          (Can p ()))
   (where (s_1 s_r ...)
          ,(filter (lambda (x) (not (member x `(s ...)))) `(s_o ...)))]
  [(Cannot_shared p (s ...)) ⊥])

(define-metafunction esterel-eval
  Can : p θ. -> ((S ...) (n ...) (s ...))

  [(Can (ρ θ._1 p) θ.)
   (Can p (<- θ. θ._1))]

  [(Can nothing θ.) (() (0) ())]

  [(Can pause θ.) (() (1) ())]

  [(Can (exit n) θ.) (() (,(+ 2 `n)) ())]

  [(Can (emit S) θ.) ((S) (0) ())]

  [(Can (present S p q) (env-v_0 ... (sig S present) env-v_2 ...))
   (Can p (env-v_0 ... (sig S present) env-v_2 ...))]
  [(Can (present S p q) (env-v_0 ... (sig S absent) env-v_2 ...))
   (Can q (env-v_0 ... (sig S absent) env-v_2 ...))]

  [(Can (present S p q) θ.)
   ((U (Can_S p θ.) (Can_S q θ.))
    (U (Can_K p θ.) (Can_K q θ.))
    (U (Can_shared p θ.) (Can_shared q θ.)))]

  [(Can (suspend p S) θ.)
   (Can p θ.)]

  [(Can (seq p q) θ.)
   (Can p θ.)
   (where #t (∉ 0 (Can_K p θ.)))]

  [(Can (seq p q) θ.)
   ( (U (Can_S p θ.) (Can_S q θ.))
     (U (without (Can_K p θ.) 0)
        (Can_K q θ.))
      (U (Can_shared p θ.) (Can_shared q θ.)))]

  [(Can (loop p) θ.)

   (Can p θ.)]

  [(Can (par p q) θ.)
   ( (U (Can_S p θ.) (Can_S q θ.))
     (,(apply max (append `(Can_K p θ.) `(Can_K q θ.))))
     (U (Can_shared p θ.) (Can_shared q θ.)))]

  [(Can (trap p) θ.)
   ( (Can_S p θ.)
     (harp... (Can_K p θ.))
      (Can_shared p θ.))]

  [(Can (signal S p) θ.)
   ((without (S_* ...) S) (n ...) (s ...))
   (where ((S_* ...) (n ...) (s ...)) (Can p (<- θ. (sig S unknown))))]

  [(Can (shared s := e p) θ.)
   ((Can_S p θ.)
    (Can_K p θ.)
    (without (Can_shared p θ.) s))]
  [(Can (<= s e) θ.)
   (() (0) (s))]

  [(Can (var x := e p) θ.)
   (Can p θ.)]
  [(Can (:= x e) θ.)
   (() (0) ())]
  [(Can (if e p q) θ.)
   ((U (Can_S p θ.) (Can_S q θ.))
    (U (Can_K p θ.) (Can_K q θ.))
    (U (Can_shared p θ.) (Can_shared q θ.)))])

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
  Can_S : p θ. -> (S ...)
  [(Can_S p θ.)
   (S ...)
   (where ((S ...) any_1 any_2) (Can p θ.))])

(define-metafunction esterel-eval
  Can_K : p θ. -> (n ...)
  [(Can_K p θ.)
   (n ...)
   (where (any_1 (n ...) any_2) (Can p θ.))])

(define-metafunction esterel-eval
  Can_shared : p θ. -> (s ...)
  [(Can_shared p θ.)
   (s ...)
   (where (any_1 any_2 (s ...)) (Can p θ.))])

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
  U : (any ...) ... -> (any ...)
  [(U (any ...) ...)
   ,(set->list (list->set `(any ... ...)))])

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
  harp : halted -> halted
  [(harp nothing) nothing]
  [(harp (exit 0)) nothing]
  [(harp (exit n)) (exit ,(sub1 `n))])

(define-metafunction esterel-eval
  get-signals : p -> (S ...)
  [(get-signals (ρ θ. p))
   (get-signals* θ.)]
  [(get-signals p) ()])
(define-metafunction esterel-eval
  get-signals* : θ. -> (S ...)
  [(get-signals* θ.) (get-signals-of-status θ. present)])

(define-metafunction esterel-eval
  get-unknown-signals : θ. -> (S ...)
  [(get-unknown-signals θ.)
   (get-signals-of-status θ. unknown)])

(define-metafunction esterel-eval
  get-signals-of-status : θ. status -> (S ...)
  [(get-signals-of-status  ((sig S status) env-v ...) status)
   (S S_r ...)
   (where (S_r ...) (get-signals-of-status (env-v ...) status))]
  [(get-signals-of-status  (env-v_h env-v ...) status)
   (get-signals-of-status (env-v ...) status)]
  [(get-signals-of-status  () status)
   ()])

(define-metafunction esterel-eval
  set-all-absent : θ. (S ...) -> θ.
  [(set-all-absent θ. ()) θ.]
  [(set-all-absent (env-v_0 ... (sig S unknown) env-v_2 ...) (S S_r ...))
   (set-all-absent (env-v_0 ... (sig S absent) env-v_2 ...) (S_r ...))])

(define-metafunction esterel-eval
  get-unready-shared : θ. -> (s ...)
  [(get-unready-shared  ((shar s ev shared-status) env-v ...))
   (s s_r ...)
   (where #t (∈ shared-status (new old)))
   (where (s_r ...) (get-unready-shared (env-v ...)))]
  [(get-unready-shared (env-v_h env-v ...))
   (get-unready-shared (env-v ...))]
  [(get-unready-shared ())
   ()])

(module+ test
  (check-equal?
   `(get-unready-shared ((sig Ib absent)
                         (sig d absent)
                         (sig l absent)
                         (shar random-shared766092 0 new)
                         (sig random-signal766091 absent)))
   '(random-shared766092)))

(define-metafunction esterel-eval
  set-all-ready : θ. (s ...) -> θ.
  [(set-all-ready θ. ()) θ.]
  [(set-all-ready (env-v_0 ... (shar s ev shared-status) env-v_2 ...) (s s_r ...))
   (set-all-ready (env-v_0 ... (shar s ev ready) env-v_2 ...) (s_r ...))])

(module+ test
  (check-equal?
   `(set-all-ready ((shar random-shared934658 0 ready)) ())
   '((shar random-shared934658 0 ready))))

(define-metafunction esterel-eval
  ;<- : θ. env-v -> θ.
  ;<- : θ. θ. -> θ.
  [(<- (env-v_0 ... (var· x ev_old) env-v_1 ...) (var· x ev_new))
   (env-v_0 ... (var· x ev_new) env-v_1 ...)]
  [(<- (env-v_0 ... (shar s ev_old shared-status_old) env-v_1 ...)
       (shar s ev_new shared-status_new))
   (env-v_0 ... (shar s ev_new shared-status_new) env-v_1 ...)]
  [(<- (env-v_0 ... (sig S status_old) env-v_1 ...) (sig S status_new))
   (env-v_0 ... (sig S status_new) env-v_1 ...)]
  [(<- θ. env-v) (insert θ. env-v)]
  [(<- θ. ()) θ.]
  [(<- θ. (env-v_h env-v_r ...))
   (<- (<- θ. env-v_h) (env-v_r ...))])

(define-metafunction esterel-eval
  insert : θ. env-v -> θ.
  [(insert θ. env-v)
   ,(sort
     (cons `env-v `θ.)
     symbol<?
     #:key second)])

(define-metafunction esterel-eval
  FV : e -> (s ...)
  [(FV ev) ()]
  [(FV s) (s)]
  [(FV (f e ...))
   (U (FV e) ...)])
