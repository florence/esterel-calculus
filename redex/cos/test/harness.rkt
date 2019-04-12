#lang racket
(require redex/reduction-semantics racket/random
         esterel-calculus/redex/cos/model)
(provide (all-defined-out))
(require rackunit (prefix-in rackunit: rackunit))
(define (do t [E `()] [data `()])
  (judgment-holds (non-det-> ,t ,data ,E
                             pdotdot data_* e k)
                  (pdotdot e k data_*)))
(define (do/det t [E `()] [data `()])
  (judgment-holds (det-> ,t ,data ,E
                         pdotdot data_* e k)
                  (pdotdot e k data_*)))
(define-syntax-rule (do* p data)
  (judgment-holds (non-det-> p data ()
                             pdotdot_* data_* e k)
                  (pdotdot_* data_* e k)))

(define-extended-language esterel-check esterel-eval
  (p-check
   nothing
   pause
   (seq p-check p-check)
   (par p-check p-check)
   (trap p-check)
   (exit nat)
   (signal S p-check)
   (suspend p-check S)
   (present S p-check p-check)
   (emit S)
   (shared s := call/check p-check+sset)
   (var v := call/check p-check+vset))

  (p-check+sset
   p-check
   (seq p-check+sset p-check+sset)
   (par p-check+sset p-check+sset)
   (trap p-check+sset)
   (exit nat)
   (signal S p-check+sset)
   (suspend p-check+sset S)
   (present S p-check+sset p-check+sset)
   (var v := call/check p-check+sset+vset)
   (<= s call/check))

  (p-check+vset
   p-check
   (seq p-check+vset p-check+vset)
   (par p-check+vset p-check)
   (trap p-check+vset)
   (exit nat)
   (signal S p-check+vset)
   (suspend p-check+vset S)
   (present S p-check+vset p-check+vset)

   (shared s := call/check p-check+sset+vset)
   (:= v call/check))

  (p-check+sset+vset
   p-check+vset
   p-check+sset)

  (phat-check
   (hat pause)
   ;; loops only present here to force loops to be non-instantanious
   (loop phat-check)
   (suspend phat-check S)
   (seq phat-check p-check)
   (seq p-check phat-check)
   ;; force a phat for the sake of loop safety
   (present S phat-check phat-check)
   (par phat-check phat-check)
   (trap phat-check)
   (signal S phat-check)
   (shared s := call/check phat-check+sset))
  (phat-check+sset
   phat-check
   (loop phat-check+sset)
   (suspend phat-check+sset S)
   (seq phat-check+sset p-check+sset)
   (seq p-check+sset phat-check+sset)
   ;; force a phat for the sake of loop safety
   (present S phat-check+sset phat-check+sset)
   (par phat-check+sset phat-check+sset)
   (trap phat-check+sset)
   (signal S phat-check+sset))
  (pbar-check p-check phat-check)

  (NL ()
      (nat NL))

  (call/check (+ call/check  call/check ) (+ call/check ) (+) v s  natural))

(define-judgment-form esterel-eval
  ;; constructive ->>, with testing checks
  #:mode     (cc->> I I O O       O)
  #:contract (cc->> M E M (S ...) k)
  [(where (((machine qbar_r data_r*) (S_r ...) k_r) ...)
          ,(judgment-holds
            (c->> (machine pbar data) E (machine qbar data_*) (S ...) k)
            ((machine qbar data_*) (S ...) k)))
   (where (M_* (S_* ...)) (eval (machine pbar data) E))
   (where (((machine qbar data_*) (S ...) k) any_2 ...)
          (((machine qbar_r data_r*) (S_r ...) k_r) ...))
   (where #t ,(andmap (curry equal? `k)
                      `(k_r ...)))
   (where #t ,(andmap (lambda (M) (alpha-equivalent? esterel-eval `(machine qbar data_*) M))
                      `(M_* (machine qbar_r data_r*) ...)))
   ;(side-condition ,(displayln `(S_* ... S ... (free-emitted-signals pbar))))
   ;(side-condition ,(displayln `((∈ S (free-emitted-signals pbar)) ...)))
   (where (#t ...) ((∈ S_* (free-emitted-signals pbar)) ...
                    (∈ S (free-emitted-signals pbar)) ...))
   (where E_2 (Can_S pbar E))
   ;(side-condition ,(displayln `((S one) ... E_2)))
   ;(side-condition ,(displayln `((∈ (S one) E_2) ...)))
   (where (#t ...) ((∈ (S_* (Succ zero)) E_2) ...
                    (∈ (S (Succ zero)) E_2) ...))
   (where #t
          ,(for*/and ([Sl1 (in-list `((S_* ...) (S_r ...) ...))]
                      [Sl2 (in-list `((S_* ...) (S_r ...) ...))])
             (equal? (list->set Sl1) (list->set Sl2))))
   (bars-match qbar k)
   -------
   (cc->> (machine pbar data) E (machine qbar data_*) (S ...) k)])


(define-judgment-form esterel-eval
  #:mode (bars-match I I)
  #:contract (bars-match pbar k)
  [-------
   (bars-match p zero)]
  [-------
   (bars-match phat (Succ zero))])

(define-metafunction esterel-eval
  random-E : (S ...) -> E
  [(random-E (S ...))
   ((random-E_S S) ...)])

(define-metafunction esterel-eval
  random-E_S : S -> (S k)
  [(random-E_S S)
   (S ,(if (> (random) 0.5) `zero `(Succ zero)))])

(define-judgment-form esterel-eval
  #:mode (->*/final I I O O O)
  [(→* (machine pdotdot data) E (machine qdotdot data_*) (S ...) k)
   (where #f ,(judgment-holds (→ qdotdot data E _ _ _ _)))
   -------------
   (->*/final (machine pdotdot data) E (machine qdotdot data_*) (S ...) k)])

(define-judgment-form esterel-check
  #:mode (traps-okay I I)
  #:contract (traps-okay pbar NL)

  [(traps-okay (exit nat_h) NL)
   -----------
   (traps-okay (exit nat_h) (nat_h NL))]

  [-----------
   (traps-okay (exit nat_h) (nat_h NL))]

  [(traps-okay pbar ((Succ (Succ zero)) ()))
   ----------
   (traps-okay (trap pbar) ())]

  [(traps-okay pbar ((Succ nat) (nat NL)))
   ----------
   (traps-okay (trap pbar) (nat NL))]

  [(traps-okay pbar NL)
   ---------
   (traps-okay (loop pbar) NL)]

  [---------
   (traps-okay nothing any)]

  [---------
   (traps-okay pause any)]

  [---------
   (traps-okay (hat pause) any)]

  [---------
   (traps-okay (emit S) any)]

  [(traps-okay pbar_l NL)
   (traps-okay pbar_r NL)
   ---------
   (traps-okay (seq pbar_l pbar_r) NL)]

  [(traps-okay pbar_l NL)
   (traps-okay pbar_r NL)
   ---------
   (traps-okay (present S pbar_l pbar_r) NL)]

  [(traps-okay pbar_l NL)
   (traps-okay pbar_r NL)
   ---------
   (traps-okay (par pbar_l pbar_r) NL)]

  [(traps-okay pbar NL)
   ---------
   (traps-okay (signal S pbar) NL)]

  [(traps-okay pbar NL)
   ---------
   (traps-okay (suspend pbar S) NL)]

  [(traps-okay pbar NL)
   ---------
   (traps-okay (shared s := call pbar) NL)]

  [(traps-okay pbar NL)
   ---------
   (traps-okay (var v := call pbar) NL)]

  [---------
   (traps-okay (<= s call) NL)]

  [---------
   (traps-okay (:= v call) NL)]

  [(traps-okay pbar NL)
   (traps-okay qbar NL)
   ---------
   (traps-okay (if v pbar qbar) NL)])

(define-judgment-form esterel-check
  #:mode (loops-okay I)
  #:contract (loops-okay pbar)
  [-----------
   (loops-okay (exit nat_h))]

  [-----------
   (loops-okay (exit nat_h))]

  [(loops-okay pbar)
   ----------
   (loops-okay (trap pbar))]

  [---------
   (loops-okay nothing)]

  [---------
   (loops-okay pause)]

  [---------
   (loops-okay (hat pause))]

  [---------
   (loops-okay (emit S))]

  [(loops-okay pbar_l)
   (loops-okay pbar_r)
   ---------
   (loops-okay (seq pbar_l pbar_r))]

  [(loops-okay pbar_l)
   (loops-okay pbar_r)
   ---------
   (loops-okay (present S pbar_l pbar_r))]

  [(loops-okay pbar_l)
   (loops-okay pbar_r)
   ---------
   (loops-okay (par pbar_l pbar_r))]

  [(loops-okay pbar)
   ---------
   (loops-okay (signal S pbar))]

  [(loops-okay pbar)
   ---------
   (loops-okay (suspend pbar S))]

  [(loops-okay pbar)
   (K_s pbar (k ...))
   (where #f (∈ zero (k ...)))
   ---------
   (loops-okay (loop pbar))]
  )
(define-judgment-form esterel-check
  #:mode (K_s I O)
  #:contract (K_s pbar (k ...))
  [----------
   (K_s nothing (zero))]
  [----------
   (K_s pause ((Succ zero)))]
  [----------;; identical. we're pretending its a p
   (K_s (hat pause) ((Succ zero)))]
  [----------
   (K_s (exit k) (k))]

  [(K_s pbar (k_1 ...))
   (K_s qbar (k_2 ...))
   ----------
   (K_s (present S pbar qbar) (U (k_2 ...) (k_2 ...)))]
  [(K_s pbar (k ...))
   ----------
   (K_s (suspend S pbar) (k ...))]
  [(K_s pbar (k_1 ...))
   (K_s qbar (k_2 ...))
   (where #t (∈ 0 (k_1 ...)))
   ----------
   (K_s (seq pbar qbar) (U (k_2 ...) (without zero (k_1 ...))))]
  [(K_s pbar (k ...))
   (where #f (∈ 0 (k ...)))
   ----------
   (K_s (seq pbar qbar) (k ...))]
  [(K_s pbar (k ...))
   ----------
   (K_s (loop pbar) (without zero (k ...)))]
  [(K_s pbar (k_1 ...))
   (K_s qbar (k_2 ...))
   ----------
   (K_s (seq pbar qbar) (metamax (k_2 ...) (k_1 ...)))]
  [(K_s pbar (k ...))
   ----------
   (K_s (trap pbar) (↓ (k ...)))]
  [(K_s pbar (k ...))
   ----------
   (K_s (suspend S pbar) (k ...))])
(define-metafunction esterel-eval
  fix-env : M -> M

  [(fix-env (machine (exit nat_h) data))
   (machine (exit nat_h) data)]

  [(fix-env (machine pause data))
   (machine pause data)]

  [(fix-env (machine (hat pause) data))
   (machine (hat pause) data)]

  [(fix-env (machine nothing data))
   (machine nothing data)]

  [(fix-env (machine (emit S) data))
   (machine (emit S) data)]

  [(fix-env (machine (trap pbar) data))
   (machine (trap pbar_*) data_*)
   (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

  [(fix-env (machine (loop pbar) data))
   (machine (loop pbar_*) data_*)
   (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

  [(fix-env (machine (signal S pbar) data))
   (machine (signal S pbar_*) data_*)
   (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

  [(fix-env (machine (suspend pbar S) data))
   (machine (suspend pbar_* S) data_*)
   (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

  [(fix-env (machine (seq pbar qbar) data))
   (machine (seq pbar_* qbar_*) (U data_* data_**))
   (where (machine pbar_* data_*) (fix-env (machine pbar data)))
   (where (machine qbar_* data_**) (fix-env (machine qbar data)))]

  [(fix-env (machine (par pbar qbar) data))
   (machine (par pbar_* qbar_*) (U data_* data_**))
   (where (machine pbar_* data_*) (fix-env (machine pbar data)))
   (where (machine qbar_* data_**) (fix-env (machine qbar data)))]

  [(fix-env (machine (present S pbar qbar) data))
   (machine (present S pbar_* qbar_*) (U data_* data_**))
   (where (machine pbar_* data_*) (fix-env (machine pbar data)))
   (where (machine qbar_* data_**) (fix-env (machine qbar data)))]

  [(fix-env (machine (shared s := call phat) data))
   (machine (shared s := call_* phat_*) data_**)
   (where call_* (delete-bad-var-call s data call))
   (where data_* (data<- data s (eval-call call_* data) ready))
   (where (machine phat_* data_**) (fix-env (machine phat data_*)))]

  [(fix-env (machine (shared s := call p) data))
   (machine (shared s := call_* p_*) data_**)
   (where call_* (delete-bad-var-call s data call))
   (where data_* (data<- data s (eval-call call_* data) old))
   (where (machine p_* data_**) (fix-env (machine p data_*)))]

  [(fix-env (machine (<= s call) data))
   (machine (<= s_* call_*) data)
   (where s_* (visible-s s data))
   (where call_* (delete-bad-var-call s_* data call))]

  [(fix-env (machine (var v := call pbar) data))
   (machine (var v := call_* pbar_*) data_**)
   (where call_* (delete-bad-var-call ,(gensym) data call))
   (where data_* (data<- data v (eval-call call_* data)))
   (where (machine pbar_* data_**) (fix-env (machine pbar data_*)))]

  [(fix-env (machine (:= v call) data))
   (machine (:= v_* call_*) data)
   (where v_* (visible-v v data))
   (where call_* (delete-bad-var-call ,(gensym) data call))]

  [(fix-env (machine (if v pbar qbar) data))
   (machine (if v_* pbar_* qbar_*) (U data_* data_**))
   (where v_* (delete-bad-var-call ,(gensym) data v))
   (where (machine pbar_* data_*) (fix-env (machine pbar data)))
   (where (machine qbar_* data_**) (fix-env (machine qbar data)))])

(define-metafunction esterel-eval
  visible-s : s data -> s
  [(visible-s s data)
   s
   (where #t (∈ s (get-shared data)))]
  [(visible-s s data) (get-random-s data)])

(define-metafunction esterel-eval
  visible-v : v data -> v
  [(visible-v v data)
   s
   (where #t (∈ v (get-shared data)))]
  [(visible-v v data) (get-random-v data)])


(define-metafunction esterel-eval
  get-shared : data -> (s ...)
  [(get-shared ()) ()]
  [(get-shared ((dshared s any_1 any_2) data-elem ...))
   (s s_r ...)
   (where (s_r ...) (get-shared (data-elem ...)))]
  [(get-shared ((dvar any_1 any_2) data-elem ...))
   (get-shared (data-elem ...))])

(define-metafunction esterel-eval
  get-random-s : data -> s
  [(get-random-s data)
   ,(random-ref `(s ...))
   (where (s ...) (get-shared data))])

(define-metafunction esterel-eval
  get-random-v : data -> s
  [(get-random-v data)
   ,(random-ref `(v ...))
   (where (v ...) (get-unshared data))])

(define-metafunction esterel-eval
  get-unshared : data -> (v ...)
  [(get-unshared ()) ()]
  [(get-unshared ((dvar v any) data-elem ...))
   (v v_r ...)
   (where (v_r ...) (get-unshared (data-elem ...)))]
  [(get-unshared (any data-elem ...))
   (v_r ...)
   (where (v_r ...) (get-unshared (data-elem ...)))])

(define-metafunction esterel-eval
  delete-bad-var-call : s data call -> call
  [(delete-bad-var-call s data (+ call ...))
   (+ (delete-bad-var-call s data call) ...)]
  [(delete-bad-var-call s data s) 1]
  [(delete-bad-var-call s_0 data s_1)
   s_1
   (where #t (∈ s_1 (get-shared data)))]
  [(delete-bad-var-call s_0 data s_1) 1]
  [(delete-bad-var-call s data datum) datum])

(define-extended-language uniquify-lang esterel-eval
  #:binding-forms
  (shared s := call pbar #:refers-to s)
  (var v := call pbar #:refers-to v))
(define-metafunction uniquify-lang
  ;uniquify : pbar -> pbar
  [(uniquify (any ...))
   ((uniquify any) ...)]
  [(uniquify any) any])

(define-judgment-form esterel-check
  #:mode     (okay I)
  #:contract (okay pbar)
  [(traps-okay pbar ())
   --------
   (okay pbar)])