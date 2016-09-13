#lang racket
(require redex/reduction-semantics "shared.rkt")
(provide (all-defined-out))

(define-syntax quasiquote (make-rename-transformer #'term))

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

  ;; stuck programs
  (unreducable ::= v blocked)
  (blocked ::=
           (present (sig S unknown) p q)
           (suspend^ p (sig S unknown))
           (seq blocked q)
           (par blocked v)
           (par v blocked)
           (par blocked blocked)
           (suspend^ blocked (sig S absent))
           (suspend blocked Sdat)
           (trap blocked)
           (shared s := blocked/e p)
           (var x := blocked/e p)
           (<= s blocked/e)
           (:= x blocked/e)
           (if blocked/e p q))
  (blocked/e ::=
                 (shar s ev new)
                 (shar s ev old)
                 (f ev ... blocked/e e ...))

  (A ::= (env (env-v ...) hole))
  (P* Q* ::= (in-hole A P))
  (E* ::= (in-hole A (in-hole P E)))

  ;; evaluation context
  (P Q ::=
     hole
     (seq P q)
     (par P q)
     (par unreducable Q)
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

  )

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
       (side-condition `(∈ ev ((rvalue #f) 0)))
       if-false)
  (--> (in-hole P* (if ev p q))
       (in-hole P* p)
       (side-condition `(∉ ev ((rvalue #f) 0)))
       if-true)
  ;; evaling code
  (--> (in-hole E* (shar s ev ready)) (in-hole E* ev)
       eval-shared)
  (--> (in-hole E* (var· x ev)) (in-hole E* ev)
       eval-var)
  (--> (in-hole E* (f ev ...)) (in-hole E* (δ f ev ...))
       eval-δ)
  ))



(define R*
  (extend-reduction-relation
   R
   esterel-eval
   (-->
    (env (env-v_1 ... (sig S unknown) env-v_2 ...) unreducable)
    (substitute* (env (env-v_1 ... (sig S unknown) env-v_2 ...) unreducable) (sig S unknown) (sig S absent))
    (where (S_not ...) (Cannot unreducable (S)))
    (where #t (∈ S (S_not ...)))
    ;; these are only here to make things run with decent speed
    (where #t (unprogressable (env-v_1 ...) unreducable))
    absence)
   (-->
   (env (env-v_1 ... (shar s ev shared-status) env-v_2 ...) unreducable)
   (substitute* (env (env-v_1 ... (shar s ev shared-status) env-v_2 ...) unreducable)
                (shar s ev shared-status) (shar s ev ready))
   (where (s_not ...) (Cannot_shared unreducable (s)))
   (where #t (∈ s (s_not ...)))
   (where #t (∈ shared-status (old new)))
   ;; for speed
   (where #t (unprogressable (env-v_1 ...) unreducable))
   readyness)))

(define-metafunction esterel-eval
  instant : p (env-v ...) -> (p (any ...)) or #f
  [(instant p (env-v ...))
   (p_*
    (get-signals a))
   (where (a) ,(apply-reduction-relation* R* `(setup p (env-v ...))))
   (where p_* (add-hats (clear-up-values a)))]
  [(instant p (env-v ...))
   #f
   (where (p_* ...) ,(apply-reduction-relation* R* `(setup p (env-v ...))))
   (side-condition (pretty-print `(p_* ...)))])

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
