#lang racket
(require redex/reduction-semantics "shared.rkt")
(provide (all-defined-out))

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
  (ap ::= (env (env-v ...) vp))
  (a* ::= (env (env-v ...) v*))
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

  ;; evaluation contexts
  (C ::=
     hole

     (env (env-v ...) C)

     (seq C q)
     (seq q C)
     (par C q)
     (par p C)
     (suspend C Sdat)
     (suspend^ C (sig S absent))
     (trap C)

     (shared s := C p)
     (var x := C p)
     (<= s C)
     (:= x C)
     (if C p q)
     (f e ... C e ...))

  ;; special evaluation contexts
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


(define R
  ;; ASSUMPTIONS:
  ;; program is loop safe
  (reduction-relation
   esterel-eval #:domain p
   ;; TODO reducing on nothings?
   (--> (in-hole C (par vp v)) (in-hole C (value-max vp v))
        par-done-right)
   (--> (in-hole C (par v vp)) (in-hole C (value-max v vp))
        par-done-left)

   ;; TODO can only really do in evaluation contexts ...
   (--> (in-hole C (present (sig S present) p q)) (in-hole C p)
    is-present)
   (--> (in-hole C (present (sig S absent) p q)) (in-hole C q)
    is-absent)

   (--> (in-hole C (in-hole P (emit Sdat)))
        (in-hole C (par (emit Sdat) (in-hole P nothing))))
   (-->
    (in-hole A (emit (sig S unknown)))
    (substitute* (in-hole C nothing) (sig S unknown) (sig S present))
    emit-unknown)
   (--> (in-hole A (emit (sig S present))) (in-hole C nothing)
        emit-present)

   (--> (in-hole C (loop p)) (in-hole C (seq p (loop p)))
    loop)
   (--> (in-hole C (seq nothing q)) (in-hole C q)
    seq-done)
   (--> (in-hole C (seq (exit n) q)) (in-hole C (exit n))
    seq-exit)
   (--> (in-hole C (suspend vp Sdat)) (in-hole C vp)
    suspend-value)
   (--> (in-hole C (suspend^ vp (sig S absent))) (in-hole C vp)
    suspend^-value)
   ;; traps
   (--> (in-hole C (trap vp)) (in-hole C (harp vp))
        trap-done)
   ;; lifting signals
   (--> (in-hole C (in-hole P (signal S p)))
        (in-hole C (signal S (in-hole P p))))
   (--> (in-hole A (signal S p))
        (add-new-signal S (in-hole A p))
        raise-signal)

   ;; shared state
   (-->
    (in-hole C (in-hole P (shared s := ev p)))
    (in-hole C (shared s := ev (in-hole P p)))))
   (-->
    (in-hole A (shared s := ev p))
    (add-new-shared s ev (in-hole A p))
    raise-shared)

   (--> (in-hole C (in-hole P (<= s e)))
        (in-hole C (par (<= s e) (in-hole P nothing))))
   ;; TODO C doesn't work here, need's E like context
   (-->
    (env (env-v_1 ... (shar s any old)  env-v_2 ...) (in-hole C (<= s ev)))
    (substitute* (env (env-v_1 ... (shar s any old) env-v_2 ...) (in-hole C nothing))
                 (shar s any old) (shar s ev new))
    set-shared-value-old)

   (-->
    (env (env-v_1 ... (shar s ev_o new) env-v_2 ...) (in-hole C (<= s ev_n)))
    (substitute* (env (env-v_1 ... (shar s ev_o new) env-v_2 ...) (in-hole C nothing))
                 (shar s ev_o new) (shar s (δ + ev_o ev_n) new))
    set-value-new)

  ;; unshared state
   (--> (in-hole C (in-hole P (:= x e)))
        (in-hole C (seq (:= x e) (in-hole P nothing))))
  (-->
   (in-hole A (var x := ev p))
   (add-new-var x ev (in-hole A p))
   raise-var)

   ;; TODO C doesn't work here, need's E like context
  (-->
   (env (env-v_1 ... (var· x ev_old) env-v_2 ...) (in-hole C (:= x ev_new)))
   (substitute* (env (env-v_1 ... (var· x ev_old) env-v_2 ...) (in-hole C nothing))
                (var· x ev_old) (var· x ev_new)))
  ;; if
  (--> (in-hole C (if ev p q))
       (in-hole C q)
       (side-condition `(∈ ev (#f 0)))
       if-false)
  (--> (in-hole C (if ev p q))
       (in-hole C p)
       (side-condition `(∉ ev ((rvalue #f) 0)))
       if-true)
  ;; evaling code
  ;; TODO can only really do in evaluation contexts ...
  (--> (in-hole C (shar s ev ready)) (in-hole E* ev)
       eval-shared)
  (--> (in-hole C (var· x ev)) (in-hole E* ev)
       eval-var)
  (--> (in-hole C (f ev ...)) (in-hole E* (δ f ev ...))
       eval-δ)

  ;; progression
  (-->
    (env (env-v_1 ... (sig S unknown) env-v_2 ...) p)
    (substitute* (env (env-v_1 ... (sig S unknown) env-v_2 ...) p) (sig S unknown) (sig S absent))
    (where (S_not ...) (Cannot p (S)))
    (where #t (∈ S (S_not ...)))
    absence)
   (-->
   (env (env-v_1 ... (shar s ev shared-status) env-v_2 ...) p)
   (substitute* (env (env-v_1 ... (shar s ev shared-status) env-v_2 ...) p)
                (shar s ev shared-status) (shar s ev ready))
   (where (s_not ...) (Cannot_shared p (s)))
   (where #t (∈ s (s_not ...)))
   (where #t (∈ shared-status (old new)))
   readyness)))

(define-metafunction esterel-eval
  instant : p (env-v ...) -> (p (any ...)) or #f
  [(instant p (env-v ...))
   (p_*
    (get-signals a))
   (where (a) ,(apply-reduction-relation* R `(setup p (env-v ...))))
   (where p_* (add-hats (clear-up-values a)))]
  [(instant p (env-v ...))
   #f
   (where (p_* ...) ,(apply-reduction-relation* R* `(setup p (env-v ...))))
   (side-condition (pretty-print `(p_* ...)))])
