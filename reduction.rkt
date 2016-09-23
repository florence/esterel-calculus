#lang racket
(require redex/reduction-semantics "shared.rkt")
(provide (all-defined-out))

(define-syntax quasiquote (make-rename-transformer #'term))

(define-extended-language esterel-standard esterel-eval
  ;; stuck programs
  (unreducable ::= v blocked)
  (blocked ::=
           (present S p q) ;; TODO ???
           (suspend^ p S) ;;TODO ???
           (suspend^ blocked S)
           (seq blocked q)
           (par blocked v)
           (par v blocked)
           (par blocked blocked)
           (suspend blocked S)
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
  (D ::=
     hole
     (seq D q)
     (par D q)
     (par unreducable D) ;; TODO
     (suspend D Sdat)
     (ρ (env-v_0 ... (sig S absent) env-v_2 ...)
        (in-hole D (suspend^ D S)))
     (trap D)
     (shared s := D p)
     (var x := D p)
     (<= s D)
     (:= x D)
     (if D p q)
     (f ev ... D e ...))
  )

(define R
  ;; ASSUMPTIONS:
  ;; program is loop safe
  (reduction-relation
   esterel-standard #:domain p
   ;; TODO reducing on nothings?
   (--> (in-hole D (par vp v)) (in-hole D (value-max vp v))
        par-done-right)
   (--> (in-hole D (par v vp)) (in-hole D (value-max v vp))
        par-done-left)

   ;; TODO can only really do in evaluation contexts ...
   (--> (ρ θ. (in-hole D (present (sig S present) p q)))
        (ρ θ. (in-hole D p))
        (where #t (∈ S θ.))
        is-present)
   (--> (ρ θ. (in-hole D (present (sig S absent) p q)))
        (ρ θ. (in-hole D q))
        (where #t (∈ S θ.))
        is-absent)
   (--> (ρ θ. (in-hole D (emit (sig S unknown))))
        (ρ θ. (substitute* (in-hole D nothing) (sig S unknown) (sig S present)))
        (where #t (∈ S θ.))
        emit-unknown)
   (--> (ρ θ. (in-hole D (emit (sig S present))))
        (ρ θ. (in-hole D nothing))
        (where #t (∈ S θ.))
        emit-present)

   (--> (in-hole D (loop p)) (in-hole D (seq p (loop p)))
    loop)
   (--> (in-hole D (seq nothing q)) (in-hole D q)
    seq-done)
   (--> (in-hole D (seq (exit n) q)) (in-hole D (exit n))
    seq-exit)
   (--> (in-hole D (suspend vp Sdat)) (in-hole D vp)
    suspend-value)
   (--> (in-hole D (suspend^ vp (sig S absent))) (in-hole D vp)
    suspend^-value)
   ;; traps
   (--> (in-hole D (trap vp)) (in-hole D (harp vp))
        trap-done)
   ;; lifting signals
   (--> (in-hole D (signal S p))
        (in-hole D (ρ (S) p))
        raise-signal)

   ;; shared state
   (-->
    (in-hole D (shared s := ev p))
    (in-hole D (ρ (s) (substitute* p s (shar s ev new))))
    raise-shared)
   (-->
    (ρ θ. (in-hole D (<= (shar s ev_old old) ev)))
    (ρ θ. (substitute* (in-hole D nothing) (shar s ev_old old) (shar s ev new)))
    (where #t (∈ s θ.))
    set-shared-value-old)
   (-->
    (ρ θ. (in-hole D (<= (shar s ev_old new) ev)))
    (ρ θ. (substitute* (in-hole D nothing) (shar s ev_old old) (shar s (δ + ev_old ev) new)))
    (where #t (∈ s θ.))
    set-shared-value-new)
   ;; unshared state
   (-->
    (in-hole D (var x := ev p))
    (in-hole D (ρ (x) (substitute* p x (var· x ev))))
    raise-var)
  (-->
   (ρ θ. (in-hole D (:= (var· x ev_old) ev)))
   (ρ θ. (substitute* (in-hole D nothing) (var· x ev_old) (var· x ev)))
   (where #t (∈ x θ.))
   set-var)
  ;; if
  (--> (in-hole D (if ev p q))
       (in-hole D q)
       (side-condition `(∈ ev ((rvalue #f) 0)))
       if-false)
  (--> (in-hole D (if ev p q))
       (in-hole D p)
       (side-condition `(∉ ev ((rvalue #f) 0)))
       if-true)
  ;; evaling code
  (--> (ρ θ. (in-hole D (shar s ev ready)))
       (ρ θ. (in-hole D (shar s ev ready)))
       (where #t (∈ s θ.))
       eval-shared)
  (--> (ρ θ. (in-hole D (var· x ev)))
       (ρ θ. (in-hole D ev))
       (where #t (∈ x θ.))
       eval-var)
  (--> (in-hole D (f ev ...)) (in-hole D (δ f ev ...))
       eval-δ)

  ;; progression
  (-->
   (ρ θ. unreducable)
   (ρ θ. (substitute* unreducable (sig S •) (sig S absent)))
   (where θ._prime (get-unknown-signals-in p θ.))
   (where (S_0 ... S S_2 ...) (Cannot p θ._prime))
   (where #t (unprogressable (S_0 ...) unreducable))
   absence)
  (-->
   (in-hole C (ρ θ. unreducable))
   (in-hole C (ρ θ. (substitute* unreducable (shar s • •) (shar s • ready))))
   (where θ._prime (get-unready-shared-in unreducable θ.))
   (where (s_0 ... s s_1 ...) (Cannot_shared unreducable θ._prime))
   (where #t (unprogressable (s_0 ...) unreducable))
   readyness)

  ;; lifting

  ;; TODO doesn't quite work because we don't have renaming and might lift too high for something that
  ;; will be reused.
  (-->
   (in-hole C (ρ θ._1 (in-hole E (ρ θ._2 p))))
   (in-hole C (ρ (U θ._1 θ._2) (in-hole E p))))))

#;
(define R
  ;; ASSUMPTIONS:
  ;; program is loop safe
  (reduction-relation
   esterel-eval #:domain p
   (--> (in-hole D (par vp v)) (in-hole P* (value-max vp v))
        par-done-right)
   (--> (in-hole D (par v vp)) (in-hole P* (value-max v vp))
        par-done-left)
   (--> (in-hole D (present (sig S present) p q)) (in-hole D p)
    is-present)
   (--> (in-hole D (present (sig S absent) p q)) (in-hole D q)
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



#;
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
   (where (a) ,(apply-reduction-relation* R `(setup p (env-v ...))))
   (where p_* (add-hats (clear-up-values a)))]
  [(instant p (env-v ...))
   #f
   (where (p_* ...) ,(apply-reduction-relation* R `(setup p (env-v ...))))
   (side-condition (pretty-print `(p_* ...)))])

(define-metafunction esterel-eval
  unprogressable : (env ...) p -> boolean
  [(unprogressable () p) #t]
  [(unprogressable (x env ...) p)
   (unprogressable (env ...) p)
   (where (var· x ev) (get-env-v x p))]
  [(unprogressable (S env ...) p)
   (unprogressable (env ...) p)
   (where (sig S status) (get-env-v S p))
   (where #t (∈ status (present absent)))]
  [(unprogressable (S env ...) p)
   (unprogressable (env ...) p)
   (where (sig S status) (get-env-v S p))
   (where ⊥ (Cannot p (S)))]
  [(unprogressable (s env ...) p)
   (unprogressable (env ...) p)
   (where (shar s ev ready) (get-env-v s p))]
  [(unprogressable (s env ...) p)
   (unprogressable (env ...) p)
   (where (shar s ev shared-status) (get-env-v s p))
   (where ⊥ (Cannot_shared p (s)))]
  [(unprogressable (env-v ...) p) #f])
