#lang racket
(require redex/reduction-semantics "shared.rkt" racket/random)
(provide (all-defined-out))

(define R
  ;; ASSUMPTIONS:
  ;; program is loop safe
  (reduction-relation
   esterel-eval #:domain p
   ;; TODO reducing on nothings?
   (--> (in-hole C (par halted done)) (in-hole C (value-max halted done))
        par-done-right)
   (--> (in-hole C (par done halted)) (in-hole C (value-max done halted))
        par-done-left)

   (--> (in-hole C (ρ θ. (in-hole E (present S p q))))
        (in-hole C (ρ θ. (in-hole E p)))
        (where #t (∈ (sig S present) θ.))
        is-present)
   (--> (in-hole C (ρ θ. (in-hole E (present S p q))))
        (in-hole C (ρ θ. (in-hole E q)))
        (where #t (∈ (sig S absent) θ.))
        is-absent)
   (--> (in-hole C (ρ θ. (in-hole E (emit S))))
        (in-hole C (ρ (<- θ. (sig S present)) (in-hole E nothing)))
        (where (env-v_0 ... (sig S status) env-v_2 ...) θ.)
        emit)
   #;
   (--> (in-hole C (ρ θ. (in-hole E (emit S))))
        (in-hole C (ρ θ. (in-hole E nothing)))
        (where #t (∈ (sig S present) θ.))
        emit-present)

   (--> (in-hole C (loop p)) (in-hole C (seq p (loop p)))
    loop)
   (--> (in-hole C (seq nothing q)) (in-hole C q)
    seq-done)
   (--> (in-hole C (seq (exit n) q)) (in-hole C (exit n))
    seq-exit)
   (--> (in-hole C (suspend halted S)) (in-hole C halted)
    suspend-done)
   ;; traps
   (--> (in-hole C (trap halted)) (in-hole C (harp halted))
        trap-done)
   ;; lifting signals
   (--> (in-hole C (signal S p))
        (in-hole C (ρ ((sig S unknown)) p))
        raise-signal)

   ;; shared state
   (-->
    (in-hole C (shared s := ev p))
    (in-hole C (ρ ((shar s ev new)) p))
    raise-shared)
   (-->
    (in-hole C (ρ θ. (in-hole E (<= s ev))))
    (in-hole C (ρ (<- θ. (shar s ev new)) (in-hole E nothing)))
    (where (env-v_0 ... (shar s ev_old old) env-v_2 ...)  θ.)
    set-shared-value-old)
   (-->
    (in-hole C (ρ θ. (in-hole E (<= s ev))))
    (in-hole C (ρ (<- θ. (shar s (δ f_c ev ev_old) new)) (in-hole E nothing)))
    (where (env-v_0 ... (shar s ev_old new) env-v_2 ...)  θ.)
    (where f_c +)
    set-shared-value-new)
   ;; unshared state
   (-->
    (in-hole C (var x := ev p))
    (in-hole C (ρ ((var· x ev)) p))
    raise-var)
  (-->
   (in-hole C (ρ θ. (in-hole E (:= x ev))))
   (in-hole C (ρ (<- θ. (var· x ev)) (in-hole E nothing)))
   (where (env-v_0 ... (var· x ev_old) env-v_2 ...) θ.)
   set-var)
  ;; if
  (--> (in-hole C (if ev p q))
       (in-hole C q)
       (where #t (∈ ev ((rvalue #f) 0)))
       if-false)
  (--> (in-hole C (if ev p q))
       (in-hole C p)
       (where #t (∉ ev ((rvalue #f) 0)))
       if-true)
  ;; evaling code
  (--> (in-hole C (ρ θ. (in-hole E s)))
       (in-hole C (ρ θ. (in-hole E ev)))
       (where (env-v_0 ... (shar s ev ready) env-v_2 ...) θ.)
       eval-shared)
  (--> (in-hole C (ρ θ. (in-hole E x)))
       (in-hole C (ρ θ. (in-hole E ev)))
       (where (env-v_0 ... (var· x ev) env-v_2 ...) θ.)
       eval-var)
  (--> (in-hole C (f ev ...)) (in-hole C (δ f ev ...))
       eval-δ)

  ;; progression
  (-->
   (in-hole C (ρ θ. p))
   (in-hole C (ρ (set-all-absent θ. (S_a1 S_a ...)) p))
   (where (S_a1 S_a ...) (Cannot (ρ θ. p) (get-unknown-signals θ.)))
   absence)
  (-->
   (in-hole C (ρ θ. p))
   (in-hole C (ρ (set-all-ready θ. (s_r1 s_r ...)) p))
   (where (s_r1 s_r ...) (Cannot_shared (ρ θ. p) (get-unready-shared θ.)))
   readyness)

  ;; lifting
  ;; TODO suffers from same problem as felleisen-heib (E and θ. can't be empty or something)
  (-->
   (in-hole C (ρ θ._1 (in-hole E (ρ θ._2 p))))
   (in-hole C (ρ (<- θ._1 θ._2) (in-hole E p)))
   merge)))
