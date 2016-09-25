#lang racket
(require redex/reduction-semantics "shared.rkt")
(provide (all-defined-out))
(module+ test (require rackunit))

(define-syntax quasiquote (make-rename-transformer #'term))

(define-extended-language esterel-standard esterel-eval
  ;; stuck programs
  (D ::=
     hole
     (seq D q)
     (par D q)
     (par p D)
     (suspend D S)
     (trap D)
     (shared s := D p)
     (var x := D p)
     (<= s D)
     (:= x D)
     (if D p q)
     (f ev ... D e ...)))

(define-metafunction esterel-eval
  instant : p (env-v ...) -> (p (any ...)) or #f
  [(instant p (env-v ...))
   (p_*
    (get-signals complete))
   (where (complete) ,(apply-reduction-relation* R `(setup p (env-v ...))))
   (where p_* (add-hats (clear-up-values complete)))]
  [(instant p (env-v ...))
   #f
   (where (p_* ...) ,(apply-reduction-relation* R `(setup p (env-v ...))))
   (side-condition (pretty-print `(p_* ...)))])

(define R
  ;; ASSUMPTIONS:
  ;; program is loop safe
  (reduction-relation
   esterel-standard #:domain p
   ;; TODO reducing on nothings?
   (--> (ρ θ. (in-hole D (par halted done))) (ρ θ. (in-hole D (value-max halted done)))
        (judgment-holds (good D θ.))
        par-done-right)
   (--> (ρ θ. (in-hole D (par done halted))) (ρ θ. (in-hole D (value-max done halted)))
        (judgment-holds (good D θ.))
        par-done-left)

   ;; TODO can only really do in evaluation contexts ...
   (--> (ρ θ. (in-hole D (present S p q)))
        (ρ θ. (in-hole D p))
        (judgment-holds (good D θ.))
        (where #t (∈ (sig S present) θ.))
        is-present)
   (--> (ρ θ. (in-hole D (present S p q)))
        (ρ θ. (in-hole D q))
        (judgment-holds (good D θ.))
        (where #t (∈ (sig S absent) θ.))
        is-absent)
   (--> (ρ θ. (in-hole D (emit S)))
        (ρ (<- θ. (sig S present)) (in-hole D nothing))
        (judgment-holds (good D θ.))
        (where (env-v_0 ... (sig S status) env-v_2 ...) θ.)
        emit)
   (--> (ρ θ. (in-hole D (loop p))) (ρ θ. (in-hole D (seq p (loop p))))
        (judgment-holds (good D θ.))
        loop)
   (--> (ρ θ. (in-hole D (seq nothing q))) (ρ θ. (in-hole C q))
        (judgment-holds (good D θ.))
        seq-done)
   (--> (ρ θ. (in-hole D (seq (exit n) q))) (ρ θ. (in-hole D (exit n)))
        (judgment-holds (good D θ.))
        seq-exit)
   (--> (ρ θ. (in-hole D (suspend halted S))) (ρ θ. (in-hole D halted))
        (judgment-holds (good D θ.))
        suspend-done)
   ;; traps
   (--> (ρ θ. (in-hole D (trap halted))) (ρ θ. (in-hole D (harp halted)))
        (judgment-holds (good D θ.))
        trap-done)
   ;; lifting signals
   (--> (ρ θ. (in-hole D (signal S p)))
        (ρ θ. (in-hole D (ρ ((sig S unknown)) p)))
        (judgment-holds (good D θ.))
        raise-signal)
   ;; shared state
   (-->
    (ρ θ. (in-hole D (shared s := ev p)))
    (ρ θ. (in-hole D (ρ ((shar s ev new)) p)))
    (judgment-holds (good D θ.))
    raise-shared)
   (-->
    (ρ θ. (in-hole D (<= s ev)))
    (ρ (<- θ. (shar s ev new)) (in-hole D nothing))
    (judgment-holds (good D θ.))
    (where (env-v_0 ... (shar s ev_old old) env-v_2 ...)  θ.)
    set-shared-value-old)
   (-->
    (ρ θ. (in-hole D (<= s ev)))
    (ρ (<- θ. (shar s (δ f_c ev ev_old) new)) (in-hole D nothing))
    (where (env-v_0 ... (shar s ev_old new) env-v_2 ...)  θ.)
    (judgment-holds (good D θ.))
    (where f_c +)
    set-shared-value-new)
   ;; unshared state
   (-->
    (ρ θ. (in-hole D (var x := ev p)))
    (ρ θ. (in-hole D (ρ ((var· x ev)) p)))
    (judgment-holds (good D θ.))
    raise-var)
  (-->
   (ρ θ. (in-hole D (:= x ev)))
   (ρ (<- θ. (var· x ev)) (in-hole D nothing))
   (judgment-holds (good D θ.))
   (where (env-v_0 ... (var· x ev_old) env-v_2 ...) θ.)
   set-var)
  ;; if
  (--> (ρ θ. (in-hole D (if ev p q)))
       (ρ θ. (in-hole D q))
       (judgment-holds (good D θ.))
       (where #t (∈ ev ((rvalue #f) 0)))
       if-false)
  (--> (ρ θ. (in-hole D (if ev p q)))
       (ρ θ. (in-hole D p))
       (judgment-holds (good D θ.))
       (where #t (∉ ev ((rvalue #f) 0)))
       if-true)
  ;; evaling code
  (--> (ρ θ. (in-hole D s))
       (ρ θ. (in-hole D ev))
       (judgment-holds (good D θ.))
       (where (env-v_0 ... (shar s ev ready) env-v_2 ...) θ.)
       eval-shared)
  (--> (ρ θ. (in-hole D x))
       (ρ θ. (in-hole D ev))
       (judgment-holds (good D θ.))
       (where (env-v_0 ... (var· x ev) env-v_2 ...) θ.)
       eval-var)
  (--> (ρ θ. (in-hole D (f ev ...)))
       (ρ θ. (in-hole D (δ f ev ...)))
       (judgment-holds (good D θ.))
       eval-δ)

  ;; progression
  (-->
   (ρ θ. p)
   (ρ (set-all-absent θ. (S_a1 S_a ...)) p)
   (judgment-holds (stuck p (get-unknown-signals θ.) (get-unready-shared θ.)))
   (where (S_a1 S_a ...) (Cannot (ρ θ. p) (get-unknown-signals θ.)))
   absence)
  (-->
   (ρ θ. p)
   (ρ (set-all-ready θ. (s_r1 s_r ...)) p)
   (judgment-holds (stuck p (get-unknown-signals θ.) (get-unready-shared θ.)))
   (where () (Cannot (ρ θ. p) (get-unknown-signals θ.)))
   (where (s_r1 s_r ...) (Cannot_shared (ρ θ. p) (get-unready-shared θ.)))
   readyness)

  ;; lifting
  (-->
   (ρ θ._1 (in-hole D (ρ θ._2 p)))
   (ρ (<- θ._1 θ._2) (in-hole D p))
   (judgment-holds (good D θ.))
   merge)
  ))

(define-judgment-form esterel-standard
  #:mode     (good I I)
  #:contract (good D θ.)
  [(good-D D (get-unknown-signals θ.) (get-unready-shared θ.))
   -------------
   (good D θ.)])


(define-judgment-form esterel-standard
  #:mode     (good-D I I I)
  #:contract (good-D D (S ...) (s ...))
  [----------
   (good-D hole (S ...) (s ...))]
  [(good-D D (S ...) (s ...))
   ----------
   (good-D (seq D q) (S ...) (s ...))]
  [(good-D D (S ...) (s ...))
   ----------
   (good-D (par D q) (S ...) (s ...))]
  [(good-D D (S ...) (s ...))
   (stuck p (S ...) (s ...))
   ----------
   (good-D (par p D) (S ...) (s ...))]
  [(good-D D (S ...) (s ...))
   ----------
   (good-D (suspend D S_a) (S ...) (s ...))]
  [(good-D D (S ...) (s ...))
   ----------
   (good-D (trap D) (S ...) (s ...))]
  ;; TODO state
  [(good-D D (S ...) (s ...))
   ----------
   (good-D (trap D) (S ...) (s ...))])

(define-judgment-form esterel-standard
  #:mode     (stuck I I I)
  #:contract (stuck p (S ...) (s ...))
  [----------
   (stuck paused (S ...) (s ...))]
  [(where #t (∈ S_p (S ...)))
   ----------
   (stuck (present S_p p q) (S ...) (s ...))]
  [(stuck p (S ...) (s ...))
   (stuck q (S ...) (s ...))
   ----------
   (stuck (par p q) (S ...) (s ...))]
  [(stuck p (S ...) (s ...))
   ---------
   (stuck (seq p q) (S ...) (s ...))]
  [(stuck p (S ...) (s ...))
   ---------
   (stuck (trap p) (S ...) (s ...))]
  [(stuck-e e (s ...))
   --------
   (stuck (shared s_s := e p) (S ...) (s ...))]
  [(where #t (∈ s_s (s ...)))
   --------
   (stuck (<= s_s e) (S ...) (s ...))]
  [(stuck-e e (s ...))
   --------
   (stuck (<= s_s e) (S ...) (s ...))]
  [(stuck-e e (s ...))
   --------
   (stuck (var x := e p) (S ...) (s ...))]
  [(stuck-e e (s ...))
   --------
   (stuck (:= x e) (S ...) (s ...))])

(define-judgment-form esterel-standard
  #:mode     (stuck-e I I)
  #:contract (stuck-e e (s ...))
  [(where (s_1 ... s_u s_2 ...) (FV e))
   (where #t (∈ s_u (s ...)))
   ------------
   (stuck-e e (s ...))])
