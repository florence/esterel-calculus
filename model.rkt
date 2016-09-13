#lang debug racket
(provide (all-defined-out))
(require redex/reduction-semantics)
(require racket/random
         (prefix-in r: racket)
         rackunit
         racket/sandbox)

(define-syntax quasiquote (make-rename-transformer #'term))


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
       (side-condition `(∈ ev (#f 0)))
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
    (env (env-v_1 ... (sig S unknown) env-v_2 ...) p)
    (substitute* (env (env-v_1 ... (sig S unknown) env-v_2 ...) p) (sig S unknown) (sig S absent))
    (where (S_not ...) (Cannot p (S)))
    (where #t (∈ S (S_not ...)))
    ;; these are only here to make things run with decent speed
    (where () ,(apply-reduction-relation R `(env (env-v_1 ... (sig S unknown) env-v_2 ...) p)))
    (where #t (unprogressable (env-v_1 ...) p))
    absence)
   (-->
   (env (env-v_1 ... (shar s ev shared-status) env-v_2 ...) p)
   (substitute* (env (env-v_1 ... (shar s ev shared-status) env-v_2 ...) p)
                (shar s ev shared-status) (shar s ev ready))
   (where (s_not ...) (Cannot_shared p (s)))
   (where #t (∈ s (s_not ...)))
   (where #t (∈ shared-status (old new)))
   ;; for speed
   (where () ,(apply-reduction-relation R `(env (env-v_1 ... (sig S unknown) env-v_2 ...) p)))
   (where #t (unprogressable (env-v_1 ...) p))
   readyness)))

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



(module+ tracing
  (require redex
           (prefix-in cos: esterel/cos-model))
  (define-syntax-rule (render-derivations r)
    (show-derivations (build-derivations r)))
  (define (steps p)
    (traces R* `(env () ,p))
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
