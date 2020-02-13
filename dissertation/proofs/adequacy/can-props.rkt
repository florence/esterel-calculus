#lang racket
(require redex/reduction-semantics
         esterel-calculus/dissertation/lib/proof-extras)

(provide all-bot-S all-bot-n all-bot all-bot-rec)

(define-judgment-form esterel/typeset
  #:mode (= I I)
  [------------
   (= any any)])

(define-metafunction esterel/typeset
  sub : p p cs -> cs
  [(sub p q cs) cs])

(define-judgment-form esterel/typeset
  #:mode     (all-bot-S I      I I)
  #:contract (all-bot-S p-pure θ cs)
  [(⊥-implies-⊥-S p-pure θ cs)
   ---------
   (all-bot-S p-pure θ cs)])

(define-judgment-form esterel/typeset
  #:mode     (⊥-implies-⊥-S I I I)
  #:contract (⊥-implies-⊥-S p-pure θ cs)
  [------
   (⊥-implies-⊥-S p-pure θ cs)])

(define-judgment-form esterel/typeset
  #:mode     (⊥-implies-⊥-n I I I)
  #:contract (⊥-implies-⊥-n p-pure θ cs)
  [------
   (⊥-implies-⊥-n p-pure θ cs)])

(define-judgment-form esterel/typeset
  #:mode     (all-bot-n I      I I)
  #:contract (all-bot-n p-pure θ cs)
  [(⊥-implies-⊥-n p-pure θ cs)
   ---------
   (all-bot-n p-pure θ cs)])

(define-judgment-form esterel/typeset
  #:mode     (all-bot I      I I)
  #:contract (all-bot p-pure θ cs)
  [(all-bot-n p-pure θ cs) (all-bot-S p-pure θ cs) (all-bot-rec p-pure θ cs)
   --------
   (all-bot p-pure θ cs)])

(define-judgment-form esterel/typeset
  #:mode     (all-bot-rec I      I I)
  #:contract (all-bot-rec p-pure θ cs)
  [-------- "nothing"
   (all-bot-rec nothing θ cs)]
  [-------- "pause"
   (all-bot-rec pause θ cs)]
  [-------- "exit"
   (all-bot-rec (exit n) θ cs)]
  [-------- "emit"
   (all-bot-rec (emit S) θ cs)]
  [(θ-ref-S θ S present) (all-bot p-pure θ (sub (present S p-pure q-pure) p-pure cs))
   -------- "if-1"
   (all-bot-rec (present S p-pure q-pure) θ cs)]
  [(θ-ref-S θ S absent) (all-bot q-pure θ (sub (present S p-pure q-pure) q-pure cs))
   -------- "if-0"
   (all-bot-rec (present S p-pure q-pure) θ cs)]
  [(θ-ref-S θ S unknown) (all-bot p-pure θ (sub (present S p-pure q-pure) p-pure cs)) (all-bot q-pure θ (sub (present S p-pure q-pure) q-pure cs))
   -------- "if-⊥"
   (all-bot-rec (present S p-pure q-pure) θ cs)]
  [(all-bot p-pure θ (sub (suspend p-pure S) p-pure cs))
   -------- "suspend"
   (all-bot-rec (suspend p-pure S) θ cs)]
  [(L¬∈ 0 (->K (Can p-pure θ)))
   (all-bot p-pure θ (sub (seq p-pure q-pure) p-pure cs))
   -------- "seq-¬0"
   (all-bot-rec (seq p-pure q-pure) θ cs)]
  [(L∈ 0 (->K (Can p-pure θ)))
   (all-bot p-pure θ (sub (seq p-pure q-pure) p-pure cs))
   (all-bot q-pure θ (sub (seq p-pure q-pure) q-pure cs))
   -------- "seq-0"
   (all-bot-rec (seq p-pure q-pure) θ cs)]
  [(all-bot p-pure θ (sub (par p-pure q-pure) p-pure cs)) (all-bot q-pure θ (sub (par p-pure q-pure) q-pure cs))
   -------- "par"
   (all-bot-rec (par p-pure q-pure) θ cs)]
  [(all-bot p-pure θ (sub (trap p-pure) p-pure cs))
   -------- "trap"
   (all-bot-rec (trap p-pure) θ cs)]
  [(L¬∈ S (->S (Can p-pure (<- θ  (mtθ+S S ⊥)))))
   (all-bot p-pure (<- θ (mtθ+S S absent)) (sub (signal S p-pure) p-pure cs))
   -------- "signal-0"
   (all-bot-rec (signal S p-pure) θ cs)]
  [(L∈ S (->S (Can p-pure (<- θ  (mtθ+S S ⊥)))))
   (all-bot p-pure (<- θ (mtθ+S S unknown)) (sub (signal S p-pure) p-pure cs))
   -------- "signal-⊥"
   (all-bot-rec (signal S p-pure) θ cs)]
  [(all-bot-rec p-pure θ (sub (ρ · θ p-pure) p-pure cs))
   -------- "ρ-empty"
   (all-bot-rec (ρ · WAIT p-pure) θ cs)]
  [(L∈dom S θ) (θ-ref-S θr S unknown)
   (L¬∈ S (->S (Can-θ (ρ (Lwithoutdom θr S) WAIT p-pure) (<- θ (mtθ+S S unknown)))))
   (all-bot-rec (ρ (Lwithoutdom θr S) WAIT p-pure) (<- θ (mtθ+S S absent)) (sub (ρ θr WAIT p-pure) (ρ (Lwithoutdom θr S) WAIT p-pure) cs))
   -------- "ρ-0"
   (all-bot-rec (ρ θr WAIT p-pure) θ cs)]
  [(L∈dom S θ) (θ-ref-S θ S unknown)
   (L∈ S (->S (Can-θ (ρ (Lwithoutdom θr S) WAIT p-pure) (<- θ (mtθ+S S unknown)))))
   (all-bot-rec (ρ (Lwithoutdom θr S) WAIT p-pure) (<- θ (mtθ+S S unknown)) (sub (ρ θr WAIT p-pure) (ρ (Lwithoutdom θr S) WAIT p-pure) cs))
   -------- "ρ-⊥"
   (all-bot-rec (ρ θr WAIT p-pure) θ cs)]
  [(L∈dom S θ) (θ-ref-S θ S present)
   (all-bot-rec (ρ (Lwithoutdom θr S) WAIT p-pure) (<- θ (mtθ+S S present)) (sub (ρ θr WAIT p-pure) (ρ (Lwithoutdom θr S) WAIT p-pure) cs))
   -------- "ρ-1"
   (all-bot-rec (ρ θr WAIT p-pure) θ cs)])
