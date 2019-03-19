#lang racket
(require redex/reduction-semantics
         racket/require
         (multi-in
          esterel-calculus/redex/model
          (shared lset lmap potential-function calculus/define))
         (only-in esterel-calculus/redex/model/calculus/variants/base R-empty))
(provide (all-defined-out))


(define-metafunction esterel-eval
  safe-after-reduction-C : (in-hole C (ρ θ E)) V -> boolean
  [(safe-after-reduction-C (in-hole C (ρ θ E)) V)
   #t
   (judgment-holds (safe-after-reduction (in-hole C (ρ θ E)) V))]
  [(safe-after-reduction-C (in-hole C (ρ θ E)) V)
   #f])

(define-judgment-form esterel-eval
  #:mode     (safe-after-reduction I                   I)
  #:contract (safe-after-reduction (in-hole C (ρ θ E)) V)
  [(where p_r (reassemble (ρ θ E) V))
   ;; by making sure we look for E, we make sure we ran the "right"
   ;; reduction.
   (where (_ ... (ρ θ_* (in-hole E nothing)) _ ...)
          ,(apply-reduction-relation R-empty (term p_r)))
   (where L-S_changed
          (Lset-sub (Can_S p_r ·)
                    (Can_S (ρ θ_* (in-hole E nothing)) ·)))
   (where L-S_deps (control-deps (in-hole C (ρ θ E))))
   (distinct L-S_changed L-S_deps)
   ----------------- "safe-after-reduction"
   (safe-after-reduction (in-hole C (ρ θ E)) V)])

(define-metafunction esterel-eval
  control-deps : C -> L-S
  [(control-deps C)
   (Mdom
    (Mrestrict-range-to
     (control-deps* C ·)
     nothin))])

(define-metafunction esterel-eval
  control-deps* : C θ -> M-S-κ
  [(control-deps* hole θ) (M0)]
  [(control-deps* (seq C q) θ)
   (MU (Mrestrict-range
        (control-deps* C θ)
        nothin)
       (κ-deps q))]
  [(control-deps* (seq p C) θ)
   (MU (Mrestrict-range
        (κ-deps p)
        nothin)
       (control-deps* C θ))]
  [(control-deps* (loop^stop C q) θ)
   (control-deps* C θ)]
  [(control-deps* (loop^stop p C) θ)
   (κ-deps p θ)]
  [(control-deps* (present S C q) θ)
   (MU
    (M1* S (Can_K (present S (in-hole C nothing) q) θ))
    (MU
     (control-deps* C θ)
     (κ-deps q θ)))]
  [(control-deps* (present S p C) θ)
   (MU
    (M1* S (Can_K (present S p (in-hole C nothing)) θ))
    (MU
     (κ-deps p θ)
     (control-deps* C θ)))]
  [(control-deps* (par C q) θ)
   (Mmax*
    (control-deps* C θ)
    (κ-deps q θ))]
  [(control-deps* (par p C) θ)
   (Mmax*
    (κ-deps p θ)
    (control-deps* C θ))]
  [(control-deps* (loop C) θ)
   (control-deps* C θ)]
  [(control-deps* (suspend C S) θ)
   (control-deps* C θ)]
  [(control-deps* (trap C) θ)
   (M---κ↓ (control-deps* C θ))]
  [(control-deps* (shared s := e C) θ)
   (control-deps* C θ)]
  [(control-deps* (var x := e C) θ)
   (control-deps* C θ)]
  [(control-deps* (if x C q) θ)
   (MU
    (control-deps* C θ)
    (κ-deps q θ))]
  [(control-deps* (if x p C) θ)
   (MU
    (κ-deps p θ)
    (control-deps* C θ))]
  [(control-deps* (signal S C) θ)
   (Mrestrict-domain (control-deps* C θ) S)]
  [(control-deps* (ρ θ E) θ_1)
   (Mrestrict-domain*
    (control-deps* C (<- θ θ_1))
    (get-unknown-signals θ))]
  [(control-deps* (ρ θ C) θ_1)
   (Mrestrict-domain*
    (control-deps* C θ_1)
    (get-unknown-signals θ))])

(define-metafunction esterel-eval
  κ-deps : p θ -> M-S-κ
  [(κ-deps (signal S p) θ)
   (Mrestrict-domain (κ-deps p (<- θ TODO) S))]
  [(κ-deps nothing θ) (M0)]
  [(κ-deps pause θ) (M0)]
  [(κ-deps (seq p q) θ)
   (MU (Mrestrict-range
        (κ-deps p θ)
        nothin)
       (κ-deps q θ))]
  [(κ-deps (emit S)) (M0)]
  [(κ-deps (present S p q) θ)
   (MU
    (M1* S (Can_K (present S p q) θ))
    (MU
     (κ-deps p θ)
     (κ-deps q θ)))]
  [(κ-deps (par p q) θ)
   (Mmax*
    (κ-deps p θ)
    (κ-deps q θ))]
  [(κ-deps (loop p) θ)
   (κ-deps p θ)]
  [(κ-deps (suspend p S))
   (κ-deps p)]
  [(κ-deps (trap p))
   (M---κ↓ (κ-deps p))]
  [(κ-deps (exit n)) (M0)]
  [(κ-deps (shared s := e p))
   (κ-deps p)]
  [(κ-deps (var x := e p))
   (κ-deps p)]
  [(κ-deps (<= s e)) (M0)]
  [(κ-deps (:= x e)) (M0)]
  [(κ-deps (if x p q))
   (MU (κ-deps p) (κ-deps q))]
  [(κ-deps (ρ θ p))
   (Mrestrict-domain*
    (κ-deps p)
    (get-unknown-signals θ))]
  [(κ-deps (loop p q))
   (κ-deps p)])
  
(define R-safe-after-reduction (MR safe-after-reduction-C))