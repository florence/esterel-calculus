#lang racket
(require redex/reduction-semantics
         esterel-calculus/redex/model/calculus/define
         esterel-calculus/redex/model/shared)
(provide (all-defined-out))

(define-metafunction esterel-eval
  closed-C : (in-hole C (ρ θ E)) V -> boolean
  [(closed-C (in-hole C (ρ θ E)) V)
   #t
   (where () (FV (reassemble (ρ θ E) V)))]
  [(closed-C _ _) #f])

(define-metafunction esterel-eval
  control-closed-C : (in-hole C (ρ θ E)) V -> boolean
  [(control-closed-C (in-hole C (ρ θ E)) V)
   (control-closed (reassemble (ρ θ E) V))])

(define-metafunction esterel-eval
  control-closed : p -> boolean
  [(control-closed p)
   #t
   (where () (FV p))
   (side-condition
    (subset? 
     (list->set
      (flatten
       (term (Can_K p ·))))
     (set 'nothin 'paus)))]
            
  [(control-closed _) #f])

(define-metafunction esterel-eval
  no-control-C : (in-hole C (ρ θ E)) V -> boolean
  [(no-control-C (in-hole C (ρ θ E)) _)
   (no-control C)])

(define-metafunction esterel-eval
  no-present-C : (in-hole C (ρ θ E)) V -> boolean
  [(no-present-C (in-hole C (ρ θ E)) _)
   (no-present C)])

(define-metafunction esterel-eval
  no-seq-C : (in-hole C (ρ θ E)) V -> boolean
  [(no-seq-C (in-hole C (ρ θ E)) _)
   (no-seq C)])

(define-metafunction esterel-eval
  ;; is C a context which cannot incur a control depencency
  ;; that might gain a data dependency
  no-control : C -> boolean
  [(no-control E) #t]
  [(no-control (signal S C)) (no-control C)]
  [(no-control (loop C)) (no-control C)]
  [(no-control (shared s := e C)) (no-control C)]
  [(no-control (var x := e C)) (no-control C)]
  [(no-control (if x C q)) (no-control C)]
  [(no-control (if x p C)) (no-control C)]
  [(no-control (ρ θ C)) (no-control C)]
  [(no-control _) #f])

(define-metafunction esterel-eval
  ;; like no-control but allows control dependencies of seq
  no-present : C -> boolean
  [(no-present E) #t]
  [(no-present (seq p C)) (no-present C)]
  [(no-present (signal S C)) (no-present C)]
  [(no-present (loop C)) (no-present C)]
  [(no-present (shared s := e C)) (no-present C)]
  [(no-present (var x := e C)) (no-present C)]
  [(no-present (if x C q)) (no-present C)]
  [(no-present (if x p C)) (no-present C)]
  [(no-present (ρ θ C)) (no-present C)]
  [(no-present _) #f])

(define-metafunction esterel-eval
  ;; like no-control but allows control dependencies of present
  no-seq : C -> boolean
  [(no-seq E) #t]
  [(no-seq (seq p C)) (no-seq C)]
  [(no-seq (signal S C)) (no-seq C)]
  [(no-seq (loop C)) (no-seq C)]
  [(no-seq (shared s := e C)) (no-seq C)]
  [(no-seq (var x := e C)) (no-seq C)]
  [(no-seq (if x C q)) (no-seq C)]
  [(no-seq (if x p C)) (no-seq C)]
  [(no-seq (ρ θ C)) (no-seq C)]
  [(no-seq _) #f])

(define R-no-control (MR no-control-C))
(define R-control-closed (MR control-closed-C))
(define R-closed (MR closed-C))
(define R-no-present (MR no-present-C))
(define R-no-seq (MR no-seq-C))