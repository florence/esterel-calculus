#lang racket
(provide (all-defined-out))
(require redex/reduction-semantics
         (only-in esterel-calculus/redex/model/shared quasiquote esterel-eval)
         esterel-calculus/redex/model/lset
         esterel-calculus/redex/model/calculus)

(define-extended-language esterel-L
  esterel-eval
  (s/l ::= x s n)
  (e ::= (+) (+ s/l) (+ s/l s/l))
  (ev ::= natural)
  (i ::= (emit S) (<= s e) (:= x e))
  (R ::=  i
     (present S p q)
     (if x p q) (shared s := e p) (var x := e p)))

(define-metafunction esterel-L
  BV : p -> L
  [(BV nothing) {}]
  [(BV pause) {}]
  [(BV (signal S p))
   {S (BV p)}]
  [(BV (present S p q))
   (LU (BV p) (BV q))]
  [(BV (emit S)) {}]
  [(BV (par p q))
   (LU (BV p) (BV q))]
  [(BV (loop p))
   (BV p)]
  [(BV (seq p q))
   (LU (BV p) (BV q))]
  [(BV (loop^stop p q))
   (LU (BV p) (BV q))]
  [(BV (suspend p S))
   (BV p)]
  [(BV (trap p))
   (BV p)]
  [(BV (exit n)) {}]
  [(BV (shared s := e p))
   {s (BV p)}]
  [(BV (<= s e)) {}]
  [(BV (var x := e p))
   {x (BV p)}]
  [(BV (:= x e)) {}]
  [(BV (if x p q))
   (LU (BV p) (BV q))]
  [(BV (ρ θr A p))
   (LU (BV p) (Ldom θr))])

(define-metafunction esterel-L
  FV : p -> L
  [(FV nothing) {}]
  [(FV pause) {}]
  [(FV (signal S p)) (Lremove (FV p) S)]
  [(FV (present S p q))
   {S (LU (FV p) (FV q))}]
  [(FV (emit S)) {S {}}]
  [(FV (par p q))
   (LU (FV p) (FV q))]
  [(FV (loop p))
   (FV p)]
  [(FV (seq p q))
   (LU (FV p) (FV q))]
  [(FV (loop^stop p q))
   (LU (FV p) (FV q))]
  [(FV (suspend p S))
   {S (FV p)}]
  [(FV (trap p))
   (FV p)]
  [(FV (exit n)) {}]
  [(FV (shared s := e p))
   (LU (FV/e e) (Lremove (FV p) s))]
  [(FV (<= s e)) (s (FV/e e))]
  [(FV (var x := e p))
   (LU (FV/e e) (Lremove (FV p) x))]
  [(FV (:= x e)) (x (FV/e e))]
  [(FV (if x p q))
   (x (LU (FV p) (FV q)))]
  [(FV (ρ θr A p))
   (Lset-sub (FV p) (Ldom θr))])

(define-metafunction esterel-L
  FV/e : e -> L
  [(FV/e (+)) (L0set)]
  [(FV/e (+ n)) (L0set)]
  [(FV/e (+ s/l)) (L1set s/l)]
  [(FV/e (+ n s/l)) (FV/e (+ s/l))]
  [(FV/e (+ s/l n)) (FV/e (+ s/l))]
  [(FV/e (+ s/l_1 s/l_2)) (L2set s/l_1 s/l_2)])


(define-judgment-form esterel-eval
  #:mode (closed I)
  #:contract (closed p)
  [(where () (FV p))
   -----
   (closed p)])

(define-judgment-form esterel-L
  #:mode (CB I)
  #:contract (CB p)
  [------------ "nothing"
   (CB nothing)]
  [---------- "pause"
   (CB pause)]
  [(CB p)
   ----------------- "signal"
   (CB (signal S p))]
  [(CB p) (CB q)
   -------------------- "present"
   (CB (present S p q))]

  [-------------"emit"
   (CB (emit S))]

  [(distinct (BV p) (BV q)) (distinct (FV p) (BV q)) (distinct (BV p) (FV q))
   ------- "par"
   (CB (par p q))]

  [(distinct (BV p) (FV p)) (CB p)
   ------ "loop"
   (CB (loop p))]

  [(distinct (BV p) (FV q)) (CB p) (CB q)
   -------- "seq"
   (CB (seq p q))]
  [(distinct (BV p) (FV q)) (distinct (BV q) (FV q)) (CB p) (CB q)
   -------- "loop^stop"
   (CB (loop^stop p q))]

  [(distinct (L1set S) (BV p)) (CB p)
   ------ "suspend"
   (CB (suspend p S))]

  [(CB p)
   --------- "trap"
   (CB (trap p))]

  [------------- "exit"
   (CB (exit n))]

  [(CB p)
   ---------------------- "shared"
   (CB (shared s := e p))]

  [------------- "<="
   (CB (<= s e))]

  [(CB p)
   ------------------- "var"
   (CB (var x := e p))]

  [-------------- ":="
   (CB (:= x e))]

  [(CB p) (CB q)
   --------------- "if"
   (CB (if x p q))]

  [(CB p)
   ------------ "ρ"
   (CB (ρ θr A p))])

(module+ test
  (check-false
   (judgment-holds
    (CB
     (par
      (ρ ((shar sB 0 new) ((var· xL 0) ·))
         GO
         (suspend (signal Sm (exit 0)) SY))
      (if xl
          (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1))))
          (signal Si (trap (emit Sp))))))))
  (check-false
   (judgment-holds
    (CB
     (par
      (ρ ((shar sB 0 new) ((var· xL 0) ·))
         WAIT
         (suspend (signal Sm (exit 0)) SY))
      (if xl
          (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1))))
          (signal Si (trap (emit Sp))))))))
  (check-false
   (judgment-holds
    (CB
     (loop
      (par
       (ρ ((shar sB 0 old) ((var· xL 0) ·))
          GO
          (suspend (signal Sm (exit 0)) SY))
       (if xl
           (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1))))
           (signal Si (trap (emit Sp)))))))))
  (check-false
   (judgment-holds
    (CB
     (loop
      (par
       (ρ ((shar sB 0 old) ((var· xL 0) ·))
          WAIT
          (suspend (signal Sm (exit 0)) SY))
       (if xl
           (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1))))
           (signal Si (trap (emit Sp)))))))))
  (check-false
   (judgment-holds
    (CB
     (loop (par (ρ ((shar sB 0 old) ((var· xL 0) ·)) WAIT (suspend (signal Sm (exit 0)) SY)) (if xl (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1)))) (signal Si (trap (emit Sp)))))))))
  (check-false
   (judgment-holds
    (CB
     (loop (par (ρ ((shar sB 0 new) ((var· xL 0) ·)) GO (suspend (signal Sm (exit 0)) SY)) (if xl (var xL := (+ 0) (shared sZ := (+ 2 5) (<= sZ (+ 1)))) (signal Si (trap (emit Sp))))))))))

(define-metafunction esterel-L
  Xs : L -> L
  [(Xs {}) {}]
  [(Xs {S L}) (Xs L)]
  [(Xs {s L}) (Xs L)]
  [(Xs {x L}) {x (Xs L)}])

(module+ test
  (require rackunit)
  (check-true `(CB nothing))
  (check-true `(CB pause))
  (check-true `(CB (signal S nothing)))
  (check-true `(CB (signal S (emit S))))
  (check-true `(CB (signal S (suspend (emit S) S))))
  (redex-check
   esterel-L
   #:satisfying (CB p)
   (for/and ([pp (in-list (apply-reduction-relation ⟶ `p))])
     `(CB ,pp))
   #:attempts 100)
  (define-judgment-form esterel-L
    #:mode (renamed I)
    [(renamed nothing)]
    [(renamed pause)]
    [(distinct {S} (BV P))
     (renamed p)
     -------
     (renamed (signal S p))]
    [(distinct (BV p) (BV q))
     (distinct (FV p) (BV q))
     (distinct (BV p) (FV q))
     (renamed p)
     (renamed q)
     --------
     (renamed (present S p q))]
    [(renamed (emit S))]
    [(distinct (BV p) (BV q))
     (distinct (FV p) (BV q))
     (distinct (BV p) (FV q))
     (renamed p)
     (renamed q)
     ------------
     (renamed (par p q))]
    [(renamed p)
     -----------
     (renamed (loop p))]
    [(distinct (BV p) (BV q))
     (distinct (FV p) (BV q))
     (distinct (BV p) (FV q))
     (renamed p)
     (renamed q)
     ------------
     (renamed (seq p q))]
    [(distinct (BV p) (BV q))
     (distinct (FV p) (BV q))
     (distinct (BV p) (FV q))
     (renamed p)
     (renamed q)
     ------------
     (renamed (loop^stop p q))]
    [(distinct {S} (BV p))
     (renamed p)
     -------
     (renamed (suspend p S))]
    [(renamed p)
     -----
     (renamed (trap p))]
    [(renamed (exit n))]
    [(distinct {s} (BV p))
     (renamed p)
     -----
     (renamed (shared s := e p))]
    [(renamed (<= s e))]
    [(distinct {x} (BV p))
     (renamed p)
     --------
     (renamed (var x := e p))]
    [(renamed (:= x e))]
    [(distinct (BV p) (BV q))
     (distinct (FV p) (BV q))
     (distinct (BV p) (FV q))
     (renamed p)
     (renamed q)
     ----------
     (renamed (if x p q))])
  (redex-check
   esterel-L
   #:satisfying (renamed p)
   (for/and ([pp (in-list (apply-reduction-relation ⟶ `p))])
     `(CB ,pp))
   #:attempts 100))
