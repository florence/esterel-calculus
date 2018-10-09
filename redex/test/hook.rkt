#lang racket

(require redex/reduction-semantics
         (prefix-in b: esterel-calculus/redex/test/binding)
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/calculus
         rackunit)

(module+ test
  (define S↦unknown (term {(sig S unknown) ·}))
  (define S↦present (term {(sig S present) ·})))

(define-extended-language esterel-hook esterel-eval
  (p* ::=
      (signal S p)
      (seq p q)
      (emit S)
      (present S p q)
      (par p q)
      nothing
      pause
      (loop p)
      (suspend p S)
      (trap p)
      (exit n)
      (shared s := e p)
      (<= s e)
      (var x := e p)
      (:= x e)
      (if x p q)
      (loop^stop p q)))

(define-judgment-form esterel-hook
  #:contract (~1 C p C p)
  #:mode     (~1 I I I I)
  [------------------ "same-context"
   (~1   hole p*_1       hole p_2)]

  [-------------------
   (~1   (ρ θ_1 E) p_1   (ρ θ_2 E) p_2)])

(define-judgment-form esterel-hook
  #:contract (hook1/c C C)
  #:mode     (hook1/c I O)
  [--------------------
   (hook1/c hole hole)]

  [(side-condition ,(not (equal? (term C) (term hole))))
   (hook1/c C_1 C_2)
   -----------------------------------------
   (hook1/c (in-hole C C_1) (in-hole C C_2))]

  [(hook1/c C_1 C_2)
   (hook1   p_1 p_2)
   --------------------
   (hook1/c (loop^stop C_1 p_1) (loop^stop C_2 p_2))])

(define-judgment-form esterel-hook
  #:contract (hook1 p p)
  #:mode     (hook1 I O)
  [----------- "hrfl1"
   (hook1 p p)]

  [(hook1/c C_ci C_co)

   (where (any_1 ... (in-hole C_po p_o) any_2 ...)
          ,(apply-reduction-relation R* (term (in-hole C_pi p_i))))
   (~1 C_pi p_i C_po p_o)

   (hook1/c C_po C_poh)
   ------------------------------------------------------------------------------- "hred1"
   (hook1 (in-hole C_ci (in-hole C_pi p_i)) (in-hole C_co (in-hole C_poh p_o)))])


(module+ test
  (test-judgment-holds (hook1 (suspend (ρ ,S↦unknown (trap (emit S))) S2)
                              (suspend (ρ {(sig S present) ·} (trap nothing)) S2))))




(define-judgment-form esterel-hook
  #:contract (~2 C p C p)
  #:mode     (~2 I I I I)
  [------------------
   (~2   C p*_1                      C p_2)]

  [--------------------------------------------------------------
   (~2   (in-hole C (ρ θ_1 E)) p_1   (in-hole C (ρ θ_2 E)) p_2)])

(define-judgment-form esterel-hook
  #:contract (hook2/c C C)
  #:mode     (hook2/c I O)
  [--------------------
   (hook2/c hole hole)]

  [(side-condition ,(not (equal? (term C) (term hole))))
   (hook2/c C_1 C_2)
   -----------------------------------------
   (hook2/c (in-hole C C_1) (in-hole C C_2))]

  [(hook2/c C_1 C_2)
   (hook2   p_1 p_2)
   --------------------
   (hook2/c (loop^stop C_1 p_1) (loop^stop C_2 p_2))])

(define-judgment-form esterel-hook
  #:contract (hook2 p p)
  #:mode     (hook2 I O)
  [----------- "hrfl2"
   (hook2 p p)]

  [(where (any_1 ... (in-hole C_o p_o) any_2 ...)
          ,(apply-reduction-relation R (term (in-hole C_i p_i))))
   (~2 C_i p_i C_o p_o)
   (hook2/c C_o C_oh)
   ------------------------------------------------------------- "hred2"
   (hook2 (in-hole C_i p_i) (in-hole C_oh p_o))])


(define-judgment-form esterel-hook
  #:contract (hook3 p p)
  #:mode     (hook3 I O)
  [---------- "refl"
   (hook3 p p)]
  
  [(hook3C C_i C_o)
   (hook3p p_i p_o)
   -------------------------
   (hook3 (in-hole C_i p_i) (in-hole C_o p_o))])
(define-judgment-form esterel-hook
  #:contract (hook3C C C)
  #:mode     (hook3C I O)
  [------------ "hole"
   (hook3C hole hole)]
  
  [(side-condition ,(not (equal? (term C) (term hole))))
   (hook3C C_i C_o)
   ------------ "C"
   (hook3C (in-hole C C_i) (in-hole C C_o))]
  
  [(hook3C C_i C_o)
   (hook3 q_i q_o)
   ------------ "loop^stop"
   (hook3C (loop^stop C_i q_i) (loop^stop C_o q_o))])

(define-judgment-form esterel-hook
  #:contract (hook3p p p)
  #:mode     (hook3p I O)
  
  [(where (_ ... p_o _ ...) ,(apply-reduction-relation R* (term p*_i)))
   ---------- "→"
   (hook3p p*_i p_o)]
  
  [(where (_ ... (ρ θ_o p) _ ...) ,(apply-reduction-relation R* (term (ρ θ_i p))))
   ---------- "pot"
   (hook3p (ρ θ_i p) (ρ θ_o p))]
  
  [(hook3C E_i E_o)
   (where (_ ... (ρ θ_o (in-hole E_i p_o)) _ ...)
    ,(apply-reduction-relation R* (term (ρ θ_i (in-hole E_i p_i)))))
   (side-condition ,(not (equal? (term p_i) (term p_o))))
   ---------- "E"
   (hook3p (ρ θ_i (in-hole E_i p_i)) (ρ θ_o (in-hole E_o p_o)))])

(define (→ p)
  (apply-reduction-relation R p))
(define (h→1 p)
  (apply-reduction-relation hook1 p))
(define (h→2 p)
  (apply-reduction-relation hook2 p))
(define (h→3 p)
  (apply-reduction-relation hook3 p))

(define ((arrow-implies-hook h) p)
  (define next (apply-reduction-relation R p))
  (define hnext (h p))
  (for/and ([n (in-list next)])
    (member n hnext)))

(define arrow-implies-hook1 (arrow-implies-hook h→1))
(define arrow-implies-hook2 (arrow-implies-hook h→2))
(define arrow-implies-hook3 (arrow-implies-hook h→3))

(define ((conf r) p)
  (define ps (r p))
  (for*/and ([left (in-list ps)]
             [right (in-list ps)])
    (define rr (r right))
    (for/or ([q (in-list (r left))])
      (member q rr))))

(define (test-CB f a)
  (redex-check
   b:esterel-L
   #:satisfying (b:CB p)
   (check-not-false (f (term p)))
   #:attempts a))


(module+ test
  (test-judgment-holds (~2 hole (par nothing nothing) hole nothing))
  (test-judgment-holds (~2 (suspend (ρ ,S↦unknown (trap hole)) S2) (emit S)
                           (suspend (ρ ,S↦present (trap hole)) S2) nothing))

  (test-judgment-holds (hook2/c (suspend (ρ {(sig S present) ·} (trap hole)) S2)
                                (suspend (ρ {(sig S present) ·} (trap hole)) S2)))
  
  (test-judgment-holds (hook3C (suspend (ρ {(sig S present) ·} (trap hole)) S2)
                                (suspend (ρ {(sig S present) ·} (trap hole)) S2)))



  (test-judgment-holds (hook2 (suspend (ρ ,S↦unknown (trap (emit S))) S2)
                              (suspend (ρ {(sig S present) ·} (trap nothing)) S2)))
  
  (test-judgment-holds (hook3 (suspend (ρ ,S↦unknown (trap (emit S))) S2)
                              (suspend (ρ {(sig S present) ·} (trap nothing)) S2))))
