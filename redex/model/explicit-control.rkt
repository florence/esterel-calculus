#lang racket
(require redex/reduction-semantics
         (only-in esterel-calculus/redex/model/shared
                  esterel-eval θ-ref-S θ-ref-s θ-ref-x
                  add2 <- dom get-unknown-signals
                  mtθ+S mtθ+s mtθ+x
                  Lwithoutdom L∈dom θ-get-S)
         esterel-calculus/redex/model/lset)
;                                                                        
;                                                                        
;                                                                        
;     ;;;;                                                               
;    ;;   ;                                                              
;   ;;                                                                   
;   ;;         ;;  ;;    ;;;;;    ; ;; ;;   ; ;; ;;    ;;;;;     ;;  ;;  
;   ;           ; ; ;        ;    ;; ;; ;;  ;; ;; ;;       ;      ; ; ;  
;   ;           ;;  ;        ;;   ;  ;   ;  ;  ;   ;       ;;     ;;  ;  
;   ;   ;;;;    ;;        ;;;;;   ;  ;   ;  ;  ;   ;    ;;;;;     ;;     
;   ;     ;;    ;        ;   ;;   ;  ;   ;  ;  ;   ;   ;   ;;     ;      
;   ;     ;;    ;       ;;   ;;   ;  ;   ;  ;  ;   ;  ;;   ;;     ;      
;   ;;    ;;    ;       ;;   ;;   ;  ;   ;  ;  ;   ;  ;;   ;;     ;      
;    ;;   ;;    ;       ;;  ;;;   ;  ;   ;  ;  ;   ;  ;;  ;;;     ;      
;     ;;;;;    ;;;;      ;;;; ;   ;  ;   ;  ;  ;   ;   ;;;; ;    ;;;;    
;                                                                        
;                                                                        
;                                                                        
;                                                                        
;                                                                        


(define-language esterel
  (p q r ::=
     (signal S p+c) (seq p+c q+c) (emit S) (present S p+c q+c) (par p+c q+c)
     nothing pause (loop +cp) (suspend p+c S) (trap p+c) (exit n)
     (shared s := e p+c) (<= s e) (var x := e p+c) (:= x e) (if x p+c q+c)
     (ρ θ p)
     (loop^stop p q))

  (p+c q+c r+c :=
       (signal S p+c) (seq p+c q+c) (emit S) (present S p+c q+c) (par p+c q+c)
       nothing pause (loop +cp) (suspend p+c S) (trap p+c) (exit n)
       (shared s := e p+c) (<= s e) (var x := e p+c) (:= x e) (if x p+c q+c)
       (ρ θ p)
       (loop^stop p q)
       (ctrl control p+c p))

  (S ::= (variable-prefix S))
  (s ::= (variable-prefix s))
  (x ::= (variable-prefix x))
  (V ::= S s x)
  (n ::= natural)

  (e ::= (f s/l ...))

  (s/l ::= s x n (rvalue any))
  (f ::= + dec (rfunc any))

  
  ;; later occurrences of duplicate bindings in θ are
  ;; ignored; i.e. only the first one should ever count
  (θ ::= · {env-v θ})

  (env-v ::= Sdat shareddat vardat)
  (status ::=
          present
          absent
          unknown)
  (Sdat ::= (sig S status))
  ;; go is lionel's `green`. It means control must reach here
  ;; wait is lionel's `gray`. It means control may or may not reach here.
  (control ::= go wait)
  



  (C ::=
     (ctrl control C p)
     (signal S C)
     (seq C q)
     (seq p C)
     (loop^stop C q)
     (loop^stop p C)
     (present S C q)
     (present S p C)
     (par C q)
     (par p C)
     (loop C)
     (suspend C S)
     (trap C)
     (shared s := e C)
     (var x := e C)
     (if x C q)
     (if x p C)
     (ρ θ C)
     hole)

  ;; state
  (shared-status ::= ready old new)
  (shareddat ::= (shar s ev shared-status))
  (vardat ::= (var· x ev))
  (ev ::= n (rvalue any))

  ;; Values and answers
  (complete ::= done (ρ θ/c done))
  (θ/c ::= · {env-v/c θ/c})
  (env-v/c ::=
           vardat
           (shar s ev ready)
           (sig S present)
           (sig S absent))
  (done ::= stopped paused)
  (stopped ::= nothing (exit n))
  (paused ::=
          pause
          (seq paused q)
          (loop^stop paused q)
          (par paused paused)
          (suspend paused S)
          (trap paused))

  ;; evaluation contexts
  (E ::=
     (ctrl control E p)
     (seq E q)
     (loop^stop E q)
     (par E q)
     (par p E)
     (suspend E S)
     (trap E)
     hole)
  (E1 ::=
      (ctrl control hole p)
      (seq hole q)
      (loop^stop hole q)
      (par hole q)
      (par p hole)
      (suspend hole S)
      (trap hole))

  (κ ::= nothin paus n)

  ;; lists as sets
  (L ::= () (any L))
  (L-S ::= () (S L-S))  (𝕊 ::= L-S L-s)
  (L-κ ::= () (κ L-κ))
  (L-s ::= () (s L-s))
  (K ::= L-n) ;; codes are lists of nats
  ;; list as maps
  ;; no duplicate keys are allowed
  (M ::= () ((variable L) M))
  (M-S-κ ::= () ((S L-κ) M-S-κ))
  (Can-result ::= (S-code-s L-S L-κ L-s)))

(define-metafunction esterel-eval
  Can-θ : (ρ θ p) θ -> Can-result

  [(Can-θ (ρ θ p) θ_2)
   (Can-θ (ρ (Lwithoutdom θ S) p) (<- θ_2 (mtθ+S S absent)))
   (judgment-holds (L∈dom S θ)) ;; S ∈ dom(θ_1)
   (judgment-holds (θ-ref-S θ S unknown)) ;; θ_1(S) = present
   (judgment-holds (L¬∈ S (->S (Can-θ (ρ (Lwithoutdom θ S) p) (<- θ_2 (mtθ+S S unknown))))))]

  [(Can-θ (ρ θ p) θ_2)
   (Can-θ (ρ (Lwithoutdom θ S) p) (<- θ_2 (mtθ+S S (θ-get-S θ S))))
   (judgment-holds (L∈dom S θ))] ;; S ∈ dom(θ_1)

  [(Can-θ (ρ θ_1 p) θ_2)
   (Can p θ_2)])

(define-metafunction esterel-eval
  Can : p θ -> Can-result
  [(Can (ρ θ_1 p) θ_2)
   (S-code-s (Lset-sub (->S (Can-θ (ρ θ_1 p) θ_2)) (Ldom θ_1))
             (->K (Can-θ (ρ θ_1 p) θ_2))
             (Lset-sub (->sh (Can-θ (ρ θ_1 p) θ_2)) (Ldom θ_1)))]

  [(Can nothing θ) (S-code-s (L0set) (L1set nothin) (L0set))]

  [(Can pause θ) (S-code-s (L0set) (L1set paus) (L0set))]

  [(Can (exit n) θ) (S-code-s (L0set) (L1set n) (L0set))]

  [(Can (emit S) θ) (S-code-s (L1set S) (L1set nothin) (L0set))]

  [(Can (present S p q) θ)
   (Can p θ)
   (judgment-holds (θ-ref-S θ S present))]

  [(Can (present S p q) θ)
   (Can q θ)
   (judgment-holds (θ-ref-S θ S absent))]

  [(Can (present S p q) θ)
   (S-code-s (LU (->S (Can p θ)) (->S (Can q θ)))
             (LU (->K (Can p θ)) (->K (Can q θ)))
             (LU (->sh (Can p θ)) (->sh (Can q θ))))]

  [(Can (suspend p S) θ)
   (Can p θ)]

  [(Can (seq p q) θ)
   (Can p θ)
   (judgment-holds (L¬∈ nothin (->K (Can p θ))))]

  [(Can (seq p q) θ)
   (S-code-s (LU (->S (Can p θ)) (->S (Can q θ)))
             (LU (Lset-sub (->K (Can p θ)) (L1set nothin)) (->K (Can q θ)))
             (LU (->sh (Can p θ)) (->sh (Can q θ))))]

  [(Can (loop p) θ)
   (Can p θ)]

  [(Can (loop^stop p q) θ)
   (Can p θ)]

  [(Can (par p q) θ)
   (S-code-s (LU (->S (Can p θ)) (->S (Can q θ)))
             (Lmax* (->K (Can p θ)) (->K (Can q θ)))
             (LU (->sh (Can p θ)) (->sh (Can q θ))))]

  [(Can (trap p) θ)
   (S-code-s (->S (Can p θ)) (Lharp... (->K (Can p θ))) (->sh (Can p θ)))]

  [(Can (signal S p) θ)
   (S-code-s (Lset-sub (->S (Can p (<- θ (mtθ+S S absent)))) (L1set S))
             (->K (Can p (<- θ (mtθ+S S absent))))
             (->sh (Can p (<- θ (mtθ+S S absent)))))
   (judgment-holds (L¬∈ S (->S (Can p (<- θ (mtθ+S S unknown))))))]

  [(Can (signal S p) θ)
   (S-code-s (Lset-sub (->S (Can p θ_2)) (L1set S)) (->K (Can p θ_2)) (->sh (Can p θ_2)))
   (where θ_2 (<- θ (mtθ+S S unknown)))]

  [(Can (shared s := e p) θ)
   (S-code-s (->S (Can p θ)) (->K (Can p θ)) (Lset-sub (->sh (Can p θ)) (L1set s)))]
  [(Can (<= s e) θ)
   (S-code-s (L0set) (L1set nothin) (L1set s))]

  [(Can (var x := e p) θ)
   (Can p θ)]
  [(Can (:= x e) θ)
   (S-code-s (L0set) (L1set nothin) (L0set))]
  [(Can (if x p q) θ)
   (S-code-s (LU (->S (Can p θ)) (->S (Can q θ)))
             (LU (->K (Can p θ)) (->K (Can q θ)))
             (LU (->sh (Can p θ)) (->sh (Can q θ))))])