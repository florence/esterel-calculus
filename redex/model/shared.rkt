#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))
(module+ test (require rackunit))

(define-syntax quasiquote (make-rename-transformer #'term))


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
     nothing (exit n) (emit S) pause
     (signal S p) (seq p q) (present S p q) (par p q)
     (loop p) (suspend p S) (trap p)
     (shared s := e p) (<= s e) (var x := e p) (:= x e) (if x p q))
  ;; (<= s e) renders as s += e in the paper

  (S ::= (variable-prefix S))
  (s ::= (variable-prefix s))
  (x ::= (variable-prefix x))
  (V ::= S s x)
  (n ::= natural)

  (e ::= (f s/l ...))

  (s/l ::= s x n (rvalue any))
  (f ::= + dec (rfunc any)))

(define-extended-language esterel-eval esterel
  (p q r ::= ....
     (loop^stop p q)
     (ρ θ A p))

  ;; later occurrences of duplicate bindings in θ are
  ;; ignored; i.e. only the first one should ever count
  (θ ::= · {env-v θ})

  (env-v ::= Sdat shareddat vardat)
  (status ::=
          present
          unknown
          absent)
  (Sdat ::= (sig S status))
  ;; go is lionel's `green`. It means control must reach here
  ;; wait is lionel's `gray`. It means control may or may not reach here.
  (A ::= GO WAIT)

  (C ::=
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
     (ρ θ A C)
     hole)

  ;; state
  (shared-status ::= old new)
  (shareddat ::= (shar s ev shared-status))
  (vardat ::= (var· x ev))
  (ev ::= n (rvalue any))

  ;; Values and answers
  (complete* ::= done (ρ θ GO done))
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
     (seq E q)
     (loop^stop E q)
     (par E q)
     (par p E)
     (suspend E S)
     (trap E)
     hole)
  (E1 ::=
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



;                                                                        
;                                                                        
;                                                                        
;   ;;    ;                ;                                             
;   ;;    ;                ;                                             
;   ;;    ;                ;                                             
;   ;;    ;     ;;;;       ;       ; ;;;      ;;;;     ;;  ;;     ;;;;   
;   ;;    ;    ;;  ;;      ;       ;;  ;;    ;;  ;;     ; ; ;    ;    ;  
;   ;;;;;;;    ;    ;      ;       ;    ;    ;    ;     ;;  ;    ;       
;   ;;    ;   ;;    ;      ;       ;    ;   ;;    ;     ;;       ;;      
;   ;;    ;   ;;;;;;;      ;       ;    ;   ;;;;;;;     ;         ;;;;   
;   ;;    ;   ;;           ;       ;    ;   ;;          ;            ;;  
;   ;;    ;    ;           ;       ;    ;    ;          ;             ;  
;   ;;    ;    ;;   ;      ;       ;;  ;;    ;;   ;     ;       ;;   ;;  
;   ;;    ;     ;;;;        ;;;    ;;;;;      ;;;;     ;;;;      ;;;;;   
;                                  ;                                     
;                                  ;                                     
;                                  ;                                     
;                                                                        
;                                                                        


(define-metafunction esterel-eval
  A->= : A A -> boolean
  [(A->= GO A) #t]
  [(A->= WAIT WAIT) #t]
  [(A->= WAIT GO) #f])

(define-metafunction esterel-eval
  par-⊓ : done done -> done
  [(par-⊓ nothing done) done]
  [(par-⊓ done nothing) done]
  [(par-⊓ (exit n_1) (exit n_2)) (exit (max-mf n_1 n_2))]
  [(par-⊓ (exit n) paused) (exit n)]
  [(par-⊓ paused (exit n)) (exit n)])

(define-metafunction esterel-eval
  max-mf : n n -> n
  [(max-mf n_1 n_2) ,(max `n_1 `n_2)])

(define-metafunction esterel-eval
  setup : p (env-v ...) -> p
  [(setup (ρ θ A p) ())
   (ρ θ GO p)]
  [(setup (ρ θ A p) (env-v_h env-v ...))
   (setup (ρ (<- θ {env-v_h ·}) GO p) (env-v ...))]
  [(setup p (env-v ...))
   (setup (ρ · GO p) (env-v ...))])

(define-metafunction esterel-eval
  next-instant : complete* -> p
  [(next-instant (ρ θ GO p)) (ρ (reset-θ θ) WAIT (next-instant p))]
  [(next-instant pause) nothing]
  [(next-instant nothing) nothing]
  [(next-instant (loop^stop p q)) (seq (next-instant p) (loop q))]
  [(next-instant (seq p q)) (seq (next-instant p) q)]
  [(next-instant (par p q)) (par (next-instant p) (next-instant q))]
  [(next-instant (suspend p S))
   (suspend (seq (present S pause nothing) (next-instant p)) S)]
  [(next-instant (trap p)) (trap (next-instant p))]
  [(next-instant (exit n)) (exit n)])

(define-metafunction esterel-eval
  reset-θ : θ -> θ
  [(reset-θ ·) ·]
  [(reset-θ {env-v θ}) {(reset-env-v env-v) (reset-θ θ)}])

(define-metafunction esterel-eval
  reset-env-v : env-v -> env-v
  [(reset-env-v S) S]
  [(reset-env-v (sig S status)) (sig S unknown)]
  [(reset-env-v (shar s ev shared-status)) (shar s ev old)]
  [(reset-env-v (var· x ev)) (var· x ev)])

(module+ test
  (check-equal?
   (term (next-instant (loop^stop pause (loop^stop pause (loop pause)))))
   (term (seq nothing (loop (loop^stop pause (loop pause))))))
  (check-equal?
   (term (next-instant (seq pause pause)))
   (term (seq nothing pause)))
  (check-equal?
   (term (next-instant (ρ ((sig S1 unknown) ((sig S2 present) ·)) GO pause)))
   (term (ρ ((sig S1 unknown) ((sig S2 unknown) ·)) WAIT nothing)))
  (check-equal?
   (term (next-instant (ρ ((shar s2 0 new) ((shar s3 0 new) ·))
                          GO
                          (par (seq (trap pause) pause)
                               (par pause pause)))))
   (term (ρ ((shar s2 0 old) ((shar s3 0 old) ·))
            WAIT
            (par (seq (trap nothing) pause)
                 (par nothing nothing))))))

(define-metafunction esterel-eval
  add2 : n -> n
  [(add2 n) ,(+ `n 2)])

(define-metafunction esterel-eval
  sub1 : n -> n
  [(sub1 n) ,(- `n 1)])

(define-metafunction esterel-eval
  Σ : n n -> n
  [(Σ n_1 n_2) ,(+ `n_1 `n_2)])

(define-metafunction esterel-eval
  max* : {κ ...} {κ ...} -> {κ ...}
  [(max* {} {κ ...}) {}]
  [(max* {κ_1 κ_r ...} {κ ...})
   (appen ,(map (lambda (x) (max x `κ_1)) `{κ ...})
          (max* {κ_r ...} {κ ...}))])

(define-metafunction esterel-eval
  harp... : {κ ...} -> {κ ...}
  [(harp... {κ ...})
   ({↓ κ} ...)])

(define-metafunction esterel-eval
  ↓ : κ -> κ
  [(↓ nothin) nothin]
  [(↓ paus) paus]
  [(↓ 0) nothin]
  [(↓ n) (sub1 n)
         (side-condition (term (greater-than-0 n)))])

(define-metafunction esterel-eval
  greater-than-0 : n -> boolean
  [(greater-than-0 0) #f]
  [(greater-than-0 n) #t])

(define-judgment-form esterel-eval
  #:mode (∉ I I)
  #:contract (∉ any (any ...))

  [(where #t ,(not (member `any_1 `{any_2 ...})))
   -----------------------------------------------
   (∉ any_1 {any_2 ...})])

(define-judgment-form esterel-eval
  #:mode (∈ I I)
  #:contract (∈ any (any ...))
  [---------------------------
   (∈ any_1 (any_1 any_2 ...))]
  [(where #t (different any_1 any_2))
   (∈ any_1 (any_3 ...))
   ---------------------------
   (∈ any_1 (any_2 any_3 ...))])


(define-metafunction esterel-eval
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t])

(define-metafunction esterel-eval
  [(same any_1 any_1) #t]
  [(same any_1 any_2) #f])

(define-metafunction esterel-eval
  U : {any ...} ... -> {any ...}
  [(U {any ...} ...)
   ,(set->list (list->set `(any ... ...)))])

(define-metafunction esterel-eval
  appen : (any ...) ... -> (any ...)
  [(appen (any ...) ...) (any ... ...)])

(define-metafunction esterel-eval
  without : {any ...} any -> {any ...}
  [(without {any_1 ... any_2 any_3 ...} any_2)
   (without {any_1 ... any_3 ...} any_2)]
  [(without {any_1 ...} any_2) {any_1 ...}])

(define-metafunction esterel-eval
  meta-max : {n ...} {n ...} -> {n ...}
  [(meta-max {} {n_2 ...})
   {}]
  [(meta-max {n_1 ...} {})
   {}]
  [(meta-max {n_1 ...} {n_2 ...})
   ,(set->list
     (for*/set ([n1 (in-list `(n_1 ...))]
                [n2 (in-list `(n_2 ...))])
       (max n1 n2)))])

(define-metafunction esterel-eval
  δ : e θ -> ev
  [(δ (+ s/l ...) θ) ,(apply + `(resolve (s/l ...) θ))]
  [(δ (dec s/l) θ) ,(apply (λ (x) (max 0 (- x 1))) `(resolve (s/l) θ))]
  [(δ (dec s/l ...) θ) 0]
  [(δ ((rfunc any) s/l ...) θ) (rvalue ,(apply `any `(resolve (s/l ...) θ)))])

(define-metafunction esterel-eval
  resolve : (s/l ...) θ -> (ev ...)
  [(resolve () θ) ()]
  [(resolve (ev s/l ...) θ)
   (ev ev_r ...)
   (where (ev_r ...) (resolve (s/l ...) θ))]

  [(resolve (x s/l ...) θ)
   (ev ev_r ...)
   (where (var· x ev) (θ-ref θ x))
   (where (ev_r ...) (resolve (s/l ...) θ))]
  [(resolve (s s/l ...) θ)
   (ev ev_r ...)
   (where (shar s ev shared-status) (θ-ref θ s))
   (where (ev_r ...) (resolve (s/l ...) θ))])

(define-metafunction esterel-eval
  harp : stopped -> stopped
  [(harp nothing) nothing]
  [(harp (exit 0)) nothing]
  [(harp (exit n)) (exit (sub1 n))])

(define-metafunction esterel-eval
  get-signals : p -> (S ...)
  [(get-signals (ρ θ A p))
   (get-signals* θ)]
  [(get-signals p) ()])
(define-metafunction esterel-eval
  get-signals* : θ -> (S ...)
  [(get-signals* θ) (get-signals-of-status θ present)])

(define-metafunction esterel-eval
  get-unknown-signals : θ -> (S ...)
  [(get-unknown-signals θ)
   (get-signals-of-status θ unknown)])

(define-metafunction esterel-eval
  get-signals-of-status : θ status -> (S ...)
  [(get-signals-of-status  ((sig S status) θ) status)
   (S S_r ...)
   (where (S_r ...) (get-signals-of-status θ status))]
  [(get-signals-of-status  (env-v_h θ) status)
   (get-signals-of-status θ status)]
  [(get-signals-of-status · status)
   ()])

(define-metafunction esterel-eval
  get-unready-shared : θ -> (s ...)
  [(get-unready-shared  ((shar s ev shared-status) θ))
   {s s_r ...}
   (judgment-holds (∈ shared-status (new old)))
   (where {s_r ...} (get-unready-shared θ))]
  [(get-unready-shared {env-v_h θ})
   (get-unready-shared θ)]
  [(get-unready-shared ·)
   {}])

(module+ test
  (check-equal?
   `(get-unready-shared ((sig SIb unknown)
                         ((sig Sd unknown)
                          ((sig Sl unknown)
                           ((shar srandom-shared766092 0 new)
                            ((sig Srandom-signal766091 unknown) ·))))))
   '(srandom-shared766092)))


(define-metafunction esterel-eval
  FV : p -> {V ...}
  [(FV nothing) {}]
  [(FV pause) {}]
  [(FV (signal S p)) (without (FV p) S)]
  [(FV (present S p q)) (U {S} (FV p) (FV q))]
  [(FV (emit S)) {S}]
  [(FV (loop p)) (FV p)]
  [(FV (par p q)) (U (FV p) (FV q))]
  [(FV (seq p q)) (U (FV p) (FV q))]
  [(FV (loop^stop p q)) (U (FV p) (FV q))]
  [(FV (suspend p S)) (U {S} (FV p))]
  [(FV (trap p)) (FV p)]
  [(FV (exit n)) {}]
  [(FV (shared s := e p))
   (without (U (FV/e e) (FV p)) s)]
  [(FV (<= s e)) (U {s} (FV/e e))]
  [(FV (var x := e p))
   (without (U (FV/e e) (FV p)) x)]
  [(FV (:= x e)) (U {x} (FV/e e))]
  [(FV (if x p q)) (U {x} (FV p) (FV q))]
  [(FV (ρ θ A p))
   (set-sub (FV p) (vars-in θ))]
  )

(define-metafunction esterel-eval
  set-sub : {any ...} {any ...} -> {any ...}
  [(set-sub {any ...} {}) {any ...}]
  [(set-sub {any_0 ... any_1 any_2 ...} {any_1 any ...})
   (set-sub {any_0 ... any_2 ...} {any_1 any ...})]
  [(set-sub {any_a ...} {any_1 any ...})
   (set-sub {any_a ...} {any ...})])

(define-metafunction esterel-eval
  vars-in : θ -> {V ...}
  [(vars-in ·) {}]
  [(vars-in {(sig S status) θ})
   (U {S} (vars-in θ))]
  [(vars-in {(var· x ev) θ})
   (U {x} (vars-in θ))]
  [(vars-in {(shar s ev shared-status) θ})
   (U {s} (vars-in θ))])

(define-metafunction esterel-eval
  ;; TODO any is bad
  FV/e : any -> (V ...)
  [(FV/e ev) {}]
  [(FV/e V) {V}]
  [(FV/e (f s/l ...))
   (U (FV/e s/l) ...)])

(define-metafunction esterel-eval
  subset : (variable ...) (variable ...) -> boolean
  [(subset () (any ...)) #t]
  [(subset (any_1 any_2 ...) (any_3 ...))
   (subset (any_2 ...) (any_3 ...))
   (judgment-holds (∈ any_1 (any_3 ...)))]
  [(subset any_1 any_2) #f])


;                                
;                                
;                                
;    ;;;;;;                      
;    ;                           
;    ;                           
;    ;         ; ;;;    ;;    ;; 
;    ;         ;;  ;;   ;;    ;  
;    ;         ;    ;    ;   ;;  
;    ;;;;;     ;    ;    ;;  ;   
;    ;         ;    ;    ;;  ;   
;    ;         ;    ;     ;  ;   
;    ;         ;    ;     ; ;    
;    ;         ;    ;      ;;    
;    ;;;;;;    ;    ;      ;;    
;                                
;                                
;                                
;                                
;                                


(define-metafunction esterel-eval
  dom : θ -> {V ...}
  [(dom θ) (vars-in θ)])

(define-metafunction esterel-eval
  <- : θ θ -> θ
  [(<- θ ·) θ]
  [(<- θ {env-v θ_2})
   (θ-set (<- θ θ_2) env-v)])

(module+ test
  (check-equal? (term (<- · ·)) (term ·))
  (check-equal? (term (<- ((sig Sa unknown) ·) ·)) (term ((sig Sa unknown) ·)))
  (check-equal? (term (<- · ((sig Sa present) ·))) (term ((sig Sa present) ·)))
  (check-equal? (term (<- ((sig Sa unknown) ·) ((sig Sa present) ·)))
                (term ((sig Sa present) ·)))
  (check-equal? (term (<- · ((sig Sa unknown) ((sig Sa present) ·))))
                (term ((sig Sa unknown) ·))))

(define-metafunction esterel-eval
  mtθ+x  : x ev -> θ
  [(mtθ+x x ev) {(var· x ev) ·}])

(define-metafunction esterel-eval
  mtθ+s  : s ev shared-status -> θ
  [(mtθ+s s ev shared-status) {(shar s ev shared-status) ·}])

(define-metafunction esterel-eval
  mtθ+S  : S status -> θ
  [(mtθ+S S status) {(sig S status) ·}])

(define-metafunction esterel-eval
  θ-ref : θ V -> env-v or #f
  [(θ-ref · any) #f]
  [(θ-ref {(sig S status) θ} S) (sig S status)]
  [(θ-ref {(var· x ev) θ} x) (var· x ev)]
  [(θ-ref {(shar s ev shared-status) θ} s) (shar s ev shared-status)]
  [(θ-ref {env-v θ} V)
   (θ-ref θ V)])

;; metafunction version of θ-ref-S
(define-metafunction esterel-eval
  θ-get-S : θ S -> status or #f
  [(θ-get-S · any) #f]
  [(θ-get-S {(sig S status) θ} S) status]
  [(θ-get-S {env-v θ} V)
   (θ-get-S θ V)])

(module+ test
  (check-equal? (term (θ-get-S · S)) (term #f))
  (check-equal? (term (θ-get-S {(shar s 0 new) {(sig S1 unknown) ·}} S)) (term #f))
  (check-equal? (term (θ-get-S {(shar s 0 new) {(sig S1 unknown) {(sig S2 present) ·}}} S2))
                (term present))
  (check-equal? (term (θ-get-S {(shar s 0 new) {(sig S1 unknown) {(sig S2 present) ·}}} S1))
                (term unknown)))

(define-judgment-form esterel-eval
  #:mode (θ-ref-S I I O)
  [(where (sig S status) (θ-ref θ S))
   -----------------------------------
   (θ-ref-S θ S status)])

(define-judgment-form esterel-eval
  #:mode (θ-ref-S-∈ I I I)
  #:contract (θ-ref-S-∈ θ S L)
  [(where (sig S status) (θ-ref θ S))
   -----------------------------------
   (θ-ref-S-∈ θ S (status L))]

  [(θ-ref-S-∈ θ S L)
   -----------------------------------
   (θ-ref-S-∈ θ S (status L))])

(module+ test
  (let ([θ (term {(sig S1 unknown) {(sig S2 present) {(sig S3 unknown) ·}}})])
    (check-false (judgment-holds (θ-ref-S-∈ ,θ S0 ())))
    (check-false (judgment-holds (θ-ref-S-∈ ,θ S1 ())))
    (check-false (judgment-holds (θ-ref-S-∈ ,θ S2 ())))
    (check-false (judgment-holds (θ-ref-S-∈ ,θ S3 ())))

    (check-false (judgment-holds (θ-ref-S-∈ ,θ S0 (present (unknown ())))))
    (check-false (judgment-holds (θ-ref-S-∈ ,θ S1 (present ()))))
    (check-true (judgment-holds (θ-ref-S-∈ ,θ S1 (present (unknown ())))))
    (check-true  (judgment-holds (θ-ref-S-∈ ,θ S2 (present (unknown ())))))
    (check-true  (judgment-holds (θ-ref-S-∈ ,θ S3 (present (unknown ()))))))

  ;; make sure only the first binding of a given variable counts
  (check-false (judgment-holds (θ-ref-S-∈ {(sig S unknown) {(sig S present) ·}} S0 (present ())))))

(define-judgment-form esterel-eval
  #:mode (¬θ-ref-S I I I)
  [(where (sig S status_!_1) (θ-ref θ S))
   -----------------------------------
   (¬θ-ref-S θ S status_!_1)])

(define-judgment-form esterel-eval
  #:mode (θ-ref-s I I O O)
  [(where (shar s ev shared-status) (θ-ref θ s))
   ----------------------------------------------
   (θ-ref-s θ s ev shared-status)])

(define-judgment-form esterel-eval
  #:mode (θ-ref-x I I O)
  [(where (var· x ev) (θ-ref θ x))
   -------------------------------
   (θ-ref-x θ x ev)])

(define-judgment-form esterel-eval
  #:mode (θ-ref-x-but-also-rvalue-false-is-ok-if-ev-is-zero I I O)
  [(where (var· x ev) (θ-ref θ x))
   --------------------------------------------
   (θ-ref-x-but-also-rvalue-false-is-ok-if-ev-is-zero θ x ev)]

  [(where (var· x (rvalue #f)) (θ-ref θ x))
   --------------------------------------------
   (θ-ref-x-but-also-rvalue-false-is-ok-if-ev-is-zero θ x 0)])

(module+ test
  (check-false (judgment-holds (θ-ref-x ·                                 x 0)))
  (check-false (judgment-holds (θ-ref-x ((var· x 0) ·)                    x 1)))
  (check-true  (judgment-holds (θ-ref-x ((var· x 0) ·)                    x 0)))
  (check-false (judgment-holds (θ-ref-x ((sig S1 unknown) ((var· x 0) ·)) x 1)))
  (check-true  (judgment-holds (θ-ref-x ((sig S1 unknown) ((var· x 0) ·)) x 0))))

(define-judgment-form esterel-eval
  #:mode (¬θ-ref-x I I I)
  #:contract (¬θ-ref-x θ x ev)

  [(θ-ref-x θ x ev_2)
   (side-condition (different ev_1 ev_2))
   -------------------------------------------------------
   (¬θ-ref-x θ x ev_1)])

(define-judgment-form esterel-eval
  #:mode (¬θ-ref-x-and-also-not-rvalue-false I I I)
  #:contract (¬θ-ref-x-and-also-not-rvalue-false θ x ev)

  [(θ-ref-x θ x ev_2)
   (side-condition (different ev_1 ev_2))
   (side-condition (different ev_2 (rvalue #f)))
   -------------------------------------------------------
   (¬θ-ref-x-and-also-not-rvalue-false θ x ev_1)])

(module+ test
  (check-false (judgment-holds (¬θ-ref-x ·                                 x 0)))
  (check-true  (judgment-holds (¬θ-ref-x ((var· x 0) ·)                    x 1)))
  (check-false (judgment-holds (¬θ-ref-x ((var· x 0) ·)                    x 0)))
  (check-true  (judgment-holds (¬θ-ref-x ((sig S1 unknown) ((var· x 0) ·)) x 1)))
  (check-false (judgment-holds (¬θ-ref-x ((sig S1 unknown) ((var· x 0) ·)) x 0))))

(define-metafunction esterel-eval
  θ-set : θ env-v -> θ
  [(θ-set θ env-v)
   ,(resort `θ_2)
   (where θ_2 (θ-set* θ env-v))])

(define-metafunction esterel-eval
  θ-set* : θ env-v -> θ
  [(θ-set* · env-v) (env-v ·)]
  [(θ-set* ((sig S status) θ) (sig S status_2))
   ((sig S status_2) θ)]
  [(θ-set* ((shar s ev shared-status) θ) (shar s ev_2 shared-status_2))
   ((shar s ev_2 shared-status_2) θ)]
  [(θ-set* ((var· x ev) θ) (var· x ev_2))
   ((var· x ev_2) θ)]
  [(θ-set* (env-v θ) env-v_s)
   (env-v (θ-set* θ env-v_s))])
(module+ test
  (check-equal?
   `(θ-set* ((var· x 1) ·) (var· x 2))
   `((var· x 2) ·)))

(define-metafunction esterel-eval
  Lwithoutdom : θ S -> θ
  [(Lwithoutdom · S) ·]
  [(Lwithoutdom {(sig S status) θ_1} S) (Lwithoutdom θ_1 S)]
  [(Lwithoutdom {(sig S_1 status) θ} S_2)
   {(sig S_1 status) (Lwithoutdom θ S)}]
  [(Lwithoutdom {(shar s ev shared-status) θ} S)
   {(shar s ev shared-status) (Lwithoutdom θ S)}]
  [(Lwithoutdom {(var· x ev) θ} S)
   {(var· x ev) (Lwithoutdom θ S)}])

(module+ test
  (check-equal? (term (Lwithoutdom · S)) (term ·))
  (check-equal? (term (Lwithoutdom ({shar s 0 new} ({sig S unknown} ·)) S))
                (term ({shar s 0 new} ·)))
  (check-equal? (term (Lwithoutdom ({var· x 11} ({shar s 0 new} ({sig S unknown} ·))) S))
                (term ({var· x 11} ({shar s 0 new} ·))))
  (check-equal? (term (Lwithoutdom ({sig S present} ({sig S unknown} ·)) S))
                (term ·))
  (check-equal? (term (Lwithoutdom ({sig S1 present}
                                    ({sig S present}
                                     ({sig S2 present}
                                      ({sig S unknown}
                                       ({sig S3 unknown}
                                        ·)))))
                                   S))
                (term ({sig S1 present}
                       ({sig S2 present}
                        ({sig S3 unknown}·))))))

(define-judgment-form esterel-eval
  #:mode (L∈dom O I)
  #:contract (L∈dom S θ)
  [----------------------------------------------
   (L∈dom S {(sig S status) θ_1})]

  [(L∈dom S θ)
   ----------------------------------------------
   (L∈dom S {(shar s ev shared-status) θ})]

  [(L∈dom S θ)
   ----------------------------------------------
   (L∈dom S {(var· x ev) θ})])

(module+ test
  (check-true (judgment-holds (L∈dom S ({sig S unknown} ·))))
  (check-true (judgment-holds (L∈dom S ({shar s 0 new} ({sig S unknown} ·)))))
  (check-true (judgment-holds (L∈dom S ({shar s 0 new} ({var· x 11} ({sig S unknown} ·))))))
  (check-false (judgment-holds (L∈dom S1 ({sig S2 unknown} ·)))))

(define (resort l)
  (define flt
    (let loop ([l l])
      (match l
        ['· empty]
        [(list v r)
         (cons v (loop r))])))
  (define fixed (sort flt symbol<? #:key second))
  (let loop ([l fixed])
    (match l
      [(list) '·]
      [(cons f r)
       (list f (loop r))])))

(module+ test
  (check-equal? (resort (term ·)) (term ·))
  (check-equal? (resort (term {(sig S unknown) {(sig T present) ·}}))
                (term {(sig S unknown) {(sig T present) ·}}))
  (check-equal? (resort (term {(sig T present) {(sig S unknown) ·}}))
                (term {(sig S unknown) {(sig T present) ·}}))
  (check-equal? (resort (term {(sig S present) {(sig S unknown) ·}}))
                (term {(sig S present) {(sig S unknown) ·}})))

(define-metafunction esterel-eval
  id-but-typeset-some-parens : any -> any
  [(id-but-typeset-some-parens any) any])
