#lang racket
(require redex/reduction-semantics racket/random)
(provide (all-defined-out))

(define-syntax quasiquote (make-rename-transformer #'term))

(define-syntax-rule (render-derivations r)
    (show-derivations (build-derivations r)))

(define-struct esterel-top-procedure (code proc)
  #:property prop:procedure (struct-field-index proc)
  #:methods gen:custom-write
  [(define write-proc
     (lambda (s p mode)
       (define f
         (case mode
           [(#t) write]
           [(#f) display]
           [else (lambda (p port) (print p port mode))]))
       (f (list
           'make-esterel-top-procedure
           (esterel-top-procedure-code s)) p)))])


;                                              
;                                              
;                                              
;                                              
;   ;;;    ;                                   
;   ;;;    ;                 ;                 
;   ;;;;   ;                 ;                 
;   ;;;;   ;    ;;;;;     ;;;;;;;      ;;;;;   
;   ;; ;   ;    ;   ;;       ;        ;;   ;;  
;   ;; ;;  ;         ;;      ;        ;        
;   ;; ;;  ;         ;;      ;        ;;       
;   ;;  ;; ;     ;;;;;;      ;         ;;;;    
;   ;;  ;; ;    ;;   ;;      ;           ;;;   
;   ;;   ; ;   ;;    ;;      ;             ;;  
;   ;;   ;;;   ;;    ;;      ;             ;;  
;   ;;    ;;    ;;  ;;;      ;;  ;    ;;  ;;;  
;   ;;    ;;    ;;;;  ;       ;;;;   ; ;;;;    
;                                              
;                                              
;                                              
;                                              
;                                              


(define-language nats
  (nat zero  (Succ nat))
  (one (Succ zero)) (two (Succ (Succ zero))) (three (Succ (Succ (Succ zero)))))

(define-term one (Succ zero))
(define-term two (Succ (Succ zero)))
(define-term three (Succ (Succ (Succ zero))))

(define-metafunction nats
  to-nat : natural -> nat
  [(to-nat 0) zero]
  [(to-nat natural) (Succ (to-nat ,(sub1 `natural)))])

(define-metafunction nats
  nat- : nat nat -> nat
  [(nat- nat zero) nat]
  [(nat- zero _) zero]
  [(nat- (Succ nat_1) (Succ nat_2))
   (nat- nat_1 nat_2)]
  [(nat- nat_1 nat_2) (nat- (natnorm nat_1) (natnorm nat_2))])

(define-metafunction  nats
  nat+ : nat nat -> nat
  [(nat+ nat zero) nat]
  [(nat+ nat_1 (Succ nat_2)) (nat+ (Succ nat_1) nat_2)]
  [(nat+ nat_1 nat_2) (nat+ nat_1 (natnorm nat_2))])

(define-metafunction  nats
  [(nat<= zero nat) #t]
  [(nat<= nat zero) #f]
  [(nat<= (Succ nat_1) (Succ nat_2)) (nat<= nat_1 nat_2)]
  [(nat<= nat_1 nat_2) (nat<= (natnorm nat_1) (natnorm nat_2))])

(define-metafunction  nats
  [(nat= zero zero) #t]
  [(nat= nat zero) #f]
  [(nat= zero nat) #f]
  [(nat= (Succ nat_1) (Succ nat_2)) (nat= nat_1 nat_2)]
  [(nat= nat_1 nat_2) (nat= (natnorm nat_1) (natnorm nat_2))])

(define-metafunction nats
  [(natnorm zero) zero]
  [(natnorm one) (Succ zero)]
  [(natnorm two) (Succ (natnorm one))]
  [(natnorm three) (Succ (natnorm two))]
  [(natnorm (Succ nat)) (Succ (natnorm nat))])


;                                                                               
;                                                                               
;                                                                               
;                                                                               
;      ;;;;                                                                     
;     ;;  ;;;                                                                   
;    ;;                                                                         
;   ;;          ;;; ;;;;   ;;;;;     ; ;;  ;;   ; ;;  ;;    ;;;;;      ;;; ;;;; 
;   ;;           ;;;; ;    ;   ;;    ;; ;;; ;;  ;; ;;; ;;   ;   ;;      ;;;; ;  
;   ;;           ;;;  ;         ;;   ;   ;  ;;  ;   ;  ;;        ;;     ;;;  ;  
;   ;    ;;;;    ;;             ;;   ;   ;  ;;  ;   ;  ;;        ;;     ;;      
;   ;;     ;;    ;;         ;;;;;;   ;   ;  ;;  ;   ;  ;;    ;;;;;;     ;;      
;   ;;     ;;    ;;        ;;   ;;   ;   ;  ;;  ;   ;  ;;   ;;   ;;     ;;      
;   ;;     ;;    ;;       ;;    ;;   ;   ;  ;;  ;   ;  ;;  ;;    ;;     ;;      
;    ;     ;;    ;;       ;;    ;;   ;   ;  ;;  ;   ;  ;;  ;;    ;;     ;;      
;    ;;;  ;;;    ;;        ;;  ;;;   ;   ;  ;;  ;   ;  ;;   ;;  ;;;     ;;      
;      ;;;;     ;;;;;      ;;;;  ;   ;   ;  ;;  ;   ;  ;;   ;;;;  ;    ;;;;;    
;                                                                               
;                                                                               
;                                                                               
;                                                                               
;                                                                               


(define-extended-language esterel nats
  ((p q)
   nothing
   pause
   (seq p q)
   (par p q)
   (loop p)
   (suspend p S)
   (present S p q)
   (trap p)
   (exit k)
   (emit S)
   (var v := call p)
   (shared s := call p)
   (signal S p)
   (:= v call)
   (<= s call)
   (if v p q))

  ((phat qhat)
   (hat pause)
   (present S phat q)
   (present S p qhat)
   (seq phat q)
   (seq p qhat)
   (suspend phat S)
   (loop phat)
   (par phat qbar)
   (par pbar qhat)
   (trap phat)
   (var v := call phat)
   (shared s := call phat)
   (signal S phat)
   (if v phat q)
   (if v p qhat))

  ((pbar qbar) p phat)

  ((pbardot qbardot)
   (· pbar)
   (seq pbardot p)
   (seq p pbardot)
   (par pbardot ⊥ pbardot ⊥)
   (par pbardot ⊥ pbar l)
   (par pbar k pbardot ⊥)
   (par pbar k pbar l)
   (loop lstat pbardot)
   (suspend pbardot S)
   (present S pbardot p)
   (present S p pbardot)
   (trap pbardot)
   (var v := call pbardot)
   (shared s := call pbardot)
   (signal S sstat pbardot)
   (if v pbardot q)
   (if v p qbardot))

  (call (+ call call) (+ call) (+) v s
        (rfunc s ... datum)
        datum)
  (datum natural
         any;; ENV->any/c racket functions
         )

  ((pdotdot qdotdot) pbardot pbar)

  ((S v s) variable-not-otherwise-mentioned)

  (lstat none stop go)
  (pstat ⊥ l k)
  ((l k m) nat)
  (sstat ⊥ one zero))
(define-extended-language esterel-eval esterel
  (E ((S sstat) ...))
  (K (k ...))
  (V (v ...))
  (e ⊥ S)
  ((l k m) .... ⊥)
  (data (data-elem ...))
  (data-elem (dvar v datum)
             (dshared s datum shared-stat))
  (shared-stat ready old new)

  (M (machine pdotdot data)))


;                                                                                                     
;                                                                                                     
;                                                                                                     
;                               ;;                                       ;;                           
;    ;;;;;;                     ;;                                       ;;;                          
;    ;    ;;                    ;;                            ;                                       
;    ;     ;;                   ;;                            ;                                       
;    ;     ;;     ;;;;      ;;;;;;    ;    ;;      ;;;;    ;;;;;;;     ;;;;;       ;;;;      ;  ;;;   
;    ;     ;;   ;;   ;;    ;;  ;;;    ;    ;;     ;;  ;;      ;           ;;      ;;   ;;    ;;;  ;;  
;    ;    ;;    ;     ;    ;    ;;    ;    ;;    ;;           ;           ;;      ;    ;;    ;;   ;;  
;    ;;;;;;     ;     ;   ;;    ;;    ;    ;;    ;            ;           ;;     ;;     ;    ;    ;;  
;    ;  ;;     ;;;;;;;;   ;;    ;;    ;    ;;    ;            ;           ;;     ;;     ;    ;    ;;  
;    ;   ;;    ;;         ;;    ;;    ;    ;;    ;            ;           ;;     ;;     ;    ;    ;;  
;    ;   ;;     ;         ;;    ;;    ;    ;;    ;            ;           ;;     ;;     ;    ;    ;;  
;    ;    ;;    ;;         ;    ;;    ;    ;;    ;;           ;           ;;      ;    ;;    ;    ;;  
;    ;     ;    ;;;  ;;    ;;  ;;;    ;;  ;;;     ;;  ;;      ;;  ;       ;;      ;;  ;;;    ;    ;;  
;    ;     ;;     ;;;;      ;;;  ;     ;;;  ;      ;;;;        ;;;;    ;;;;;;;     ;;;;      ;    ;;  
;                                                                                                     
;                                                                                                     
;                                                                                                     
;                                                                                                     
;                                                                                                     


(define-judgment-form esterel-eval
  #:mode     (→ I I I O O O O)
  #:contract (→ pdotdot data E pdotdot data e k)
  #|
  [------------
  ""
  (→ )]
  |#
  [------------
   "1"
   (→ (· nothing) data E
      nothing data ⊥ zero)]
  [------------
   "2"
   (→ (· pause) data E
      (hat pause) data ⊥ (Succ zero))]
  [------------
   "3"
   (→ (· (hat pause)) data E
      pause data ⊥ zero)]
  [------------
   "4"
   (→ (· (seq pbar q)) data E
      (seq (· pbar) q) data ⊥ ⊥)]

  [(→ pbardot data E pdotdot data_* e k)
   (side-condition ,(not (equal? `k `zero)))
   ------------
   "5"
   (→ (seq pbardot q) data E
      (seq pdotdot q) data_* e k)]

  [(→ pbardot data E p data_* e zero)
   ------------
   "6"
   (→ (seq pbardot q) data E
      (seq p (· q)) data_* e ⊥)]

  [------------
   "7"
   (→ (· (seq p qhat)) data E
      (seq p (· qhat)) data ⊥ ⊥)]
  [(→ qbardot data E qdotdot data_* e m)
   ------------
   "8"
   (→ (seq p qbardot) data E
      (seq p qdotdot) data_* e m)]
  [------------
   "9"
   (→ (· (par p q)) data E
      (par (· p) ⊥ (· q) ⊥) data ⊥ ⊥)]
  [------------
   "10"
   (→ (· (par phat qhat)) data E
      (par (· phat) ⊥ (· qhat) ⊥) data ⊥ ⊥)]
  [------------
   "11"
   (→ (· (par phat q)) data E
      (par (· phat) ⊥  q zero) data ⊥ ⊥)]
  [------------
   "12"
   (→ (· (par p qhat)) data E
      (par p zero (· qhat) ⊥) data ⊥ ⊥)]
  [------------
   "13"
   (→ (par pbar k qbar l) data E
      (par pbar qbar) data ⊥ (meta-max k l))]


  [------------
   "16"
   (→ (· (loop p)) data E
      (loop stop (· p)) data ⊥ ⊥)]

  [------------
   "17"
   (→ (· (loop phat)) data E
      (loop go (· phat)) data ⊥ ⊥)]

  [(→ pbardot data E
      p data_* e zero)
   ------------
   "18"
   (→ (loop go pbardot) data E
      (loop stop (· p)) data_* e ⊥)]

  [(→ pbardot data E
      pbar data_* e k)
   (side-condition ,(and (not (equal? `k `⊥))
                         (not (equal? `k `zero))))
   ------------
   "19"
   (→ (loop lstat pbardot) data E
      (loop pbar) data_* e k)]

  ;; BLATANT TYPO data is missing? (page 103)
  [(→ pbardot data E
      pbardot_* data_* e ⊥)
   ------------
   "20"
   (→ (loop lstat pbardot) data E
      (loop lstat pbardot_*) data_* e ⊥)]

  [------------
   "21"
   (→ (· (trap pbar)) data E
      (trap (· pbar)) data ⊥ ⊥)]
  [(→ pbardot data E pbardot_′ data_′ e ⊥)
   ----------------------------------------------------- "22"
   (→ (trap pbardot) data E (trap pbardot_′) data_′ e ⊥)]

  ;; TODO pbar and p used in rule? does that mean remove any pauses?
  ;; (page 89)
  [(→ pbardot data E pbar data_′ ⊥ two)
   --------------------------------------------------------------- "23"
   (→  (trap pbardot) data E (trap (deselect pbar)) data_′ ⊥ zero)]

  [(→ pbardot data E
      p data_* e zero)
   ------------
   "24"
   (→  (trap pbardot) data E
       (trap p) data_* e zero)]

  [(→ pbardot data E
      phat data_* ⊥ one)
   ------------
   "25"
   (→  (trap pbardot) data E
       (trap phat) data_* ⊥ one)]

  [(→ pbardot data E
      pbar data ⊥ k)
   (where nat k)
   ;; k >= 3
   (side-condition (nat<= (Succ (Succ (Succ zero))) k))
   ------------
   "26"
   (→  (trap pbardot) data E
       (trap pbar) data ⊥ (↓ k))]

  [------------
   "27"
   (→ (· (exit k)) data E
      (exit k) data ⊥ k)]

  [------------
   "28"
   (→ (· (signal S pbar)) data E
      (signal S ⊥ (· pbar)) data ⊥ ⊥)]

  [(→ pbardot data (* E (S m))
      ;;TODO should this really be the same data?
      pbardot_* data S ⊥)
   (side-condition (∈ m (⊥ (Succ zero))))
   ------------
   "29"
   (→ (signal S m pbardot) data E
      (signal S (Succ zero) pbardot_*) data ⊥ ⊥)]

  ;; TODO (page 105) confusing S should be decorated with 1, 0, or ⊥
  ;; assuming to mean (S 1) is not in Can_S?

  [(side-condition (∉ (S (Succ zero)) (Can_S pbardot (* E (S ⊥)))))
   ------------
   "30"
   (→ (signal S ⊥ pbardot) data E
      (signal S zero pbardot) data ⊥ ⊥)]

  [(→ pbardot data (* E (S m))
      qbardot data_* e ⊥)
   (side-condition ,(not (equal? `e `S)))
   ;; added to avoid unneeded non-determinism
   (side-condition ,(or
                     (not (equal? `⊥ `m))
                     (not `(∉ (S one) (Can_S pbardot (* E (S ⊥)))))))
   ------------
   "31"
   (→ (signal S m pbardot) data E
      (signal S m qbardot) data_* e ⊥)]

  [(→ pbardot data (* E (S m))
      qbar data_* e k)
   (side-condition ,(not (equal? `k `⊥)))
   (side-condition ,(not (equal? `e `S)))
   ;; added to avoid unneeded non-determinism
   (side-condition ,(or
                     (not (equal? `⊥ `m))
                     (not `(∉ (S (Succ zero)) (Can_S pbardot (* E (S ⊥)))))))
   ------------
   "32"
   (→ (signal S m pbardot) data E
      (signal S qbar) data_* e k)]


  [(→ pbardot data (* E (S m))
      qbar data_* S k)
   (side-condition ,(not (equal? `k `⊥)))
   ;; added to avoid unneeded non-determinism
   (side-condition ,(or
                     (not (equal? `⊥ `m))
                     (not `(∉ (S one) (Can_S pbardot (* E (S ⊥)))))))
   ------------
   "33"
   (→ (signal S m pbardot) data E
      (signal S qbar) data_* ⊥ k)]

  [------------
   "34"
   (→ (· (emit S)) data E
      (emit S) data S zero)]

  [(where #t (∈ (S (Succ zero)) E))
   ------------
   "35"
   (→ (· (suspend phat S)) data E
      (suspend phat S) data ⊥ (Succ zero))]

  [(where #t (∈ (S zero) E))
   ------------
   "36"
   (→ (· (suspend phat S)) data E
      (suspend (· phat) S) data ⊥ ⊥)]

  [------------
   "37"
   (→ (· (suspend p S)) data E
      (suspend (· p) S) data ⊥ ⊥)]

  [(→ pbardot data E pdotdot data_* e k)
   ------------
   "38"
   (→ (suspend pbardot S) data E
      (suspend pdotdot S) data_* e k)]

  [(where #t (∈ (S (Succ zero)) E))
   ------------
   "39"
   (→ (· (present S p q)) data E
      (present S (· p) q) data ⊥ ⊥)]

  [(where #t (∈ (S zero) E))
   ------------
   "40"
   (→ (· (present S p q)) data E
      (present S p (· q)) data ⊥ ⊥)]

  [------------
   "41"
   (→ (· (present S phat q)) data E
      (present S (· phat) q) data ⊥ ⊥)]
  [------------
   "42"
   (→ (· (present S p qhat)) data E
      (present S p (· qhat)) data ⊥ ⊥)]

  [(→ pbardot data E pdotdot data_* e k)
   ------------
   "43"
   (→ (present S pbardot q) data E
      (present S pdotdot q) data_* e k)]

  [(→ qbardot data E qdotdot data_* e k)
   ------------
   "44"
   (→ (present S p qbardot) data E
      (present S p qdotdot) data_* e k)]

  [(where (s ...) (shared-of call_init data))
   (where (ready ...) ((data-ref data (s status)) ...))
   (where data_* (data<- data
                         s_set
                         (eval-call call_init data)
                         old))
   ------------
   "45"
   (→ (· (shared s_set := call_init p)) data E
      (shared s_set := call_init (· p)) data_* ⊥ ⊥)]

  [------------
   "46"
   (→ (· (shared s := call_init phat)) data E
      (shared s := call_init (· phat)) (data<- data (s status) old) ⊥ ⊥)]
  [(where #t (∈ (data-ref data (s status))
                (old new)))
   (where #t (∉ s (Can_V pbardot E)))
   ------------
   "47"
   (→ (shared s := call_init pbardot) data E
      (shared s := call_init pbardot) (data<- data (s status) ready) ⊥ ⊥)]

  [(→ pbardot data E pdotdot data_* e k)
   ;; added to avoid nondeterminism
   (where #t
          (meta-or ((∈ s (Can_V pbardot E))
                    (∈ (data-ref data (s status)) (ready)))))
   ------------
   "48"
   (→ (shared s := call_init pbardot) data E
      (shared s := call_init pdotdot) data_* e k)]

  [(where old (data-ref data (s status)))

   (where (s_shared ...) (shared-of call data))
   (where (ready ...) ((data-ref data (s_shared status)) ...))

   (where data_* (data<- data (s status) new))
   (where data_** (data<- data_* (s value) (eval-call call data)))
   ------------
   "49"
   (→ (· (<= s call)) data E
      (<= s call) data_** ⊥ zero)]

  [(where new (data-ref data (s status)))

   (where (s_shared ...) (shared-of call data))
   (where (ready ...) ((data-ref data (s_shared status)) ...))

   (where datum_this (eval-call call data))
   (where datum_new (eval-call (+ (data-ref data (s value)) datum_this) data))
   (where data_* (data<- data (s value) datum_new))
   ------------
   "50"
   (→ (· (<= s call)) data E
      (<= s call) data_* ⊥ zero)]

  [(where (s_shared ...) (shared-of call data))
   (where (ready ...) ((data-ref data (s_shared status)) ...))

   (where data_* (data<- data v (eval-call call data)))
   ----------
   "51"
   (→ (· (var v := call p)) data E
      (var v := call (· p)) data_* ⊥ ⊥)]

  [----------
   "52"
   (→ (· (var v := call phat)) data E
      (var v := call (· phat)) data ⊥ ⊥)]

  [(→ pbardot data E
      pdotdot data_* e k)
   ----------
   "53"
   (→ (var v := call pbardot) data E
      (var v := call pdotdot) data_* e k)]

  [(where #t (∉ (data-ref data v)
                (0 #f)))
   ----------
   "54"
   (→ (· (if v p q)) data E
      (if v (· p) q) data ⊥ ⊥)]

  [(where #t (∈ (data-ref data v)
                (0 #f)))
   ----------
   "55"
   (→ (· (if v p q)) data E
      (if v p (· q)) data ⊥ ⊥)]

  [----------
   "56"
   (→ (· (if v phat q)) data E
      (if v (· phat) q) data ⊥ ⊥)]

  [----------
   "57"
   (→ (· (if v p qhat)) data E
      (if v p (· qhat)) data ⊥ ⊥)]

  [(→ pbardot data E
      pdotdot data_* e k)
   ----------
   "58"
   (→ (if v pbardot q) data E
      (if v pdotdot q) data_* e k)]

  [(→ qbardot data E
      qdotdot data_* e k)
   ----------
   "59"
   (→ (if v p qbardot) data E
      (if v p qdotdot) data_* e k)]

  [(where (s_shared ...) (shared-of call data))
   (where (ready ...) ((data-ref data (s_shared status)) ...))

   (where datum (eval-call call data))
   (where data_* (data<- data v datum))
   ------------
   "60"
   (→ (· (:= v call)) data E
      (:= v call) data_* ⊥ zero)])

(define-extended-judgment-form esterel-eval →
  #:mode     (non-det-> I I I O O O O)
  #:contract (non-det-> pdotdot data E pdotdot data e k)
  [(non-det-> pbardot data E pdotdot data_* e k)
   ------------
   "14"
   (non-det-> (par pbardot ⊥ qdotdot m) data E
              (par pdotdot k qdotdot m) data_* e ⊥)]

  [(non-det-> qbardot data E qdotdot data_* e k)
   ------------
   "15"
   (non-det-> (par pdotdot m qbardot ⊥) data E
              (par pdotdot m qdotdot k) data_* e ⊥)])

(define-extended-judgment-form esterel-eval →
  #:mode     (det-> I I I O O O O)
  #:contract (det-> pdotdot data E pdotdot data e k)
  ;; morally were 14 an(seq (trap (par (exit 0) pause)) (emit rX)))d 15. change to be deterministic
  [(det-> pbardot data E pdotdot data_* e k)
   ------------
   (det-> (par pbardot ⊥ qdotdot m) data E
          (par pdotdot k qdotdot m) data_* e ⊥)]

  [(where #f ,(judgment-holds (det-> pdotdot data E pdotdot data_* e k)))
   (det-> qbardot data E qdotdot data_* e k)
   ------------
   (det-> (par pdotdot m qbardot ⊥) data E
          (par pdotdot m qdotdot k) data_* e ⊥)])

(define-metafunction esterel-eval
  meta-or : (boolean ...) -> boolean
  [(meta-or ()) #f]
  [(meta-or (#f any ...))
   (meta-or (any ...))]
  [(meta-or (#t any ...)) #t])

(define-metafunction esterel-eval
  shared-of : call data -> (s ...)
  [(shared-of s data)
   (s)
   (where (any_1 ... (dshared s datum shared-stat) any_2 ...)
          data)]
  [(shared-of v data) ()]
  [(shared-of (+) data) ()]
  [(shared-of (+ call ...) data)
   (U (shared-of call data) ...)]
  [(shared-of (rfunc s ... datum) data) (s ...)]
  [(shared-of datum data) ()])

(define-extended-language ref-lang esterel-eval
  (input ::= v s (s status) (s value))
  (output ::= datum shared-stat))
(define-metafunction ref-lang
  data-ref : data input -> output
  [(data-ref (any_1 .... (dvar v datum) any_2 ...) v) datum]
  [(data-ref (any_1 .... (dshared s datum shared-stat) any_2 ...)
             (s status))
   shared-stat]
  [(data-ref (any_1 .... (dshared s datum shared-stat) any_2 ...)
             (s value))
   datum])
(define-metafunction ref-lang
  data-ref-ext : data input -> output
  [(data-ref-ext (any_1 .... (dvar v datum) any_2 ...) v) datum]
  [(data-ref-ext (any_1 .... (dshared s datum shared-stat) any_2 ...)
                 (s status))
   shared-stat]
  [(data-ref-ext (any_1 .... (dshared s datum shared-stat) any_2 ...)
             (s value))
   datum]
  [(data-ref-ext any ...) #f])


;                                              
;                                              
;                                              
;                                    ;;;;;     
;    ;;;;;;;                            ;;     
;    ;;                                 ;;     
;    ;;                                 ;;     
;    ;;        ;;     ;;   ;;;;;        ;;     
;    ;;         ;     ;    ;   ;;       ;;     
;    ;;         ;;   ;;         ;;      ;;     
;    ;;;;;;     ;;   ;;         ;;      ;;     
;    ;;          ;   ;      ;;;;;;      ;;     
;    ;;          ;  ;;     ;;   ;;      ;;     
;    ;;          ;; ;     ;;    ;;      ;;     
;    ;;           ; ;     ;;    ;;      ;;     
;    ;;           ;;;      ;;  ;;;      ;;  ;  
;    ;;;;;;;      ;;       ;;;;  ;       ;;;;  
;                                              
;                                              
;                                              
;                                              
;                                              



(define-metafunction esterel-eval
  eval-call : call data -> datum
  [(eval-call s data)
   (data-ref data (s value))
   (where #t (∈ s (shared-of s data)))]
  [(eval-call v data) (data-ref data v)]
  [(eval-call (+ call ...) data)
   ,(apply + `(datum ...))
   (where (datum ...) ((eval-call call data) ...))]
  [(eval-call (rfunc s ... any) data)
   ,(if (esterel-top-procedure? `any)
        (`any `data)
        `any)]
  [(eval-call any data)
   ,(if (esterel-top-procedure? `any)
        (`any `data)
        `any)])

(define-metafunction esterel-eval
  ;data<- : data v datum -> data
  ;data<- : data s datum shared-stat -> data
  ;data<- : data (s value) datum -> data
  ;data<- : data (s status) shared-stat -> data
  [(data<- (any_1 ... (dvar v any) any_2 ...) v datum)
   (any_1 ... (dvar v datum) any_2 ...)]
  [(data<- (any ...) v datum)
   ((dvar v datum) any ...)]
  [(data<- (any_1 ... (dshared s any_3 any_4) any_2 ...) s datum shared-stat)
   (any_1 ... (dshared s datum shared-stat) any_2 ...)]
  [(data<- (any ...) s datum shared-stat)
   ((dshared s datum shared-stat) any ...)]
  [(data<- (any_1 ... (dshared s any shared-stat) any_2 ...) (s value) datum)
   (any_1 ... (dshared s datum shared-stat) any_2 ...)]
  [(data<- (any_1 ... (dshared s datum any) any_2 ...) (s status) shared-stat)
   (any_1 ... (dshared s datum shared-stat) any_2 ...)])

(define-metafunction esterel-eval
  eval : M E -> (M (S ...))
  [(eval (machine pbar data) E)
   (M (S ...))
   (where ((M (S ...)))
          ,(judgment-holds
            (eval->> (machine (· pbar) data) E
                     M (S ...))
            (M (S ...))))]
  [(eval (machine pbar data) E)
   ,(error 'eval
           "evaluation failed for ~a.\nGot ~a\n"
           (pretty-format (list 'eval `(machine pbar data) `E))
           (pretty-format `(any ...)))
   (where (any ...)
          ,(judgment-holds
            (eval->> (machine (· pbar) data) E
                     M (S ...))
            (M (S ...))))])
;; judgment form for raw evaluation
(define-judgment-form esterel-eval
  #:mode     (eval->> I I O O)
  #:contract (eval->> M E M (S ...))

  [(where
    ((M S k) any ...)
    ,(judgment-holds
      (det-> pdotdot data E
             pdotdot_* data_* S k)
      ((machine pdotdot_* data_*) S k)))
   (where #f ,(equal? `⊥ `k))
   -----------
   (eval->> (machine pdotdot data) E
            M (S))]
  [(where
    ((M k) any ...)
    ,(judgment-holds
      (det-> pdotdot data E
             pdotdot_* data_* ⊥ k)
      ((machine pdotdot_* data_*) k)))
   (where #f ,(equal? `⊥ `k))
   -----------
   (eval->> (machine pdotdot data) E
            M ())]

  [(where
    ((M S_n) any ...)
    ,(judgment-holds
      (det-> pdotdot data E
             pdotdot_* data_* S ⊥)
      ((machine pdotdot_* data_*) S)))

   (eval->> M E (machine pdotdot_** data_**) (S ...))
   -----------
   (eval->> (machine pdotdot data) E
            (machine pdotdot_** data_**) (S_n S ...))]
  [(where
    (M any ...)
    ,(judgment-holds
      (det-> pdotdot data E
             pdotdot_* data_* ⊥ ⊥)
      (machine pdotdot_* data_*)))

   (eval->> M E (machine pdotdot_** data_**) (S ...))
   -----------
   (eval->> (machine pdotdot data) E
            (machine pdotdot_** data_**) (S ...))]

  [(where
    ()
    ,(judgment-holds
      (det-> pdotdot data E
             pdotdot_* data_* any_1 any_2)
      (machine pdotdot_* data_*)))

   (side-condition
    ,(error 'eval "evaluation stuck at: ~a\n~a"
            (pretty-format `(machine pdotdot data))
            (pretty-format `E)))
   ;; never run just here to make code compile
   (eval->> (machine pdotdot data) E
            (machine pdotdot_** data_**) (S ...))
   -----------
   (eval->> (machine pdotdot data) E
            (machine pdotdot_** data_**) (S ...))])

(define-judgment-form esterel-eval
  #:mode     (→* I I O  O      O)
  #:contract (→* M E M (S ...) k)
  [(non-det-> pdotdot data E
              pdotdot_* data_* ⊥ k)
   -----------
   (→* (machine pdotdot data) E
       (machine pdotdot_* data_*) () k)]

  [(non-det-> pdotdot data E
              pdotdot_* data S k)
   -----------
   (→* (machine pdotdot data) E
       (machine pdotdot_* data) (S) k)]

  [(non-det-> pdotdot data E
              pdotdot_* data_* S ⊥)
   (→* (machine pdotdot_* data_*) E
       (machine pdotdot_** data_**) (S_r ...) k)
   -----------
   (→* (machine pdotdot data) E
       (machine pdotdot_** data_**) (U (S) (S_r ...)) k)]

  [(non-det-> pdotdot data E
              pdotdot_* data_* ⊥ ⊥)
   (→* (machine pdotdot_* data_*) E
       (machine pdotdot_** data_**) (S ...) k)
   -----------
   (→* (machine pdotdot data) E
       (machine pdotdot_** data_**) (S ...) k)])

(define-judgment-form esterel-eval
  ;; constructive ->>
  #:mode     (c->> I I O  O      O)
  #:contract (c->> M E M (S ...) k)
  [(→* (machine (· pbar) data) E (machine pbar_* data_*) (S ...) k)
   (side-condition ,(not (equal? `k `⊥)))
   -------
   (c->> (machine pbar data) E (machine pbar_* data_*) (S ...) k)])

(define-metafunction esterel
  free-emitted-signals : pbar  -> (S ...)
  [(free-emitted-signals nothing) ()]
  [(free-emitted-signals pause) ()]
  [(free-emitted-signals (hat pause)) ()]
  [(free-emitted-signals (seq pbar qbar))
   (U (free-emitted-signals pbar) (free-emitted-signals qbar))]
  [(free-emitted-signals (par pbar qbar))
   (U (free-emitted-signals pbar) (free-emitted-signals qbar))]
  [(free-emitted-signals (loop pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (suspend pbar S)) (free-emitted-signals pbar)]
  [(free-emitted-signals (present S pbar qbar))
   (U (free-emitted-signals pbar) (free-emitted-signals qbar))]
  [(free-emitted-signals (trap pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (exit _)) ()]
  [(free-emitted-signals (emit S)) (S)]
  [(free-emitted-signals (var v := call pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (shared s := call pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (signal S pbar)) (without_s (free-emitted-signals pbar) S)]
  [(free-emitted-signals (:= v call)) ()]
  [(free-emitted-signals (<= s call)) ()])

(define-metafunction esterel
  free-signal-vars : pbar -> (S ...)
  [(free-signal-vars nothing) ()]
  [(free-signal-vars pause) ()]
  [(free-signal-vars (hat pause)) ()]
  [(free-signal-vars (seq pbar qbar))
   (U (free-signal-vars pbar) (free-signal-vars qbar))]
  [(free-signal-vars (par pbar qbar))
   (U (free-signal-vars pbar) (free-signal-vars qbar))]
  [(free-signal-vars (loop pbar)) (free-signal-vars pbar)]
  [(free-signal-vars (suspend pbar S)) (U (S) (free-signal-vars pbar))]
  [(free-signal-vars (present S pbar qbar))
   (U (S)
      (U (free-signal-vars pbar) (free-signal-vars qbar)))]
  [(free-signal-vars (trap pbar)) (free-signal-vars pbar)]
  [(free-signal-vars (exit _)) ()]
  [(free-signal-vars (emit S)) (S)]
  [(free-signal-vars (var v := call pbar)) (free-signal-vars pbar)]
  [(free-signal-vars (shared s := call pbar)) (free-signal-vars pbar)]
  [(free-signal-vars (signal S pbar)) (without_s (free-signal-vars pbar) S)]
  [(free-signal-vars (:= v call)) ()]
  [(free-signal-vars (<= s call)) ()])

(define-metafunction esterel-eval
  deselect : pdotdot -> p
  [(deselect p) p]
  [(deselect (· pbar)) (deselect pbar)]
  [(deselect (hat pause)) pause]
  [(deselect (present S pdotdot qdotdot))
   (present S (deselect pdotdot) (deselect qdotdot))]
  [(deselect (suspend S pdotdot)) (suspend S (deselect pdotdot))]
  [(deselect (seq pdotdot qdotdot))
   (seq (deselect pdotdot) (deselect qdotdot))]
  [(deselect (suspend pdotdot S)) (suspend (deselect pdotdot) S)]
  [(deselect (loop pdotdot)) (loop (deselect pdotdot))]
  [(deselect (loop lstat pdotdot)) (loop (deselect pdotdot))]
  [(deselect (par pdotdot qdotdot))
   (par (deselect pdotdot) (deselect qdotdot))]
  [(deselect (par pdotdot any_1 qdotdot any_2))
   (par (deselect pdotdot) (deselect qdotdot))]
  [(deselect (trap pdotdot)) (trap (deselect pdotdot))]
  [(deselect (var v := call pdotdot))
   (var v := call (deselect pdotdot))]
  [(deselect (shared s := call pdotdot))
   (shared s := call (deselect pdotdot))]
  [(deselect (signal S pdotdot))
   (signal S (deselect pdotdot))]
  [(deselect (signal S sstat pdotdot))
   (signal S (deselect pdotdot))]
  [(deselect (if v pdotdot qdotdot))
   (if v (deselect pdotdot) (deselect qdotdot))])


;                                   
;                                   
;                                   
;                                   
;      ;;;;;                        
;     ;;   ;;                       
;    ;;                             
;    ;          ;;;;;      ;  ;;;   
;   ;;          ;   ;;     ;;;  ;;  
;   ;;               ;;    ;;   ;;  
;   ;;               ;;    ;    ;;  
;   ;;           ;;;;;;    ;    ;;  
;   ;;          ;;   ;;    ;    ;;  
;    ;         ;;    ;;    ;    ;;  
;    ;;        ;;    ;;    ;    ;;  
;     ;;   ;;   ;;  ;;;    ;    ;;  
;      ;;;;;    ;;;;  ;    ;    ;;  
;                                   
;                                   
;                                   
;                                   
;                                   


(define-metafunction esterel-eval
  #|
  ↓ : k or (k ...) -> k or (k ...)
  |#
 [(↓ zero) zero]
 [(↓ two) zero]
 [(↓ one) one]
 [(↓ nat) (nat- nat one)]
 [(↓ (k ...)) ((↓ k) ...)])

(define-metafunction esterel-eval
  Can : pdotdot E -> (E K V)

  [(Can (· pbar) E) (Can pbar E)]

  [(Can (present S pbardot q) E) (Can pbardot E)]

  [(Can (present S p qbardot) E) (Can qbardot E)]

  [(Can (suspend pbardot S) E) (Can pbardot E)]

  [(Can (if v pbardot q) E) (Can pbardot E)]

  [(Can (if v p qbardot) E) (Can qbardot E)]

  [(Can (seq pbardot q) E)
   (Can pbardot E)
   (side-condition `(∉ zero (Can_K pbardot E)))]

  [(Can (seq pbardot q) E)
   ((U (Can_S pbardot E) (Can_S q E))
    (U (without (Can_K pbardot E) (zero))
       (Can_K q E))
    (U (Can_V pbardot E)
       (Can_V q E)))
   (side-condition `(∈ zero (Can_K pbardot E)))]

  [(Can (seq p qbardot) E)
   (Can qbardot E)]

  [(Can (par pbardot ⊥ qbardot ⊥) E)
   ((U (Can_S pbardot E)
       (Can_S qbardot E))
    (meta-max (Can_K pbardot E)
              (Can_K qbardot E))
    (U (Can_V pbardot E)
       (Can_V qbardot E)))]

  ;; TODO should this be qbar? (page 112)
  ;; FIXING, listed as q, fails if not qbar
  [(Can (par pbardot ⊥ qbar k) E)
   ((Can_S pbardot E)
    (meta-max (Can_K pbardot E) (k))
    (Can_V pbardot E))]

  ;; FIXING, listed as p, fails if not pbar
  [(Can (par pbar k qbardot ⊥) E)
   ((Can_S qbardot E)
    (meta-max (Can_K qbardot E) (k))
    (Can_V qbardot E))]

  ;; FIXING, listed as p/q, fails if not pbar/qbar
  [(Can (par pbar k qbar l) E)
   (() ((meta-max k l)) ())]

  [(Can (loop go pbardot) E)
   ((U (Can_S pbardot E) (Can_S p E))
    (U (without (Can_K pbardot E) (zero))
       (Can_K p E))
    (U (Can_V pbardot E)
       (Can_V p E)))
   (where p (deselect pbardot))
   (side-condition `(∈ zero (Can_K pbardot E)))]

  [(Can (loop lstat pbardot) E)
   (Can pbardot E)]

  [(Can (signal S sstat pbardot) E)
   (without (Can pbardot (* E (S sstat))) S)]

  [(Can (trap pbardot) E)
   ((Can_S pbardot E) (↓ (Can_K pbardot E)) (Can_V pbardot E))]

  [(Can (var v := call pbardot) E)
   (Can pbardot E)]

  [(Can (shared s := call pbardot) E)
   (without_s (Can pbardot E) s)]

  [(Can (:= v call) E)
   (() (zero) ())]

  [(Can (<= s call) E)
   (() (zero) (s))]

  [(Can (var v := call pbar) E) (Can pbar E)]
  [(Can (if v p q) E) (U (Can p E) (Can q E))]

  [(Can (if v phat q) E) (Can phat E)]

  [(Can (if v p qhat) E) (Can qhat E)]

  [(Can (shared s := call pbar) E) (without_s (Can pbar E) s)]

  ;; from ch 3 (starts at 77)
  [(Can nothing E) (() (zero) ())]

  [(Can pause E) (() (one) ())]

  [(Can (exit k) E) (() (k) ())]

  [(Can (emit S) E) (((S one)) (zero) ())]

  [(Can (present S p q) E)
   (Can p E)
   (side-condition `(∈ (S one) E))]

  [(Can (present S p q) E)
   (Can q E)
   (side-condition `(∈ (S zero) E))]

  [(Can (present S p q) E)
   (U (Can p E) (Can q E))
   (side-condition `(∈ (S ⊥) E))]

  [(Can (suspend p S) E)
   (Can p E)]

  [(Can (seq p q) E)
   (Can p E)
   (side-condition `(∉ zero (Can_K p E)))]

  [(Can (seq p q) E)
   ( (U (Can_S p E) (Can_S q E))
     (U (without (Can_K p E) (zero))
        (Can_K q E))
     (U (Can_V p E) (Can_V q E)) )]

  [(Can (loop p) E)
   (Can p E)]

  [(Can (par p q) E)
   ( (U (Can_S p E) (Can_S q E))
     (meta-max (Can_K p E) (Can_K q E))
     (U (Can_V p E) (Can_V q E)) )]

  [(Can (trap p) E)
   ( (Can_S p E)
     (↓ (Can_K p E))
     (Can_V p E) )]

  [(Can (signal S p) E)
   (without (Can p (* E (S zero))) S)
   (side-condition `(∉ (S one) (Can_S p (* E (S ⊥)))))]

  [(Can (signal S p) E)
   (without (Can p (* E (S ⊥))) S)]

  [(Can (hat pause) E)
   ( () (zero) () )]

  [(Can (present S phat q) E)
   (Can phat E)]

  [(Can (present S p qhat) E)
   (Can qhat E)]

  [(Can (suspend phat S) E)
   ( () (one) () )
   (side-condition `(∈ (S one) E))]

  [(Can (suspend phat S) E)
   (Can phat E)
   (side-condition `(∈ (S zero) E))]

  [(Can (suspend phat S) E)
   ( E_o (U ((Succ zero)) (k ...)) (v ...) )
   (where (E_o (k ...) (v ...)) (Can phat E))
   (side-condition `(∈ (S ⊥) E))]

  [(Can (seq p qhat) E)
   (Can qhat E)]

  [(Can (seq phat q) E)
   (Can phat E)
   (side-condition `(∉ zero (Can_K phat E)))]

  [(Can (seq phat q) E)
   ( (U (Can_S phat E) (Can_S q E))
     (U (without (Can_K phat E) (zero))
        (Can_K q E))
     (U (Can_V phat E) (Can_V q E)))]

  [(Can (loop phat) E)
   (Can phat E)
   (side-condition `(∉ zero (Can_K phat E)))]

  [(Can (loop phat) E)
   ( (U (Can_S phat E) (Can_S p E))
     (U (without (Can_K phat E) (zero)) (Can_K p E))
     (U (Can_V phat E) (Can_V p E)) )
   (where p (deselect phat))]

  [(Can (par phat q) E)
   (Can phat E)]

  [(Can (par p qhat) E)
   (Can qhat E)]

  [(Can (par phat qhat) E)
   ( (U (Can_S phat E) (Can_S qhat E))
     (meta-max (Can_K phat E) (Can_K qhat E))
     (U (Can_V phat E) (Can_V qhat E)) )]

  [(Can (trap phat) E)
   ( (Can_S phat E)
     (↓ (Can_K phat E))
     (Can_V phat E) )]

  [(Can (signal S phat) E)
   (without (Can phat (* E (S zero))) S)
   (side-condition `(∉ (S one) (Can_S phat (* E (S ⊥)))))]

  [(Can (signal S phat) E)
   (without (Can phat (* E (S ⊥))) S)])

(define-metafunction esterel-eval
  U : (any ...) ... -> (any ...)
  ;; I suspect this case is wrong...?
  [(U E_1 E_2)
   (U_E E_1 E_2)]
  [(U (E_1 (k_1 ...) (v_1 ...))
      (E_2 (k_2 ...) (v_2 ...)))
   ( (U E_1 E_2)
     (U (k_1 ...) (k_2 ...))
     (U (v_1 ...) (v_2 ...)))]
  [(U () (any ...))
   (any ...)]
  [(U (any any_1 ...) (any_2 ...))
   (U (any_1 ...) (insert any (any_2 ...)))]
  [(U (any ...)) (any ...)]
  [(U (any_1 ...) (any_2 ...) (any_r ...) ...)
   (U (U (any_1 ...) (any_2 ...)) (any_r ...) ...)])

(define-metafunction esterel-eval
  ;; special case union for signal events
  U_E : E E -> E
  [(U_E () E) E]
  [(U_E ((S sstat) (S_1 sstat_1) ...) E)
   (U_E ((S_1 sstat_1) ...) (insert_E (S sstat) E))])

(define-metafunction esterel-eval
  insert_E : (S sstat) E -> E
  ;; if it was bot you Can replace it
  [(insert_E (S sstat) ((S_1 sstat_1) ... (S ⊥) (S_2 sstat_2) ...))
   ((S_1 sstat_1) ... (S sstat) (S_2 sstat_2) ...)]
  ;; if its present with the same sstat ignore
  [(insert_E (S sstat) ((S_1 sstat_1) ... (S sstat) (S_2 sstat_2) ...))
   ((S_1 sstat_1) ... (S sstat) (S_2 sstat_2) ...)]
  ;; if it is not present you Can add it
  [(insert_E (S sstat) ((S_1 sstat_1) ...))
   ((S sstat) (S_1 sstat_1) ...)
   (side-condition (not (member `S `(S_1 ...))))]
  ;; else idk what the behavior is
  ;; i think this means causally unsound program
  ;; so... error?
  ;; should never happen with Can?
  )

(define-metafunction esterel-eval
  insert : any (any ...) -> (any ...)
  [(insert any (any_1 ... any any_2 ...))
   (any_1 ... any any_2 ...)]
  [(insert any (any_1 ...))
   (any any_1 ...)])

(define-metafunction esterel-eval
  #|
  without :
  ((S sstat) ...) or (k ...) or (s ...) or (((S sstat) ...) (k ...) (s ...))
  S or (k ...) or s
  ->
  (k ...) or ((S sstat) ...) or (s ...) or (((S sstat) ...) (k ...) (s ...))
  |#

  [(without ((S_1 sstat_1) ... (S sstat) (S_2 sstat_2) ...) S)
   (without ((S_1 sstat_1) ... (S_2 sstat_2) ...) S)]
  [(without ((S_1 sstat_1) ... (S_2 sstat_2) ...) S)
   ((S_1 sstat_1) ... (S_2 sstat_2) ...)]

  #|
  [(without (s_1 ... s s_2 ...) s)
   (s_1 ... s_2 ...)]
  |#

  [(without (k ...) ()) (k ...)]

  [(without (k_1 ...) (k k_2 ...))
   (without (without (k_1 ...) k) (k_2 ...))]

  [(without (k_1 ... k k_2 ...) k)
   (without (k_1 ... k_2 ...) k)]

  [(without (k_1 ... k_2 ...) k)
   (k_1 ... k_2 ...)]

  [(without (E (k ...) (s ...)) S)
   ((without E S) (k ...) (s ...))]

  [(without (E (k ...) (s_1 ...)) s)
   (E (k ...) (without (s_1 ...) s))])

(define-metafunction esterel-eval
  #|
  without_s
  : (E (k ...) (s ...)) or (s ...)
  s
  -> (E (k ...) (s ...)) or (s ...)
  |#
  [(without_s (E (k ...) (s_1 ...)) s)
   (E (k ...) (without_s (s_1 ...) s))]
  [(without_s (s_1 ... s s_2 ...) s)
   (s_1 ... s_2 ...)]
  [(without_s (s_1 ...) s)
   (s_1 ...)])

(define-metafunction esterel-eval
  ∉ : any (any ...) -> boolean
  [(∉ any_1 (any_2 ...))
   ,(not `(∈ any_1 (any_2 ...)))])
(define-metafunction esterel-eval
  ∈
  : any (any ...) -> boolean
  ;; special case, page 67
  [(∈ (S ⊥) ((S_1 sstat) ...))
   #t
   (where #t (∉ S (S_1 ...)))]
  [(∈ any_1 (any_2 ... any_1 any_3 ...))
   #t]
  [(∈ any_1 (any_2 ...))
   #f])
(define-metafunction esterel-eval
  #|
  meta-max
  : (k ...) or k
  (k ...) or k
  ->
  (k) or k
  |#

  [(meta-max (k_11 k_1 ...) (k_2 ...))
   (U (meta-max k_11 (k_2 ...))
      (meta-max (k_1 ...) (k_2 ...)))]
  [(meta-max (k_1 ...) (k_2 ...)) ()]
  [(meta-max k_1 (k_2 ...))
   (U ((meta-max k_1 k_2)) ...)]
  [(meta-max k_1 k_2)
   k_2
   (where #t (nat<= k_1 k_2))]
  [(meta-max k_1 k_2)
   k_1]
  [(meta-max k_1 k_2 k_3 ...)
   (meta-max (meta-max k_1 k_2) k_3 ...)])

(define-metafunction esterel-eval
  * : E (S sstat) -> E
  [(* ((S_1 sstat_1) ...
       (S _)
       (S_2 sstat_2) ...)
      (S sstat))
   ((S_1 sstat_1) ...
    (S sstat)
    (S_2 sstat_2) ...)]
  [(* ((S_E sstat_E) ...)
      (S sstat))
   ((S sstat) (S_E sstat_E) ...)])

(define-metafunction esterel-eval
  Can_S : pdotdot E -> ((S sstat) ...)
  [(Can_S pdotdot E)
   ((S sstat) ...)
   (where (((S sstat) ...) _ _) (Can pdotdot E))])

(define-metafunction esterel-eval
  Can_K : pdotdot E -> (k ...)
  [(Can_K pdotdot E)
   (k ...)
   (where (_ (k ...) _) (Can pdotdot E))])

(define-metafunction esterel-eval
  Can_V : pdotdot E -> (s ...)
  [(Can_V pbardot E)
   (s ...)
   (where (_ _ (s ...)) (Can pbardot E))]
  [(Can_V pause E) ()]
  [(Can_V (hat pause) E) ()]
  [(Can_V (emit S) E) ()]
  [(Can_V (exit k) E) ()]
  [(Can_V (signal S pbar) E)
   (Can_V pbar  (* E (S ⊥)))
   (side-condition `(∈ (S one) (Can_S pbar (* E (S ⊥)))))]
  [(Can_V (signal S pbar) E)
   (Can_V pbar (* E (S zero)))]
  [(Can_V (present S p q))
   (Can_V p E)
   (side-condition `(∈ (S one) E))]
  [(Can_V (present S p q))
   (Can_V q E)
   (side-condition `(∈ (S zero) E))]
  [(Can_V (present S p q))
   (U (Can_V p E) (Can_V q E))
   (side-condition `(∈ (S ⊥) E))]
  [(Can_V (present S phat q) E)
   (Can_V phat E)]
  [(Can_V (present S p qhat) E)
   (Can_V qhat E)]
  [(Can_V (suspend S p) E)
   (Can_V p E)]
  [(Can_V (suspend S phat) E)
   ()
   (side-condition `(∈ (S one) E))]
  [(Can_V (suspend S phat) E)
   (Can_V phat E)]
  [(Can_V (trap pbar) E)
   (Can_V pbar E)]
  [(Can_V (par p q) E)
   (U (Can_V p E) (Can_V q E))]
  [(Can_V (par phat qhat) E)
   (U (Can_V phat E) (Can_V qhat E))]
  [(Can_V (par phat q))
   (Can_V phar E)]
  [(Can_V (par p qhat) E)
   (Can_V qhat E)]
  [(Can_V (seq pbar q) E)
   (U (Can_V pbar E) (Can_V q E))
   (side-condition `(∈ zero (Can_K pbar E)))]
  [(Can_V (seq pbar q) E)
   (Can_V pbar E)]
  [(Can_V (seq p qhat) E)
   (Can_V qhat E)]
  [(Can_V (loop p) E)
   (Can_V p E)]
  [(Can_V (loop phat) E)
   (U (Can_V phat E) (Can_V (deselect phat) E))
   (side-condition `(∈ zero (Can_K phat E)))]
  [(Can_V pdotdot E)
   V
   (where (_ _ V) (Can pdotdot E))])