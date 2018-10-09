#lang racket
(require redex/reduction-semantics racket/random)
(provide (all-defined-out))
(module+ test
  (provide (all-defined-out))
  (require rackunit (prefix-in rackunit: rackunit))
  (define-syntax-rule (test-case str tests ...)
    (rackunit:test-case
     str
     ;(printf "starting \"~a\" tests\n" str)
     tests ...
     #;
     (printf "finishing \"~a\" tests\n" str))))

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

(module+ test
  (test-equal
   `(nat= two one)
   #f)
  (test-equal
   `(nat= one two)
   #f))

(define-metafunction nats
  [(natnorm zero) zero]
  [(natnorm one) (Succ zero)]
  [(natnorm two) (Succ (natnorm one))]
  [(natnorm three) (Succ (natnorm two))]
  [(natnorm (Succ nat)) (Succ (natnorm nat))])

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
  (sstat ⊥ one zero)
   ;#:binding-forms
   ;(signal S p #:refers-to S)
   ;(signal S phat #:refers-to S)
   ;(signal S sstat pdot #:refers-to S)
   )
(module+ test
  (test-case "grammar"
    (check-true
     (redex-match? esterel (exit k) `(exit zero)))
    (check-true
     (redex-match? esterel (exit k) `(exit one)))
    (check-true
     (redex-match? esterel (exit k) `(exit two)))
    (check-true
     (redex-match? esterel (exit k) `(exit (Succ (Succ zero)))))
    (check-true
     (redex-match? esterel (exit k) `(exit three)))))
(define-extended-language esterel-eval esterel
  ;(m P E Ss k data)
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
(module+ test
  (test-case "eval grammar"
    (check-true
     (redex-match? esterel-eval l `one))
    (check-true
     (redex-match? esterel-eval sstat `one))
    (check-true
     (redex-match? esterel-eval E `((S one))))
    (check-true
     (redex-match? esterel-eval (E K V) `(((S one)) (zero) ())))))

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


   ;; TODO allow for other comb functions
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

(module+ test
  (default-language esterel-eval)
  (define (do t [E `()] [data `()])
    (judgment-holds (non-det-> ,t ,data ,E
                               pdotdot data_* e k)
                    (pdotdot e k data_*)))
  (define (do/det t [E `()] [data `()])
    (judgment-holds (det-> ,t ,data ,E
                           pdotdot data_* e k)
                    (pdotdot e k data_*)))
  (test-case "1"
    (parameterize ([current-traced-metafunctions '(→)])
      (test-equal (do `(· nothing))
                  `((nothing ⊥ zero ())))))
  (test-case "2"
    (test-equal (do `(· pause))
                `(((hat pause) ⊥ one ()))))
  (test-case "3"
    (test-equal (do `(· (hat pause)))
                `((pause ⊥ zero ()))))
  (test-case "4"
    (test-equal
     (do `(· (seq pause pause)))
     `(((seq (· pause) pause) ⊥ ⊥ ())))
    (test-equal
     (do `(· (seq (hat pause) pause)))
     `(((seq (· (hat pause)) pause) ⊥ ⊥ ()))))
  (test-case "5"
    (test-equal
     (do `(seq (· (hat pause)) pause))
     `(( (seq pause (· pause)) ⊥ ⊥ ())))
    (test-equal
     (do `(seq (· pause) pause))
     `(( (seq (hat pause) pause) ⊥ one ()))))
  (test-case "6"
    (test-equal
     (do `(seq (· (hat pause)) pause))
     `(( (seq pause (· pause)) ⊥ ⊥ () )))

    (test-equal
     (do `(seq (· nothing) pause))
     `(( (seq nothing (· pause)) ⊥ ⊥ () ))))

  (test-case "7"
    (test-not-false "pbar"
     (redex-match esterel pbar `(seq pause (hat pause))))
    (test-equal
     (do `(· (seq pause (hat pause))))
     `(( (seq pause (· (hat pause))) ⊥ ⊥ ())))
    (test-equal
     (do `(· (seq pause (seq pause (hat pause)))))
     `(( (seq pause (· (seq pause (hat pause)))) ⊥ ⊥ () ))))

  (test-case "8"
    (check-not-false
     "8"
     (redex-match esterel pbardot `(seq pause (seq (· (hat pause)) pause))))
    (check-not-false
     "8"
     (redex-match esterel pbardot `(seq (· (hat pause)) pause)))
    (check-not-false
     "8"
     (redex-match esterel (seq p qbardot) `(seq pause (seq (· (hat pause)) pause))))
    (test-equal
     (do ` (seq pause (· (hat pause))))
     `(( (seq pause pause) ⊥ zero ())))
    (test-equal
     (do `(seq pause (seq pause (· (hat pause)))))
     `(( (seq pause  (seq pause pause)) ⊥ zero () )))
    (test-equal
     (do `(seq pause (seq pause (· pause))) )
     `(( (seq pause (seq pause (hat pause))) ⊥ one () )))
    (test-equal
     (do `(seq pause (seq (· (hat pause)) pause)))
     `(( (seq pause (seq pause (· pause))) ⊥ ⊥ () ))))

  (test-case "9"
    (test-equal
     (do `(· (par pause pause)))
     `(( (par (· pause) ⊥ (· pause) ⊥) ⊥ ⊥ ()))))

  (test-case "10"
    (test-equal
     (do `(· (par (hat pause) (hat pause))))
     `(( (par (· (hat pause)) ⊥ (· (hat pause)) ⊥) ⊥ ⊥ ()))))

  (test-case "11"
    (test-equal
     (do `(· (par (hat pause)  pause)))
     `(( (par (· (hat pause)) ⊥ pause zero) ⊥ ⊥ ()))))

  (test-case "12"
    (test-equal
     (do `(· (par  pause (hat pause))))
     `(( (par pause zero (· (hat pause)) ⊥) ⊥ ⊥ ()))))

  (test-case "13"
    (test-equal
     (do `(par pause zero (hat pause) one))
     `(( (par pause (hat pause)) ⊥ one ()))))
  (test-case "14"
    (test-equal
     (do `(par (· (seq pause pause)) ⊥ pause zero))
     `(( (par (seq (· pause) pause) ⊥ pause zero) ⊥ ⊥ ()))))
  (test-case "15"
    (test-equal
     (do `(par pause zero (· (seq pause pause)) ⊥))
     `(( (par pause zero (seq (· pause) pause) ⊥) ⊥ ⊥ ()))))
  (test-case "14/15"
    (test-equal
     (do `(par (· (seq pause pause)) ⊥ (· (seq pause pause)) ⊥))
     `(( (par (seq (· pause) pause) ⊥ (· (seq pause pause)) ⊥) ⊥ ⊥ ())
       ( (par (· (seq pause pause)) ⊥ (seq (· pause) pause) ⊥) ⊥ ⊥ ())))
    (test-equal
     (do/det `(par (· (seq pause pause)) ⊥ (· (seq pause pause)) ⊥))
     `(( (par (seq (· pause) pause) ⊥ (· (seq pause pause)) ⊥) ⊥ ⊥ ()) ))
    (test-equal
     (do/det `(· (par (signal pQ (emit x)) (emit C))))
     `((  (par (· (signal pQ (emit x))) ⊥ (· (emit C)) ⊥)
          ⊥ ⊥ ()) ))
    (test-equal
     (do/det `(par (· (signal pQ (emit x))) ⊥ (· (emit C)) ⊥))
     `((  (par  (signal pQ ⊥ (·(emit x))) ⊥ (· (emit C)) ⊥)
          ⊥ ⊥ ()) ))
    (test-equal
     (do/det `(par (signal pQ (emit x)) zero (· (emit C)) ⊥))
     `((  (par  (signal pQ (emit x)) zero (emit C) zero)
          C ⊥ ()) )))
  (test-case "16"
    (test-equal
     (do `(· (loop (seq pause nothing))))
     `(( (loop stop (· (seq pause nothing))) ⊥ ⊥ ()))))
  (test-case "17"
    (test-equal
     (do `(· (loop (seq (hat pause) nothing))))
     `(( (loop go (· (seq (hat pause) nothing))) ⊥ ⊥ ())))
    (test-equal
     (do `(· (loop (hat pause) )))
     `(( (loop go (· (hat pause))) ⊥ ⊥ ()))))
  (test-case "18"
    (test-equal
     (do `(loop go (seq pause (· nothing))))
     `(( (loop stop (· (seq pause nothing))) ⊥ ⊥ ()))))
  (test-case "19"
    (test-equal
     (do `(loop go (seq (· pause) nothing)))
     `(( (loop (seq (hat pause) nothing)) ⊥ one ())))
    (test-equal
     (do `(loop stop (seq (· pause) nothing)))
     `(( (loop (seq (hat pause) nothing)) ⊥ one ()))))
  (test-case "20"
    (test-equal
     (do `(loop go (seq (· (hat pause)) nothing)))
     `(( (loop go (seq pause (· nothing))) ⊥ ⊥ ())))
    (test-equal
     (do `(loop stop (seq (· (hat pause)) nothing)))
     `(( (loop stop (seq pause (· nothing))) ⊥ ⊥ ()))))
  (test-case "21"
    (test-equal
     (do `(· (trap (par pause pause))))
     `(( (trap (· (par pause pause))) ⊥ ⊥ ()))))
  (test-case  "22"
    (test-equal
     (do `(trap (seq (· nothing) pause)))
     `(( (trap (seq  nothing (· pause))) ⊥ ⊥ ()))))
  (test-case "23"
    (test-equal
     (do `(trap (seq (· (exit two)) pause)))
     `(( (trap (seq (exit two) pause)) ⊥ zero ()))))
  (test-case "24"
    (test-equal
     (do `(trap (seq pause (· (hat pause)))))
     `(( (trap (seq pause pause)) ⊥ zero ()))))
  (test-case "25"
    (test-equal
     (do `(trap (seq pause (· pause))))
     `(( (trap (seq pause (hat pause))) ⊥ one ()))))
  (test-case "26"
    (test-equal
     (do `(trap (· (exit three))))
     `(( (trap (exit three)) ⊥ (natnorm two) () ))))
  (test-case "27"
    (test-equal
     (do `(· (exit three)))
     `(( (exit three) ⊥ three ()))))
  (test-case "28"
    (test-equal
     (do `(· (signal S (emit S))))
     `(( (signal S ⊥ (· (emit S))) ⊥ ⊥ ()))))
  (test-case "29"
    (test-true "29-pdotdot"
     (redex-match? esterel-eval pdotdot `(seq (· (emit S«156»)) pause)))
    (test-true "29-E"
               (redex-match? esterel-eval E `((S«156» ⊥))))
    (test-equal
     (do `(seq (· (emit S)) pause))
     `(( (seq (emit S) (· pause)) S ⊥ ())))
    (test-equal
     (do `(signal S ⊥ (seq (· (emit S)) pause)))
     `(( (signal S one (seq (emit S) (· pause))) ⊥ ⊥ ()))))
  (test-case "30"
    (test-equal
     `(Can_S (signal S zero (seq (emit S) (seq pause (· pause)))) ((S ⊥)))
     `())
    (test-equal
     (do `(signal S ⊥ (seq (emit S) (seq pause (· pause)))))
     `(
       ((signal
          S
          zero
          (seq (emit S) (seq pause (· pause))))
         ⊥
         ⊥
         ())
       )))
  (test-case "31"
    (test-equal
     (do `(signal S zero (seq (· (emit R)) pause)))
     `(( (signal S zero (seq (emit R) (· pause)))
         R
         ⊥
         ())))
    (test-equal
     `(Can_S (seq (· (hat pause)) (emit S)) ())
     `((S one)))
    (test-equal
     (do `(signal S ⊥ (seq (· (hat pause)) (emit S))))
     `(( (signal S ⊥ (seq pause (· (emit S))))
         ⊥
         ⊥
         ()))))

  (test-case "32"
    (test-equal
     (do `(signal S zero (· (emit R))))
     `(( (signal S (emit R))
         R
         zero
         ())))
    (test-equal
     (do `(· pause))
     `(( (hat pause) ⊥ one ())))
    (test-equal
     (do `(signal S zero (· pause)))
     `(( (signal S (hat pause))
         ⊥
         one
         ()))))

  (test-case "33"
    (test-equal
     (do `(signal S one (· (emit S)) ))
     `(( (signal S (emit S))
         ⊥
         zero
         ()))))

  (test-case "34"
    (test-equal
     (do `(· (emit S)))
     `(( (emit S) S zero ()))))

  (test-case "35"
    (test-equal
     (do `(· (suspend (hat pause) S))
         `((S (Succ zero))))
     `(( (suspend (hat pause) S) ⊥ (Succ zero) () ))))

  (test-case "36"
    (test-equal
     (do `(· (suspend (hat pause) S))
         `((S zero)))
     `(( (suspend (· (hat pause)) S) ⊥ ⊥ () ))))

  (test-case "37"
    (test-equal
     (do `(· (suspend pause S)))
     `(( (suspend (· pause) S) ⊥ ⊥ () ))))

  (test-case "38"
    (test-equal
     (do `(suspend (· pause) S))
     `(( (suspend (hat pause) S) ⊥ one () ))))

  (test-case "39"
    (test-equal
     (do `(· (present t pause pause)) `((t one)))
     `(( (present t (· pause) pause) ⊥ ⊥ ()))))
  (test-case "40"
    (test-equal
     (do `(· (present t pause pause)) `((t zero)))
     `(( (present t pause (· pause)) ⊥ ⊥ ()))))

  (test-case "41"
    (test-equal
     (do `(· (present t (hat pause) pause)) `((t zero)))
     `(( (present t (· (hat pause)) pause) ⊥ ⊥ ()))))
  (test-case "42"
    (test-equal
     (do `(· (present t  pause (hat pause))) `((t one)))
     `(( (present t pause (· (hat pause))) ⊥ ⊥ ()))))
  (test-case "43"
    (test-equal
     (do `(present t (· (hat pause)) pause))
     `(( (present t pause pause) ⊥ zero ()))))
  (test-case "44"
    (test-equal
     (do `(present t pause (· (hat pause))))
     `(( (present t pause pause) ⊥ zero ()))))

  (define-syntax-rule (do* p data)
    (judgment-holds (non-det-> p data ()
                               pdotdot_* data_* e k)
                    (pdotdot_* data_* e k)))
  (test-case "45"
    (test-equal
     (do* (· (shared s := 5 nothing)) ())
     `(( (shared s := 5 (· nothing)) ((dshared s 5 old))
         ⊥ ⊥ )))
    (test-equal
     (do* (· (shared s := 5 nothing)) ((dshared s 5 old)))
     `(( (shared s := 5 (· nothing)) ((dshared s 5 old))
         ⊥ ⊥ ))))
  (test-case "46"
    (test-equal
     (do* (· (shared s := 5 (hat pause))) ((dshared s 12 ready)))
     `(( (shared s := 5 (· (hat pause))) ((dshared s 12 old))
         ⊥ ⊥
         ))))
  (test-case "47"
    (test-equal
     (do* (shared s := 1 (· nothing)) ((dshared s 0 old)))
     `(( (shared s := 1 (· nothing)) ((dshared s 0 ready))
         ⊥ ⊥ ))))
  (test-case "48"
    (test-equal
     (do* (shared s := 1 (· nothing)) ((dshared s 0 ready)))
     `(( (shared s := 1 nothing) ((dshared s 0 ready))
         ⊥ zero ))))
  (test-case "49"
    (test-equal
     (do* (shared s := 1
                  (· (<= s (+ 1 y))))
          ((dshared s 1 old)
           (dshared y 1 ready)))
     `((
        (shared s := 1 (<= s (+ 1 y)))
        ((dshared s 2 new)
         (dshared y 1 ready))
        ⊥
        zero
        ))))
  (test-case "50"
    (test-equal
     (do* (shared s := 1
                  (· (<= s (+ 1 y))))
          ((dshared s 1 new )
           (dshared y 1 ready)))
     `((
        (shared s := 1 (<= s (+ 1 y)))
        ((dshared s 3 new)
         (dshared y 1 ready))
        ⊥
        zero
        ))))

  (test-case "51"
    (test-equal `(shared-of (+ 2 1) ()) `())
    (check-true
     (redex-match? esterel-eval (· (var v := call p)) `(· (var v := (+ 2 1) nothing))))
    (test-equal
     (do*
      (· (var v := (+ 2 1) nothing))
      ())
     `((
        (var v := (+ 2 1) (· nothing))
        ((dvar v 3))
        ⊥ ⊥
        ))))

  (test-case "52"
    (test-equal
     (do*
      (· (var v := 3 (hat pause)))
      ((dvar v 2)))
     `((
        (var v := 3 (· (hat pause)))
        ((dvar v 2))
        ⊥
        ⊥
        ))))
  (test-case "53"
    (test-equal
     (do*
      (var v := 3 (· (hat pause)))
      ((dvar v 2)))
     `((
        (var v := 3 pause)
        ((dvar v 2))
        ⊥
        zero)))
    (test-equal
     (do*
      (var v := 3 (· (:= v 4)))
      ((dvar v 2)))
     `((
        (var v := 3 (:= v 4))
        ((dvar v 4))
        ⊥
        zero))))
  (test-case "54"
    (test-equal
     (do*
      (· (if v nothing pause))
      ((dvar v 1)))
     `((
        (if v (· nothing) pause)
        ((dvar v 1))
        ⊥ ⊥))))
  (test-case "55"
    (test-equal
     (do*
      (· (if v nothing pause))
      ((dvar v 0)))
     `((
        (if v nothing (· pause))
        ((dvar v 0))
        ⊥ ⊥))))
  (test-case "56"
    (test-equal
     (do*
      (· (if v (hat pause) nothing))
      ((dvar v 12)))
     `(( (if v (· (hat pause)) nothing)
         ((dvar v 12))
         ⊥ ⊥))))
  (test-case "57"
    (test-equal
     (do*
      (· (if v nothing (hat pause)))
      ((dvar v 12)))
     `((
        (if v nothing (· (hat pause)))
        ((dvar v 12))
        ⊥ ⊥
        ))))
  (test-case "58"
    (test-equal
     (do*
      (if v (· pause) nothing)
      ((dvar v 12)))
     `((
        (if v (hat pause) nothing)
        ((dvar v 12))
        ⊥ (Succ zero)
        ))))
  (test-case "59"
    (test-equal
     (do*
      (if v nothing (· pause))
      ((dvar v 12)))
     `((
        (if v nothing (hat pause))
        ((dvar v 12))
        ⊥ (Succ zero)
        ))))
  (test-case "60"
      (test-equal
     (do*
      (· (:= v 4))
      ((dvar v 2)))
     `((
        (:= v 4)
        ((dvar v 4))
        ⊥
        zero))))



  (test-case "bugs"
    (test-equal
     (do `(loop go (present t (· (hat pause)) nothing)))
     `(( (loop stop (· (present t pause nothing))) ⊥ ⊥ () )))
    (test-equal
     (do `(trap (· (signal T (hat pause)))))
     `(( (trap (signal T ⊥ (· (hat pause))))
         ⊥
         ⊥
         ())))
    (test-equal
     (do `(· (signal T (hat pause))))
     `(( (signal T ⊥ (· (hat pause)))
         ⊥
         ⊥
         ()  )))
    (test-equal (do `(· (par nothing nothing)))
                `(( (par (· nothing) ⊥ (· nothing) ⊥) ⊥ ⊥ () )))

    (test-equal (do `(par (· nothing) ⊥ nothing zero))
                `(( (par nothing zero nothing zero) ⊥ ⊥ () )))

    (test-equal (do `(par nothing zero nothing zero))
                `(( (par nothing nothing) ⊥ zero () )))

    (test-equal
     (do* (· (seq (shared c := 1 nothing) (suspend pause plU)))
          ((dshared c 1 old)))
     `((
        (seq (·(shared c := 1 nothing)) (suspend pause plU))
        ((dshared c 1 old))
        ⊥
        ⊥
        )))
    (test-equal
     (do*  (seq (· (shared c := 1 nothing)) (suspend pause plU))
           ((dshared c 1 old)))
     `((
        (seq (shared c := 1 (· nothing)) (suspend pause plU))
        ((dshared c 1 old))
        ⊥
        ⊥
        )))))


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


(module+ test
  (provide (all-defined-out))
  (define-extended-language esterel-check esterel-eval
    (p-check
     nothing
     pause
     (seq p-check p-check)
     (par p-check p-check)
     (trap p-check)
     (exit nat)
     (signal S p-check)
     (suspend p-check S)
     (present S p-check p-check)
     (emit S)
     (shared s := call/check p-check+sset)
     (var v := call/check p-check+vset))

    (p-check+sset
     p-check
     (seq p-check+sset p-check+sset)
     (par p-check+sset p-check+sset)
     (trap p-check+sset)
     (exit nat)
     (signal S p-check+sset)
     (suspend p-check+sset S)
     (present S p-check+sset p-check+sset)
     (var v := call/check p-check+sset+vset)
     (<= s call/check))

    (p-check+vset
     p-check
     (seq p-check+vset p-check+vset)
     (par p-check+vset p-check)
     (trap p-check+vset)
     (exit nat)
     (signal S p-check+vset)
     (suspend p-check+vset S)
     (present S p-check+vset p-check+vset)

     (shared s := call/check p-check+sset+vset)
     (:= v call/check))

    (p-check+sset+vset
     p-check+vset
     p-check+sset)

    (phat-check
     (hat pause)
     ;; loops only present here to force loops to be non-instantanious
     (loop phat-check)
     (suspend phat-check S)
     (seq phat-check p-check)
     (seq p-check phat-check)
     ;; force a phat for the sake of loop safety
     (present S phat-check phat-check)
     (par phat-check phat-check)
     (trap phat-check)
     (signal S phat-check)
     (shared s := call/check phat-check+sset))
    (phat-check+sset
     phat-check
     (loop phat-check+sset)
     (suspend phat-check+sset S)
     (seq phat-check+sset p-check+sset)
     (seq p-check+sset phat-check+sset)
     ;; force a phat for the sake of loop safety
     (present S phat-check+sset phat-check+sset)
     (par phat-check+sset phat-check+sset)
     (trap phat-check+sset)
     (signal S phat-check+sset))
    (pbar-check p-check phat-check)

    (NL ()
        (nat NL))

    (call/check (+ call/check  call/check ) (+ call/check ) (+) v s  natural))

  #;
(judgment-holds
                  (cos:c->> (machine ,(first p) ,(second p))
                            ,(setup-*-env i in)
                            (machine pbar data_*) (S ...) k)
                  (pbar data_* (S ...)))

  (define-judgment-form esterel-eval
  ;; constructive ->>, with testing checks
  #:mode     (cc->> I I O O       O)
  #:contract (cc->> M E M (S ...) k)
  [(where (((machine qbar_r data_r*) (S_r ...) k_r) ...)
          ,(judgment-holds
            (c->> (machine pbar data) E (machine qbar data_*) (S ...) k)
            ((machine qbar data_*) (S ...) k)))
   (where (M_* (S_* ...)) (eval (machine pbar data) E))
   (where (((machine qbar data_*) (S ...) k) any_2 ...)
          (((machine qbar_r data_r*) (S_r ...) k_r) ...))
   (where #t ,(andmap (curry equal? `k)
                      `(k_r ...)))
   (where #t ,(andmap (lambda (M) (alpha-equivalent? esterel-eval `(machine qbar data_*) M))
                      `(M_* (machine qbar_r data_r*) ...)))
   ;(side-condition ,(displayln `(S_* ... S ... (free-emitted-signals pbar))))
   ;(side-condition ,(displayln `((∈ S (free-emitted-signals pbar)) ...)))
   (where (#t ...) ((∈ S_* (free-emitted-signals pbar)) ...
                    (∈ S (free-emitted-signals pbar)) ...))
   (where E_2 (Can_S pbar E))
   ;(side-condition ,(displayln `((S one) ... E_2)))
   ;(side-condition ,(displayln `((∈ (S one) E_2) ...)))
   (where (#t ...) ((∈ (S_* (Succ zero)) E_2) ...
                    (∈ (S (Succ zero)) E_2) ...))
   (where #t
          ,(for*/and ([Sl1 (in-list `((S_* ...) (S_r ...) ...))]
                      [Sl2 (in-list `((S_* ...) (S_r ...) ...))])
             (equal? (list->set Sl1) (list->set Sl2))))
   (bars-match qbar k)
   -------
   (cc->> (machine pbar data) E (machine qbar data_*) (S ...) k)])

  (define-judgment-form esterel-eval
    #:mode (bars-match I I)
    #:contract (bars-match pbar k)
    [-------
     (bars-match p zero)]
    [-------
     (bars-match phat (Succ zero))])

  (define-metafunction esterel-eval
    random-E : (S ...) -> E
    [(random-E (S ...))
     ((random-E_S S) ...)])

  (define-metafunction esterel-eval
    random-E_S : S -> (S k)
    [(random-E_S S)
     (S ,(if (> (random) 0.5) `zero `(Succ zero)))])

  (define-judgment-form esterel-eval
    #:mode (->*/final I I O O O)
    [(→* (machine pdotdot data) E (machine qdotdot data_*) (S ...) k)
     (where #f ,(judgment-holds (→ qdotdot data E _ _ _ _)))
     -------------
     (->*/final (machine pdotdot data) E (machine qdotdot data_*) (S ...) k)])

  (test-case "eval bugs"
    (test-judgment-holds
     (c->>
      (machine (par (signal f (emit S)) (shared v := 1 pause)) ()) ()
      (machine (par (signal S_f (emit S_S)) (shared v := 1 (hat pause))) ((dshared v 1 ready)))
      (S_S)
      (Succ zero)))
    (test-judgment-holds
     (cc->>
      (machine (par (signal f (emit S)) (shared v := 1 pause)) ()) ()
      (machine (par (signal S_f (emit S_S)) (shared v := 1 (hat pause))) ((dshared v 1 ready)))
      (S_S)
      (Succ zero)))

    #|
    (test-judgment-holds
     (c->>
      (seq (loop (present h nothing (hat pause))) (trap (exit (Succ (Succ zero)))))
      ))
    |#
    (test-judgment-holds
     (c->>
      (machine
       (present Q (par pause nothing) (signal z nothing))
       ())
      ((Q one))

      (machine
       (present S_Q (par (hat pause) nothing) (signal S_z nothing))
       ())
      ()
      (Succ zero)))
    (test-judgment-holds
     (c->>
      (machine
       (seq (trap (signal X (emit p))) (suspend (signal g pause) UU))
       ())
      ((g one) (X zero))
      (machine (seq (trap (signal S_X (emit S_p)))
                    (suspend (signal S_g (hat pause)) S_U))
               ())
      (S_p)
      (Succ zero)))
    (test-judgment-holds
     (c->>
      (machine
       (seq (suspend (loop (seq (hat pause) (emit QY))) t) (signal f (trap nothing)))
       ())
      ((t zero))
      (machine
       (seq (suspend (loop (seq (hat pause) (emit S_QY))) S_t) (signal f (trap nothing)))
       ())
      (S_QY)
      (Succ zero)))
    (test-judgment-holds
     (c->>
      (machine
       (seq (suspend (hat pause) N) (signal k (emit Z)))
       ())
      ((N zero))
      (machine
       (seq (suspend pause S_N) (signal S_k (emit S_Z)))
       ())
      (S_Z)
      zero))
    (test-judgment-holds
     (c->>
      (machine
       (seq (trap (hat pause)) (signal n (emit h)))
       ())
      ()
      (machine
       (seq (trap pause) (signal S_n (emit S_h)))
       ())
      (S_h)
      zero))
    (test-judgment-holds
     (cc->>
      (machine
       (seq (trap (hat pause)) (signal n (emit h)))
       ())
      ()
      (machine
       (seq (trap pause) (signal S_n (emit S_h)))
       ())
      (S_h)
      zero))
    (test-judgment-holds
     (cc->>
      (machine
       (seq (loop (hat pause)) (trap nothing))
       ())
      ()
      (machine
       (seq (loop (hat pause)) (trap nothing))
       ())
      ()
      one))
    (test-judgment-holds
     (cc->>
      (machine
       (signal A (signal Gz (emit H)))
       ())
      ()
      (machine
       (signal S_A (signal S_Gz (emit S_H)))
       ())
      (S_H)
      zero))
    (test-judgment-holds
     (cc->>
      (machine
       (trap (trap (exit (Succ two))))
       ())
      ()
      (machine
       (trap (trap (exit (Succ two))))
       ())
      ()
      zero))

    (test-judgment-holds
     (cc->>
      (machine
       (seq (trap (trap (exit (Succ two)))) (signal A (signal Gz (emit H))))
       ())
      ()
      (machine
       (seq (trap (trap (exit (Succ two)))) (signal S_A (signal S_Gz (emit S_H))))
       ())
      (S_H)
      zero))

    (test-judgment-holds (cc->>
                          (machine
                           (loop (hat pause))
                           ())
                          ()
                          (machine
                           (loop (hat pause))
                           ())
                          ()
                          one))
    (test-judgment-holds (cc->>
                          (machine
                           (seq (emit z) (loop pause))
                           ())
                          ()
                          (machine
                           (seq (emit S_z) (loop (hat pause)))
                           ())
                          (z)
                          one))
    (test-judgment-holds (cc->>
                          (machine
                           (seq (emit z) (loop (hat pause)))
                           ())
                          ()
                          (machine
                           (seq (emit S_z) (loop (hat pause)))
                           ())
                          ()
                          one))
    (test-judgment-holds (cc->>
                          (machine
                           (trap (trap (exit (Succ two))))
                           ())
                          ()
                          any_1
                          any_2
                          any_3))
    (test-judgment-holds
     (cc->>
      (machine
       (seq (trap (trap (exit (Succ two)))) (signal IH nothing))
       ())
      ()
      (machine
       (seq (trap (trap (exit (Succ two)))) (signal S_IH nothing))
       ())
      ()
      zero))

    (test-judgment-holds
     (cc->>
      (machine
       (par (seq (emit Q) (emit Q)) (signal S pause))
       ())
      ()
      (machine
       (par (seq (emit S_Q) (emit S_Q)) (signal S_v (hat pause)))
       ())
      (Q)
      one)))

  (define-judgment-form esterel-check
    #:mode (traps-okay I I)
    #:contract (traps-okay pbar NL)

    [(traps-okay (exit nat_h) NL)
     -----------
     (traps-okay (exit nat_h) (nat_h NL))]

    [-----------
     (traps-okay (exit nat_h) (nat_h NL))]

    [(traps-okay pbar ((Succ (Succ zero)) ()))
     ----------
     (traps-okay (trap pbar) ())]

    [(traps-okay pbar ((Succ nat) (nat NL)))
     ----------
     (traps-okay (trap pbar) (nat NL))]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (loop pbar) NL)]

    [---------
     (traps-okay nothing any)]

    [---------
     (traps-okay pause any)]

    [---------
     (traps-okay (hat pause) any)]

    [---------
     (traps-okay (emit S) any)]

    [(traps-okay pbar_l NL)
     (traps-okay pbar_r NL)
     ---------
     (traps-okay (seq pbar_l pbar_r) NL)]

    [(traps-okay pbar_l NL)
     (traps-okay pbar_r NL)
     ---------
     (traps-okay (present S pbar_l pbar_r) NL)]

    [(traps-okay pbar_l NL)
     (traps-okay pbar_r NL)
     ---------
     (traps-okay (par pbar_l pbar_r) NL)]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (signal S pbar) NL)]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (suspend pbar S) NL)]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (shared s := call pbar) NL)]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (var v := call pbar) NL)]

    [---------
     (traps-okay (<= s call) NL)]

    [---------
     (traps-okay (:= v call) NL)]

    [(traps-okay pbar NL)
     (traps-okay qbar NL)
     ---------
     (traps-okay (if v pbar qbar) NL)])

  (define-judgment-form esterel-check
    #:mode (loops-okay I)
    #:contract (loops-okay pbar)
    [-----------
     (loops-okay (exit nat_h))]

    [-----------
     (loops-okay (exit nat_h))]

    [(loops-okay pbar)
     ----------
     (loops-okay (trap pbar))]

    [---------
     (loops-okay nothing)]

    [---------
     (loops-okay pause)]

    [---------
     (loops-okay (hat pause))]

    [---------
     (loops-okay (emit S))]

    [(loops-okay pbar_l)
     (loops-okay pbar_r)
     ---------
     (loops-okay (seq pbar_l pbar_r))]

    [(loops-okay pbar_l)
     (loops-okay pbar_r)
     ---------
     (loops-okay (present S pbar_l pbar_r))]

    [(loops-okay pbar_l)
     (loops-okay pbar_r)
     ---------
     (loops-okay (par pbar_l pbar_r))]

    [(loops-okay pbar)
     ---------
     (loops-okay (signal S pbar))]

    [(loops-okay pbar)
     ---------
     (loops-okay (suspend pbar S))]

    [(loops-okay pbar)
     (K_s pbar (k ...))
     (where #f (∈ zero (k ...)))
     ---------
     (loops-okay (loop pbar))]
    )

  (define-judgment-form esterel-check
    #:mode (K_s I O)
    #:contract (K_s pbar (k ...))
    [----------
     (K_s nothing (zero))]
    [----------
     (K_s pause ((Succ zero)))]
    [----------;; identical. we're pretending its a p
     (K_s (hat pause) ((Succ zero)))]
    [----------
     (K_s (exit k) (k))]

    [(K_s pbar (k_1 ...))
     (K_s qbar (k_2 ...))
     ----------
     (K_s (present S pbar qbar) (U (k_2 ...) (k_2 ...)))]
    [(K_s pbar (k ...))
     ----------
     (K_s (suspend S pbar) (k ...))]
    [(K_s pbar (k_1 ...))
     (K_s qbar (k_2 ...))
     (where #t (∈ 0 (k_1 ...)))
     ----------
     (K_s (seq pbar qbar) (U (k_2 ...) (without zero (k_1 ...))))]
    [(K_s pbar (k ...))
     (where #f (∈ 0 (k ...)))
     ----------
     (K_s (seq pbar qbar) (k ...))]
    [(K_s pbar (k ...))
     ----------
     (K_s (loop pbar) (without zero (k ...)))]
    [(K_s pbar (k_1 ...))
     (K_s qbar (k_2 ...))
     ----------
     (K_s (seq pbar qbar) (metamax (k_2 ...) (k_1 ...)))]
    [(K_s pbar (k ...))
     ----------
     (K_s (trap pbar) (↓ (k ...)))]
    [(K_s pbar (k ...))
     ----------
     (K_s (suspend S pbar) (k ...))])

  (define-metafunction esterel-eval
    fix-env : M -> M

    [(fix-env (machine (exit nat_h) data))
     (machine (exit nat_h) data)]

    [(fix-env (machine pause data))
     (machine pause data)]

    [(fix-env (machine (hat pause) data))
     (machine (hat pause) data)]

    [(fix-env (machine nothing data))
     (machine nothing data)]

    [(fix-env (machine (emit S) data))
     (machine (emit S) data)]

    [(fix-env (machine (trap pbar) data))
     (machine (trap pbar_*) data_*)
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

    [(fix-env (machine (loop pbar) data))
     (machine (loop pbar_*) data_*)
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

    [(fix-env (machine (signal S pbar) data))
     (machine (signal S pbar_*) data_*)
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

    [(fix-env (machine (suspend pbar S) data))
     (machine (suspend pbar_* S) data_*)
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

    [(fix-env (machine (seq pbar qbar) data))
     (machine (seq pbar_* qbar_*) (U data_* data_**))
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))
     (where (machine qbar_* data_**) (fix-env (machine qbar data)))]

    [(fix-env (machine (par pbar qbar) data))
     (machine (par pbar_* qbar_*) (U data_* data_**))
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))
     (where (machine qbar_* data_**) (fix-env (machine qbar data)))]

    [(fix-env (machine (present S pbar qbar) data))
     (machine (present S pbar_* qbar_*) (U data_* data_**))
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))
     (where (machine qbar_* data_**) (fix-env (machine qbar data)))]

    [(fix-env (machine (shared s := call phat) data))
     (machine (shared s := call_* phat_*) data_**)
     (where call_* (delete-bad-var-call s data call))
     (where data_* (data<- data s (eval-call call_* data) ready))
     (where (machine phat_* data_**) (fix-env (machine phat data_*)))]

    [(fix-env (machine (shared s := call p) data))
     (machine (shared s := call_* p_*) data_**)
     (where call_* (delete-bad-var-call s data call))
     (where data_* (data<- data s (eval-call call_* data) old))
     (where (machine p_* data_**) (fix-env (machine p data_*)))]

    [(fix-env (machine (<= s call) data))
     (machine (<= s_* call_*) data)
     (where s_* (visible-s s data))
     (where call_* (delete-bad-var-call s_* data call))]

    [(fix-env (machine (var v := call pbar) data))
     (machine (var v := call_* pbar_*) data_**)
     (where call_* (delete-bad-var-call ,(gensym) data call))
     (where data_* (data<- data v (eval-call call_* data)))
     (where (machine pbar_* data_**) (fix-env (machine pbar data_*)))]

    [(fix-env (machine (:= v call) data))
     (machine (:= v_* call_*) data)
     (where v_* (visible-v v data))
     (where call_* (delete-bad-var-call ,(gensym) data call))]

    [(fix-env (machine (if v pbar qbar) data))
     (machine (if v_* pbar_* qbar_*) (U data_* data_**))
     (where v_* (delete-bad-var-call ,(gensym) data v))
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))
     (where (machine qbar_* data_**) (fix-env (machine qbar data)))])

  (define-metafunction esterel-eval
    visible-s : s data -> s
    [(visible-s s data)
     s
     (where #t (∈ s (get-shared data)))]
    [(visible-s s data) (get-random-s data)])

  (define-metafunction esterel-eval
    visible-v : v data -> v
    [(visible-v v data)
     s
     (where #t (∈ v (get-shared data)))]
    [(visible-v v data) (get-random-v data)])


  (define-metafunction esterel-eval
    get-shared : data -> (s ...)
    [(get-shared ()) ()]
    [(get-shared ((dshared s any_1 any_2) data-elem ...))
     (s s_r ...)
     (where (s_r ...) (get-shared (data-elem ...)))]
    [(get-shared ((dvar any_1 any_2) data-elem ...))
     (get-shared (data-elem ...))])

  (define-metafunction esterel-eval
    get-random-s : data -> s
    [(get-random-s data)
     ,(random-ref `(s ...))
     (where (s ...) (get-shared data))])

  (define-metafunction esterel-eval
    get-random-v : data -> s
    [(get-random-v data)
     ,(random-ref `(v ...))
     (where (v ...) (get-unshared data))])

  (define-metafunction esterel-eval
    get-unshared : data -> (v ...)
    [(get-unshared ()) ()]
    [(get-unshared ((dvar v any) data-elem ...))
     (v v_r ...)
     (where (v_r ...) (get-unshared (data-elem ...)))]
    [(get-unshared (any data-elem ...))
     (v_r ...)
     (where (v_r ...) (get-unshared (data-elem ...)))])



  (define-metafunction esterel-eval
    delete-bad-var-call : s data call -> call
    [(delete-bad-var-call s data (+ call ...))
     (+ (delete-bad-var-call s data call) ...)]
    [(delete-bad-var-call s data s) 1]
    [(delete-bad-var-call s_0 data s_1)
     s_1
     (where #t (∈ s_1 (get-shared data)))]
    [(delete-bad-var-call s_0 data s_1) 1]
    [(delete-bad-var-call s data datum) datum])

  (define-extended-language uniquify-lang esterel-eval
    #:binding-forms
    (shared s := call pbar #:refers-to s)
    (var v := call pbar #:refers-to v))
  (define-metafunction uniquify-lang
    ;uniquify : pbar -> pbar
    [(uniquify (any ...))
     ((uniquify any) ...)]
    [(uniquify any) any])


  (define-judgment-form esterel-check
    #:mode     (okay I)
    #:contract (okay pbar)
    [(traps-okay pbar ())
     --------
     (okay pbar)]))

(module+ slow
  (require (submod ".." test))
  (test-case "slow tests"
    (time ;; failing
     (test-judgment-holds
      (cc->>
       (machine
        (par (signal TY (signal a nothing))
             (signal S (par (par (emit R) pause)
                            pause)))
        ())
       ()
       (machine (par (signal S_TY (signal S_a nothing))
                     (signal S_S (par (par (emit S_R) (hat pause))
                                      (hat pause))))
                ())
       (R)
       one)))
    (time ;; failing
     (test-judgment-holds
      (cc->>
       (machine
        (par (signal K (signal Z (par nothing pause))) (signal R nothing))
        ())
       ()
       (machine
        (par (signal S_K (signal S_Z (par nothing (hat pause)))) (signal S_R nothing))
        ())
       ()
       one)))))

(module+ random
  (require (submod ".." test))
  (define-syntax-rule (tjh e)
    (begin
      (test-judgment-holds e)
      (judgment-holds e)))
  (test-case "random tests"
    ;(current-traced-metafunctions 'all)
    (redex-check
     esterel-check
     #:satisfying (okay p-check)
     (begin
       ;(displayln `p-check)
       (term-let ([p `(uniquify p-check)])
                 (tjh (cc->> (fix-env (machine p ()))
                             (random-E (free-signal-vars p))
                             (machine pbar data_*) (S ...) k))))
     #:attempts 333
     )
    (redex-check
     esterel-check
     #:satisfying (okay phat-check)
     (begin
       ;(displayln `phat-check)
       (term-let ([p `(uniquify phat-check)])
                 (tjh (cc->> (fix-env (machine p ()))
                             (random-E (free-signal-vars p))
                             (machine pbar data_*) (S ...) k))))
     #:attempts 333
     )
    (redex-check
     esterel-check
     #:satisfying (okay pbar-check)
     (begin
       ;(displayln `pbar-check)
       (term-let ([p `(uniquify pbar-check)])
                 (tjh (cc->> (fix-env (machine p ()))
                             (random-E (free-signal-vars p))
                             (machine pbar data_*) (S ...) k))))
     #:attempts 333
     )))

(module+ test
  (test-case "eval part 2"
    (test-judgment-holds
     (c->>
      (machine (par (signal pQ (emit x)) (emit C)) ())
      ()
      (machine (par (signal S_pQ (emit S_x)) (emit S_C)) ())
      any
      zero))
    (test-judgment-holds
     (cc->>
      (machine (par (signal pQ (emit x)) (emit C)) ())
      ()
      (machine (par (signal S_pQ (emit S_x)) (emit S_C)) ())
      any
      zero))
    (test-judgment-holds
     (c->>
      (fix-env
       (machine
        (seq (shared c := Q nothing) (suspend pause plU))
        ()))
      ()
      (machine (seq (shared s_c := 1 nothing)
                    (suspend (hat pause) S_p))
               ((dshared s_c 1 ready)))
      ()
      (Succ zero)))
    (test-judgment-holds
     (cc->>
      (fix-env
       (machine
        (seq (shared c := Q nothing) (suspend pause plU))
        ()))
      ()
      (machine (seq (shared s_c := 1 nothing)
                    (suspend (hat pause) S_p))
               ((dshared s_c 1 ready)))
      ()
      (Succ zero)))))

(module+ all (require (submod ".." test) (submod ".." slow) (submod ".." random)))

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

(define-metafunction esterel-eval
  #|
  ↓ : k or (k ...) -> k or (k ...)
  |#
 [(↓ zero) zero]
 [(↓ two) zero]
 [(↓ one) one]
 [(↓ nat) (nat- nat one)]
 [(↓ (k ...)) ((↓ k) ...)])

(module+ test
  (test-case "Can bugs"
    ;(current-traced-metafunctions '(Can Can_V))
    (test-equal
     `(Can (present S pause (trap (emit A))) ())
     `( ((A (Succ zero)))
        ((Succ zero) zero)
        () ))
    (test-equal
     `(Can (suspend (loop (seq (hat pause) (emit QY))) tt) ())
     `( ((QY (Succ zero)))
        ((Succ zero))
        () ))
    (test-equal
     `(Can (suspend (hat pause) xJux) ())
     `( () ((Succ zero) zero) () ))
    (test-equal
     `(Can_S (seq (· (emit S)) pause) ((S ⊥)))
     `((S one)))
    (test-equal
     `(Can_S (seq (· (hat pause)) (emit S)) ())
     `((S one)))
    (test-equal
     `(Can_K (· (hat pause)) ())
     `(zero))
    (test-equal
     `(∉ zero (Can_K (· (hat pause)) ()))
     #f)))

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

(module+ test
  (check-equal?
   (term (without (zero zero) zero))
   (term ()))
  (check-equal?
   (term (Can (seq (trap (· (present S5 nothing (exit (Succ (Succ zero)))))) pause) ((S5 ⊥))))
   (term (() ((Succ zero)) ()))))

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

(module+ test
  (check-true
   (redex-match?
    esterel-eval
    p
    `(signal
  O4
  (par
   (signal
    A1
    (par
     (signal
      B2
      (par
       (signal
        R3
        (par
         (loop
          (trap
           (par
            (seq
             (suspend
              (seq
               (seq
                (par
                 (trap
                  (loop
                   (seq pause (present A1 (exit (Succ (Succ zero))) nothing))))
                 (trap
                  (loop
                   (seq
                    pause
                    (present B2 (exit (Succ (Succ zero))) nothing)))))
                (emit O4))
               (loop pause))
              R3)
             (exit (Succ (Succ zero))))
            (seq
             (trap
              (loop
               (seq pause (present R3 (exit (Succ (Succ zero))) nothing))))
             (exit (Succ (Succ zero)))))))
         (loop (seq (present R3 (emit R3) nothing) pause))))
       (loop (seq (present B2 (emit B2) nothing) pause))))
     (loop (seq (present A1 (emit A1) nothing) pause))))
   (loop (seq (present O4 (emit O4) nothing) pause))))
    ))


  (test-case "abro"
    (judgment-holds
     (cc->>
      (machine
       (loop
        (trap
         (par
          (seq
           (suspend
            (seq
             (seq
              (par
               (trap
                (loop
                 (seq
                  pause
                  (present A (exit (Succ (Succ zero))) nothing))))
               (trap
                (loop
                 (seq
                  pause
                  (present B (exit (Succ (Succ zero))) nothing)))))
              (emit O))
             (loop pause))
            R3)
           (exit (Succ (Succ zero))))
          (seq
           (trap
            (loop
             (seq pause (present R (exit (Succ (Succ zero))) nothing))))
           (exit (Succ (Succ zero)))))))
       ())
      ((A (Succ zero)) (B zero) (R zero))
      any_1 any_2 any_3))))
