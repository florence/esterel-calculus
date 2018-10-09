#lang racket
(provide
 ;; language for generating test cases
 esterel-check
 ;; take a program and its inputs and outputs and
 ;; make it closed. some persentage of the time force it to
 ;; use a low number of signals.
 fixup
 ;; close a given program
 fix
 ;; close a given program, forcing it to
 ;; use a small number of signals
 fix/low-signals
 ;; setup the environment use by our reduction
 setup-r-env
 ;; setup the environment used by the COS model
 setup-*-env
 ;; check what esterelv5 does on a given program
 esterel-oracle
 hiphop-oracle)
(require redex/reduction-semantics
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/test/external
         esterel-calculus/hiphop/run-hiphop
         (prefix-in calculus: esterel-calculus/redex/model/calculus)
         (prefix-in standard: esterel-calculus/redex/model/reduction)
         (prefix-in cos: esterel-calculus/cos-model)
         racket/random
         (prefix-in r: racket))
(provide (all-defined-out)
         warn-about-uninstalled-esterel)
(define-syntax quasiquote (make-rename-transformer #'term))
(module+ test (require rackunit))

(define-union-language esterel-eval* esterel-eval (cos: cos:esterel-eval))
(define-metafunction esterel-eval*
  convert : p -> cos:p
  [(convert nothing) nothing]
  [(convert pause) pause]
  [(convert (seq p q))
   (seq (convert p) (convert q))]
  [(convert (signal S p))
   (signal S (convert p))]
  [(convert (par p q))
   (par (convert p) (convert q))]
  [(convert (loop p))
   (loop (convert p))]
  [(convert (present S p q))
   (present S (convert p) (convert q))]
  [(convert (emit S)) (emit S)]
  [(convert (suspend p S))
   (suspend (convert p) S)]
  [(convert (trap p))
   (trap (convert p))]
  [(convert (exit n))
   (exit (cos:to-nat ,(+ 2 `n)))]
  [(convert (shared s := e p))
   (shared s := e (convert p))]
  [(convert (<= s e)) (<= s e)]
  [(convert (var x := e p))
   (var x := e (convert p))]
  [(convert (:= x e)) (:= x e)]
  [(convert (if x p q))
   (if x (convert p) (convert q))])

(define-extended-language esterel-check esterel-eval*
  (p-check
   nothing
   pause
   (seq p-check p-check)
   (par p-check p-check)
   (trap p-check)
   (exit n)
   (signal S p-check)
   (suspend p-check S)
   (present S p-check p-check)
   (emit S)
   (loop p-check)
   (shared s := e-check p-check)
   (<= s e-check)
   (var x := e-check p-check)
   (:= x e-check)
   (if x p-check p-check))

  (e-check ::= (+ s/l-check ...))
  (s/l-check ::= s x n))


(define (setup-*-env ins in)
  (for/list ([i in])
    (if (member i ins)
        `(,i (Succ zero))
        `(,i zero))))

(define (setup-r-env ins in)
  (for/list ([i in]
             #:when (member i ins))
    `(sig ,i present)))

;;  (p (S ...) (S ...) ((S ...) ...)) -> ((ρ θ p) (S ...) (S ...) ((S ...) ...))
;; The first S... is a list of input signals.
;; The second S... is a list of output signals
;; The ((S ...) ...) is a list of input signals to be present in each instant
;; The `p` resulting program will be closed. θ will bind the input and output signals
(define (fixup e)
  (redex-let
   esterel-eval
   ([(p (S_i ...) (S_o ...) ((S ...) ...)) e])
   (when (null? `(S_o ...)) (error 'fixup "expected at least one output signal"))
   (when (null? `(S_i ...)) (error 'fixup "expected at least one input signal"))
   (define low-signals? (< (random) 1/8))
   (define generate-S (make-generator "S" e))
   (define generate-s (make-generator "s" e))
   (define signals (build-list (add1 (random 2)) (lambda (_) (generate-S))))
   (define shareds (build-list (add1 (random 2)) (lambda (_) (generate-s))))
   (define SI (remove-duplicates `(S_i ...)))
   (define SO (remove-duplicates `(S_o ...)))
   (define (wrap p signals shareds)
     (match* (signals shareds)
       [((cons s r) _)
        `(signal ,s ,(wrap p r shareds))]
       [(n (cons s r))
        `(shared ,s := (+) ,(wrap p n r))]
       [(_ _) p]))
   (if low-signals?
       (let ([p*
              (wrap
               `(fix/low-signals p
                                 ,signals
                                 ,shareds
                                 ()
                                 0)
               signals
               shareds)])
         (list
          p*
          `(remove-unused/2 ,SI ,p*)
          `(remove-unused/2 ,SO ,p*)
          `(generate-inputs ())))
       (let ([p* `(fix p ,SI ,SO () () () 0)])
         (list
          p*
          `(remove-unused/2 ,SI ,p*)
          `(remove-unused/2 ,SO ,p*)
          `(generate-inputs (remove-unused ,SI ,p*)))))))

;; keep the first two so we have at least some tests with unused variables.
(define-metafunction esterel-eval
  remove-unused/2 : (S ...) p -> (S ...)
  [(remove-unused/2 (S_1 S_2 S ...) p)
   (S_1 S_2 S_3 ...)
   (where (S_3 ...) (remove-unused (S ...) p))]
  [(remove-unused/2 (S ...) p ) (S ...)])
(module+ test
  (check-equal?
   `(remove-unused/2 (Sf) (signal S1 (shared s1 := (+ 0) (shared s2 := (+ 0) nothing))))
   '(Sf))
  (check-equal?
   `(remove-unused/2 (S1 S2 S3) nothing)
   '(S1 S2)))
(define-metafunction esterel-eval
  remove-unused : (S ...) p -> (S ...)
  [(remove-unused () p) ()]
  [(remove-unused (S S_1 ...) p)
   (S S_2 ...)
   (where (any ... S any_2 ...) (FV p))
   (where (S_2 ...) (remove-unused (S_1 ...) p))]
  [(remove-unused (S S_1 ...) p)
   (remove-unused (S_1 ...) p)])
(module+ test
  (check-equal?
   `(remove-unused (S1 S2 S3) nothing)
   '())
  (check-equal?
   `(remove-unused (S1 S2 S3) (emit S2))
   '(S2)))

;; make-generator : string sexp -> (-> symbol)
;; returns a generator that generates symbols that
;; begin with `starter-prefix` and are guaranteed
;; to not appear in `sexp`
(define (make-generator starter-prefix sexp)
  (define reg (regexp (~a "^" (regexp-quote starter-prefix) "([0-9]+)$")))
  (define largest-number-suffix 0)
  (let loop ([e sexp])
    (cond
      [(pair? e) (loop (car e)) (loop (cdr e))]
      [(symbol? e)
       (define m (regexp-match reg (symbol->string e)))
       (when m (set! largest-number-suffix
                     (max (string->number (list-ref m 1))
                          largest-number-suffix)))]))
  (λ ()
    (set! largest-number-suffix (+ largest-number-suffix 1))
    (string->symbol (~a starter-prefix largest-number-suffix))))
(module+ test
  (check-equal? ((make-generator "x" #f)) 'x1)
  (check-equal? ((make-generator "x" '(((x11 x123) y xz123789432789)))) 'x124)
  (check-equal?
   (let ([g (make-generator "x" '(((x11 x123) y xz123789432789)))])
     (g)
     (g)
     (g))
   'x126))

;; p (listof S) (listof S) (Listof (listof S)) -> (Listof (Listof S))
;; input is analagous to `fixup`.
;; Runs the given program as an esterel module and gives back the signals present in each instant.
(define (esterel-oracle p is os ss)
  (define mod `(TEST ,is ,os ,p))
  (define res (run-with-signals mod ss))
  (match res
    ['not-installed 'not-installed]
    [(or 'instantaneous-loop 'non-constructive)
     'non-constructive]
    [(list r ...) res]
    [else (error 'esterel-exec "unknown error: ~a" res)]))
(define (hiphop-oracle p is os ss)
  (define mod `(TEST ,is ,os ,p))
  (define res (run-hiphop-with-signals mod ss))
  (match res
    ['not-installed 'not-installed]
    [#f
     'non-constructive]
    [(list r ...) res]
    [else (error 'esterel-exec "unknown error: ~a" res)]))

;; like `fix` but forces that no new signals are introduced by the program, and
;; input and output signals are not differentiated.
(define-metafunction esterel-eval
  fix/low-signals : p (S ...) (s ...) (x ...) n -> p
  [(fix/low-signals nothing (S ...) (s ...) (x ...) n)
   nothing]
  [(fix/low-signals pause (S ...) (s ...) (x ...) n)
   pause]
  [(fix/low-signals (exit n) (S ...) (s ...) (x ...) n_max)
   ,(if (zero? `n_max)
        `nothing
        `(exit ,(random `n_max)))]
  [(fix/low-signals (emit any) (S ...) (s ...) (x ...) n_max)
   (emit ,(random-ref `(S ...)))]
  [(fix/low-signals (signal any p) (S ...) (s ...) (x ...) n_max)
   (fix/low-signals p (S ...) (s ...) (x ...) n_max)]
  [(fix/low-signals (present any p q) (S ...) (s ...) (x ...) n_max)
   (present ,(random-ref `(S ...))
            (fix/low-signals p (S ...) (s ...) (x ...) n_max)
            (fix/low-signals q (S ...) (s ...) (x ...) n_max))]
  [(fix/low-signals (par p q) (S ...) (s ...) (x ...) n_max)
   (par
    (fix/low-signals p (S ...) (s ...) (first-half (x ...)) n_max)
    (fix/low-signals q (S ...) (s ...) (second-half (x ...)) n_max))]
  [(fix/low-signals (seq p q) (S ...) (s ...) (x ...) n_max)
   (seq
    (fix/low-signals p (S ...) (s ...) (x ...) n_max)
    (fix/low-signals q (S ...) (s ...) (x ...) n_max))]
  [(fix/low-signals (loop^stop p q) (S ...) (s ...) (x ...) n_max)
   (loop^stop
    (fix/low-signals p (S ...) (s ...) (x ...) n_max)
    (fix/low-signals q (S ...) (s ...) (x ...) n_max))]
  [(fix/low-signals (loop p) (S ...) (s ...) (x ...) n_max)
   (loop
    (fix/low-signals p (S ...) (s ...) (x ...) n_max))]
  [(fix/low-signals (suspend p any) (S ...) (s ...) (x ...) n_max)
   (suspend
    (fix/low-signals p (S ...) (s ...) (x ...) n_max)
    ,(random-ref `(S ...)))]
  [(fix/low-signals (trap p) (S ...) (s ...) (x ...) n_max)
   (trap
    (fix/low-signals p (S ...) (s ...) (x ...) ,(add1 `n_max)))]
  [(fix/low-signals (shared s_d := e p) (S ...) (s ...) (x ...) n_max)
   (fix/low-signals p (S ...) (s ...) (x ...) n_max)]
  [(fix/low-signals (<= s_d e) (S ...) (s ...) (x ...) n_max)
   (<= ,(random-ref `(s ...)) (fix/e e (s ... x ...)))]
  [(fix/low-signals (var x_d := e p) (S ...) (s ...) (x ...) n_max)
   (var x_n := (fix/e e (s ... x ...))
        (fix/low-signals p (S ...) (s ...) (x_n x ...) n_max))
   (where x_n ,(gensym 'xrandom-var))]
  [(fix/low-signals (:= x_d e) (S ...) (s ...) (x ...) n_max)
   ,(if (null? `(x ...))
        `nothing
        `(:= ,(random-ref `(x ...))
             (fix/e e (s ... x ...))))]
  [(fix/low-signals (if x_if p q) (S ...) (s ...) (x ...) n_max)
   ,(if (null? `(x ...))
        `(fix/low-signals p (S ...) (s ...) (x ...) n_max)
        `(if
          (fix/e x_if (x ...))
          (fix/low-signals p (S ...) (s ...) (x ...) n_max)
          (fix/low-signals q (S ...) (s ...) (x ...) n_max)))]

  [(fix/low-signals (ρ θ p) (S ...) (s ...) (x ...) n_max)
   (ρ θ
      ;;TODO this isn't great, re low-signals...
      (fix/low-signals p (S_θ ... S ...) (s_θ ... s ...) (x_θ ... x ...) n_max))
   (where ((S_θ ...) (s_θ ...) (x_θ ...)) (bindings θ (dom θ)))])

;; Takes a program, input signals, output signals, local bound signals,
;; locally bound shared variables, locally bound sequential variables, and current depth of `trap` forms
;; returns a program like `p`, but that is closed,
;; and enforces that input signals are only tested for, and that output
;; signals are only emitted.
(define-metafunction esterel-eval
  fix : p (S ...) (S ...) (S ...) (s ...) (x ...) n -> p
  [(fix nothing (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   nothing]
  [(fix pause (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   pause]
  [(fix (exit n) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   ,(if (zero? `n_max)
        `nothing
        `(exit ,(random `n_max)))]
  [(fix (emit S) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (emit ,(random-ref `(S_o ... S_b ...)))]
  [(fix (signal S_d p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (signal S (fix p (S_i ...) (S_o ...) (S S_b ...) (s ...) (x ...) n_max))
   (where S ,(gensym 'S))
   (where #t ,(<= (length `(S_b ...)) 3))]
  [(fix (signal S_d p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (where #t ,(> (length `(S_b ...)) 3))]
  [(fix (present S p q) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (present ,(random-ref `(S_i ... S_b ...))
            (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
            (fix q (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max))]
  [(fix (par p q) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (par
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (first-half (x ...)) n_max)
    (fix q (S_i ...) (S_o ...) (S_b ...) (s ...) (second-half (x ...)) n_max))]
  [(fix (seq p q) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (seq
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
    (fix q (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max))]
  [(fix (loop^stop p q) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (loop^stop
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
    (fix q (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max))]
  [(fix (loop p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (loop
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max))]
  [(fix (suspend p S) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (suspend
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
    ,(random-ref `(S_i ... S_b ...)))]
  [(fix (trap p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (trap
    (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) ,(add1 `n_max)))]
  [(fix (shared s_d := e p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (shared s_n := (fix/e e (s ... x ...))
           (fix p (S_i ...) (S_o ...) (S_b ...) (s_n s ...) (x ...) n_max))
   (where s_n ,(gensym 's))]

  [(fix (<= s_d e) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   ,(if (null? `(s ...))
        `nothing
        `(<= ,(random-ref `(s ...))
             (fix/e e (s ... x ...))))]

  [(fix (ρ θ p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (ρ θ
      (fix p (S_i ...) (S_o ...) (S_θ ... S_b ...) (s_θ ... s ...) (x_θ ... x ...) n_max))
   (where ((S_θ ...) (s_θ ...) (x_θ ...)) (bindings θ (dom θ)))]

  [(fix (var x_d := e p) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   (var x_n := (fix/e e (s ... x ...))
        (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x_n x ...) n_max))
   (where x_n ,(gensym 'x))]
  [(fix (:= x_d e) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   ,(if (null? `(x ...))
        `nothing
        `(:= ,(random-ref `(x ...))
             (fix/e e (s ... x ...))))]
  [(fix (if x_if p q) (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
   ,(if (null? `(x ...))
        `(fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
        `(if
          (fix/e x_if (x ...))
          (fix p (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)
          (fix q (S_i ...) (S_o ...) (S_b ...) (s ...) (x ...) n_max)))])


(define-metafunction esterel-eval
  bindings : θ {V ...} -> ({S ...} {s ...} {x ...})
  [(bindings θ {}) ({} {} {})]
  [(bindings θ {x V_t ...})
   ({S ...} {s ...} {x x_r ...})
   (where (var· x ev) (θ-ref θ x))
   (where ({S ...} {s ...} {x_r ...}) (bindings θ {V_t ...}))]

  [(bindings θ {s V_t ...})
   ({S ...} {s s_r ...} {x ...})
   (where (shar s ev shared-status) (θ-ref θ s))
   (where ({S ...} {s_r ...} {x ...}) (bindings θ {V_t ...}))]

  [(bindings θ {S V_t ...})
   ({S S_r ...} {s ...} {x ...})
   (where (sig S status) (θ-ref θ S))
   (where ({S_r ...} {s ...} {x ...}) (bindings θ {V_t ...}))])

(define-metafunction esterel-eval
  first-half : (V ...) -> (V ...)
  [(first-half (V ...))
   ,(let-values ([(f _) (split `(V ...))])
      f)])

(define-metafunction esterel-eval
  second-half : (V ...) -> (V ...)
  [(second-half (V ...))
   ,(let-values ([(_ s) (split `(V ...))])
      s)])
(define (split x)
  (split-at x (quotient (length x) 2)))

(define-metafunction esterel-eval
  fix/e : any (V ...) -> any
  [(fix/e n (V ...)) n]
  [(fix/e V ()) 0]
  [(fix/e V (V_s ...)) ,(random-ref `(V_s ...))]
  [(fix/e (f s/l ...) (V ...))
   (f (fix/e s/l (V ...)) ...)])

(define-metafunction esterel-eval
  generate-inputs : (S ...) -> ((S ...) ...)
  [(generate-inputs (S ...))
   ,(for/list ([_ (random 20)])
      (random-sample `(S ...)
                     (random (add1 (length `(S ...))))
                     #:replacement? #f))])

(define-metafunction esterel-eval
  add-extra-syms : p (S ...) -> p
  [(add-extra-syms p (S ...))
   (ρ θ p)
   (where θ
          ,(let loop ([l `((sig S unknown) ...)])
             (if (empty? l)
                 '·
                 (list (first l) (loop (rest l))))))])
