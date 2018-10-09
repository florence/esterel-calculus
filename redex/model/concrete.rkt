#lang racket
(require redex/reduction-semantics "shared.rkt" net/base64)
(provide redex->concrete id->concrete concrete->id)


; redex->concrete : Esterel-module -> string?
; Converts a whole Esteral module to concrete syntax.
(define (redex->concrete program)
  (match program
    [`(,name ,isigs ,osigs ,body)
     (call-with-output-string
      (λ (port)
        (fprintf port "module ~a: " name)
        (when (cons? isigs)
          (fprintf port "input ~a; " (list->comma-separated (map id->concrete isigs))))
        (when (cons? osigs)
          (fprintf port "output ~a; " (list->comma-separated (map id->concrete osigs))))
        (display (redex-term->concrete body) port)
        (display " end module" port)))]))

; list->comma-separated : [list-of symbol?] -> string?
; Converts a list of signals to a comma-separated string.
(define (list->comma-separated sigs)
  (match sigs
    [`()
     ""]
    [`(,s)
     (format "~a" s)]
    [`(,s . ,rest)
     (format "~a, ~a" s (list->comma-separated rest))]))


; redex-term->concrete : esterel-p -> string?
; Converts the parenthesized representation of Esterel terms
; the concrete syntax accepted by the Esterel compiler.
(define (redex-term->concrete t)
  (redex-term->concrete/depth t 0 '()))

; redex-term->concrete/depth : esterel-p natural? (list-of symbol?) -> string?
; Keeps track of the depth of traps in order to produce correct
; labels for exits.
(define (redex-term->concrete/depth t n sigs)
  (match t
    [`nothing            "nothing"]
    [`pause              "pause"]
    [`(signal ,S ,p)     (format "signal ~a in ~a end"
                                 (id->concrete S)
                                 (redex-term->concrete/depth p n sigs))]
    [`(present ,S ,p ,q) (format "present ~a then ~a else ~a end"
                                 (id->concrete S)
                                 (redex-term->concrete/depth p n sigs)
                                 (redex-term->concrete/depth q n sigs))]
    [`(emit ,S)          (format "emit ~a"
                                 (id->concrete S))]
    [`(par ,p ,q)        (format "[ ~a || ~a ]"
                                 (redex-term->concrete/depth p n sigs)
                                 (redex-term->concrete/depth q n sigs))]
    [`(loop ,p)  (format "loop ~a end"
                                 (redex-term->concrete/depth p n sigs))]
    [`(seq ,p ,q)        (format "~a; ~a"
                                 (redex-term->concrete/depth p n sigs)
                                 (redex-term->concrete/depth q n sigs))]
    [`(suspend ,p ,S)    (format "suspend ~a when ~a"
                                 (redex-term->concrete/depth p n sigs)
                                 (id->concrete S))]
    [`(trap ,p)          (format "trap T~a in ~a end"
                                 (add1 n)
                                 (redex-term->concrete/depth p (add1 n) sigs))]
    [`(exit ,m)          (format "exit T~a" (- n m))]
    ; state forms
    [`(shared ,s := ,e ,p)
                         (format
                          "signal ~a := ~a : combine integer with + in ~a end"
                          (id->concrete s)
                          (expr->concrete e sigs)
                          (redex-term->concrete/depth p n (cons s sigs)))]
    [`(<= ,s ,e)         (format "emit ~a(~a)"
                                 (id->concrete s)
                                 (expr->concrete e sigs))]
    [`(var ,x := ,e ,p)  (format "var ~a := ~a : integer in ~a end"
                                 (id->concrete x)
                                 (expr->concrete e sigs)
                                 (redex-term->concrete/depth p n sigs))]
    [`(:= ,x ,e)         (format "~a := ~a"
                                 (id->concrete x)
                                 (expr->concrete e sigs))]
    [`(if ,x ,p ,q)      (format "if ~a <> 0 then ~a else ~a end"
                                 (id->concrete x)
                                 (redex-term->concrete/depth p n sigs)
                                 (redex-term->concrete/depth q n sigs))]))

; expr->concrete : esterel-e (list-of symbol?) -> String
(define (expr->concrete e sigs)
  (match e
    [`(+)              "0"]
    [`(+ ,e1 . ,es)    (foldl (λ (y x) (format "~a + ~a"
                                               x
                                               (atom->concrete y sigs)))
                              (atom->concrete e1 sigs)
                              es)]
    [else              (error 'redex-expr->concrete "Unknown operator")]))

; atom->concrete : (or symbol? integer?) (list-of symbol?) -> String
(define (atom->concrete s sigs)
  (cond
    [(member s sigs) (format "?~a" (id->concrete s))]
    [(symbol? s) (id->concrete s)]
    [else (format "~a" s)]))

(define (id->concrete id)
  (apply
   string-append
   "V"
   (for/list ([k (in-string (symbol->string id))])
     (define n (char->integer k))
     (cond
       [(or
         (<= (char->integer #\A)
             n
             (char->integer #\Z))
         (<= (char->integer #\a)
             n
             (char->integer #\z)))
        (string #\_ k)]
       [else
        (string-append
         "_"
         (~a n))]))))
(define (concrete->id id)
  (define elems (rest (string-split (symbol->string id) "_")))
  (string->symbol
   (apply
    string
    (for/list ([e (in-list elems)])
      (cond
        [(string->number e) =>
         (lambda (x) (integer->char x))]
        [(= 1 (string-length e)) (string-ref e 0)]
        [else (error 'concrete->id "unknown id element ~a in ~a") e id])))))

(module+ test
  (require rackunit)
  (check-equal? (concrete->id (string->symbol (id->concrete 'S1))) 'S1)

  (check-equal? (list->comma-separated '()) "")
  (check-equal? (list->comma-separated '(A)) "A")
  (check-equal? (list->comma-separated '(A B)) "A, B")
  (check-equal? (list->comma-separated '(A B C)) "A, B, C")

  (define e expr->concrete)
  (check-equal? (e `(+) '())
                "0")
  (check-equal? (e `(+ 4) '())
                "4")
  (check-equal? (e `(+ a b) '())
                "V_a + V_b")
  (check-equal? (e `(+ a 5 b) '())
                "V_a + 5 + V_b")

  (define c redex-term->concrete)
  (check-equal? (c `nothing)
                "nothing")
  (check-equal? (c `pause)
                "pause")
  (check-equal? (c `(signal A pause))
                "signal V_A in pause end")
  (check-equal? (c `(seq pause nothing))
                "pause; nothing")
  (check-equal? (c `(seq pause (signal A pause)))
                "pause; signal V_A in pause end")
  (check-equal? (c `(signal A (par (emit A) pause)))
                "signal V_A in [ emit V_A || pause ] end")
  (check-equal? (c `(loop pause))
                "loop pause end")
  (check-equal? (c `(present A (emit O) (emit B)))
                "present V_A then emit V_O else emit V_B end")
  (check-equal? (c `(suspend pause S))
                "suspend pause when V_S")
  (check-equal? (c `(trap (exit 0)))
                "trap T1 in exit T1 end")
  (check-equal? (c `(trap (trap (exit 0))))
                "trap T1 in trap T2 in exit T2 end end")
  (check-equal? (c `(trap (trap (exit 1))))
                "trap T1 in trap T2 in exit T1 end end")
  (check-equal? (c `(loop (seq (par (emit A) pause)
                                   (emit O))))
                "loop [ emit V_A || pause ]; emit V_O end")
  (check-equal? (c `(shared s := (+ 3) pause))
                "signal V_s := 3 : combine integer with + in pause end")
  (check-equal? (c `(shared s := (+ 3) (<= s (+ s 1))))
                "signal V_s := 3 : combine integer with + in emit V_s(?V_s + 1) end")
  (check-equal?
   (c `(var x := (+ 0) (if x pause (:= x (+ x 1)))))
   "var V_x := 0 : integer in if V_x <> 0 then pause else V_x := V_x + 1 end end")

  (check-equal?
   (redex->concrete `(ABRO
                      (A B R)
                      (O)
                      (loop (seq (par (emit A) (emit B)) pause))))
   (string-append "module ABRO: input V_A, V_B, V_R; output V_O; "
                  "loop [ emit V_A || emit V_B ]; pause end end module"))
  (check-equal?
   (redex->concrete `(NoIn
                      ()
                      (O)
                      (emit O)))
   "module NoIn: output V_O; emit V_O end module")
  (check-equal?
   (redex->concrete `(NoOut
                      (I)
                      ()
                      (present I pause nothing)))
   "module NoOut: input V_I; present V_I then pause else nothing end end module"))
