#lang racket

#|
Forms not handled:
 - "CALL": front-end doesn't handle this
 - pre present S is error, because front-end doesn't handle this
 - output O := ... and emit S(v): pretty-printer doesn't print out the value
|#

(require esterel-calculus/hiphop/pretty-print
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         parser-tools/yacc
         racket/set
         racket/runtime-path)
(provide load-hiphop-test
         parse-hiphop-output/string)

; A Hiphop-module& is `(module& ,name ,input-signals ,output-signals ,@body)
; where
;   name           : Symbol
;   input-signals  : [List-of Symbol]
;   output-signals : [List-of Symbol]
;   body           : [List-of Esterel-expr&]

(define-empty-tokens hiphop-empty-tokens
  (EOF
   LPAREN
   RPAREN
   LBRACE
   RBRACE
   PLUS
   MINUS
   ABORT
   AWAIT
   EMIT
   EVERY
   EQUALS
   EXIT
   HALT
   IF
   IMMEDIATE
   LOCAL
   LOOP
   LOOP-EACH
   MODULE
   NOTHING
   PAUSE
   PARALLEL
   PRE
   PRESENT
   RUN
   SEQUENCE
   SUSPEND
   SUSTAIN
   TRAP
   WEAK-ABORT))

(define-tokens hiphop-tokens
  (IDENT NATURAL))

(define hiphop-lexer
  (lexer
   (#\( (token-LPAREN))
   (#\) (token-RPAREN))
   (#\{ (token-LBRACE))
   (#\} (token-RBRACE))
   (#\+ (token-PLUS))
   (#\- (token-MINUS))
   (#\= (token-EQUALS))
   ("Abort" (token-ABORT))
   ("Await" (token-AWAIT))
   ("Emit" (token-EMIT))
   ("Every" (token-EVERY))
   ("Exit" (token-EXIT))
   ("Halt" (token-HALT))
   ("If" (token-IF))
   ("immediate" (token-IMMEDIATE))
   ("Local" (token-LOCAL))
   ("Loop" (token-LOOP))
   ("LoopEach" (token-LOOP-EACH))
   ("Module" (token-MODULE))
   ("Nothing" (token-NOTHING))
   ("Pause" (token-PAUSE))
   ("Parallel" (token-PARALLEL))
   ("pre" (token-PRE))
   ("present" (token-PRESENT))
   ("Sequence" (token-SEQUENCE))
   ("Suspend" (token-SUSPEND))
   ("Sustain" (token-SUSTAIN))
   ("Run" (token-RUN))
   ("Trap" (token-TRAP))
   ("WeakAbort" (token-WEAK-ABORT))
   ((:: (:or alphabetic #\_)
        (:* (:or alphabetic numeric #\_)))
    (token-IDENT (string->symbol lexeme)))
   ((:+ numeric)
    (token-NATURAL (string->number lexeme)))
   (whitespace (hiphop-lexer input-port))
   ((eof) (token-EOF))))

(define hiphop-parser
  (parser
   (start modules)
   (end EOF)
   (error void)
   (tokens hiphop-tokens hiphop-empty-tokens)
   (grammar
    (modules [(module)
              (list $1)]
             [(module modules)
              (cons $1 $2)])
    (module [(IDENT MODULE signal-list block)
             `(module& ,$1 ,@$3 ,@$4)])
    (block [(LBRACE statement-list RBRACE) $2])
    (signal-list [() `(() ())]
                 [(MINUS IDENT signal-list)
                  (list (cons $2 (first $3)) (second $3))]
                 [(PLUS IDENT signal-list)
                  (list (first $3) (cons $2 (second $3)))]
                 [(IDENT signal-list)
                  (list (cons $1 (first $2)) (cons $1 (second $2)))])
    (statement-list [() `()]
                    [(statement statement-list) (cons $1 $2)])
    (statement
     [(ABORT signal-exp block)
      `(abort& ,$2 ,@$3)]
     [(AWAIT signal-exp)
      `(await& ,$2)]
     [(AWAIT IMMEDIATE signal-exp)
      `(await-immediate& ,$3)]
     [(AWAIT NATURAL signal-exp)
      `(await& ,$2 ,$3)]
     [(EMIT IDENT)
      `(emit& ,$2)]
     [(EVERY signal-exp block)
      `(every& ,$2 ,@$3)]
     [(EVERY NATURAL signal-exp block)
      `(every& (,$2 ,$3) ,@$4)]
     [(EVERY IMMEDIATE signal-exp block)
      `(every-immediate& ,$3 ,@$4)]
     [(EXIT IDENT LPAREN NATURAL RPAREN)
      `(exit& ,$2)]
     [(HALT)
      `halt&]
     [(IF signal-exp LBRACE statement statement RBRACE)
      `(present& ,$2 ,$4 ,$5)]
     [(LOCAL local-sigs block)
      (foldr (λ (sig block) `(signal& ,sig ,block))
             `(seq& ,@$3)
             $2)]
     [(LOOP block)
      `(loop& ,@$2)]
     [(LOOP-EACH signal-exp block)
      `(loop-each& ,$2 ,@$3)]
     [(NOTHING)
      `nothing&]
     [(PAUSE)
      `pause&]
     [(PARALLEL block)
      `(par& ,@$2)]
     [(RUN IDENT renamings)
      `(run& ,$2 ,@$3)]
     [(SEQUENCE block)
      `(seq& ,@$2)]
     [(SUSPEND signal-exp block)
      `(suspend& ,$2 ,@$3)]
     [(SUSTAIN IDENT)
      `(sustain& ,$2)]
     [(TRAP IDENT block)
      `(trap& ,$2 ,@$3)]
     [(WEAK-ABORT signal-exp block)
      `(weak-abort& ,$2 ,@$3)]
     [(WEAK-ABORT IMMEDIATE signal-exp block)
      `(weak-abort-immediate& ,$3 ,@$4)])
    (local-sigs [(plus-minus IDENT)
                 (list $2)]
                [(plus-minus IDENT local-sigs)
                 (cons $2 $3)])
    (plus-minus [() '()]
                [(PLUS plus-minus) '()]
                [(MINUS plus-minus) '()])
    (renamings  [()
                 '()]
                [(IDENT EQUALS IDENT renamings)
                 `([,$3 -> ,$1] ,@$4)])
    (signal-exp [(PRESENT IDENT)
                 $2]
                [(PRE signal-exp)
                 (error 'pre "signal expression not handled")]))))

; parse-hiphop : Input-port -> [List-of Hiphop-module&]
(define (parse-hiphop port)
  (hiphop-parser (λ () (hiphop-lexer port))))

; parse-hiphop/string : String -> [List-of Hiphop-module&]
(define (parse-hiphop/string program)
  (parse-hiphop (open-input-string program)))

(module+ test
  (require rackunit)
  (define p parse-hiphop/string)

  (check-equal? (p "MODULE0
                    Module -S +O +F +W {
                      WeakAbort present S {
                        Loop {
                          Emit O
                          Pause
                          Emit W
                        }
                      }
                      Emit F
                    }")
                '((module& MODULE0 (S) (O F W)
                           (weak-abort& S
                                        (loop& (emit& O) pause& (emit& W)))
                           (emit& F))))

  (check-equal? (p "MODULE0
                    Module -A -B -C -R +O {
                      LoopEach present R {
                        Parallel {
                          Await present A
                          Await present B
                          Await present C
                        }
                        Emit O
                      }
                    }")
                '((module& MODULE0 (A B C R) (O)
                           (loop-each& R
                                       (par&
                                        (await& A)
                                        (await& B)
                                        (await& C))
                                       (emit& O)))))

  (check-equal? (p "MODULE0
                    Module -I +O {
                      Local L {
                        Parallel {
                          Abort present L {
                            Loop {
                              Emit O
                              Pause
                            }
                          }
                          Sequence {
                            Await present I
                            Emit L
                          }
                        }
                      }
                    }")
                '((module& MODULE0 (I) (O)
                           (signal& L
                                    (seq&
                                     (par&
                                      (abort& L
                                              (loop& (emit& O) pause&))
                                      (seq& (await& I) (emit& L))))))))

  (check-equal? (p "MODULE0
                    Module -I +J +K +V {
                       Loop {
                          Sequence {
                             Abort present I {
                                Sequence {
                                   Emit J
                                   Pause
                                   Emit V
                                   Pause
                                }
                             }
                             If present I {
                                Emit K
                                Nothing
                             }
                          }
                       }
                    }")
                '((module& MODULE0 (I) (J K V)
                           (loop&
                            (seq&
                             (abort& I
                                     (seq& (emit& J) pause& (emit& V) pause&))
                             (present& I (emit& K) nothing&))))))
  
  (check-equal? (p "MODULE0
                    Module +O +S -T {
                       Loop {
                          Abort present T {
                             Emit S
                             Pause
                             Emit O
                          }
                          Pause
                       }
                    }")
                '((module& MODULE0 (T) (O S)
                           (loop&
                            (abort& T (emit& S) pause& (emit& O))
                            pause&))))

  (check-equal? (p "MODULE0
                    Module -I +J +O {
                       Sequence {
                          Suspend present I {
                             Loop {
                                Sequence {
                                   Emit O
                                   Pause
                                }
                             }
                          }
                          Emit J
                       }
                    }")
                '((module& MODULE0 (I) (J O)
                           (seq&
                            (suspend& I (loop& (seq& (emit& O) pause&)))
                            (emit& J)))))

  (check-equal? (p "MODULE0
                    Module -I +J +K {
                       Loop {
                          Abort present I {
                             Sustain J
                          }
                          Emit K
                       }
                    }")
                '((module& MODULE0 (I) (J K)
                           (loop& (abort& I (sustain& J))
                                  (emit& K)))))

  (check-equal? (p "MODULE0
                    Module -I +O {
                       Loop {
                          Await 3 present I
                          Emit O
                       }
                    }")
                '((module& MODULE0 (I) (O) (loop& (await& 3 I) (emit& O)))))

  (check-equal? (p "INNER Module -I +O {
                      Loop { If present I { Emit O Nothing } Pause }
                    }
                    OUTER Module +O {
                      Local S { Emit S Run INNER I=S }
                    }")
                '((module& INNER (I) (O)
                           (loop& (present& I (emit& O) nothing&) pause&))
                  (module& OUTER () (O)
                           (signal& S (seq& (emit& S) (run& INNER [S -> I]))))))

  (check-equal? (p "MODULE0 Module A { If present A { Emit A Nothing } }")
                '((module& MODULE0 (A) (A) (present& A (emit& A) nothing&))))
  
  (check-equal? (p "MODULE0 Module +A { Emit A Halt }")
                '((module& MODULE0 () (A) (emit& A) halt&)))

  (check-equal? (p "MODULE0 Module -I +O { Every present I { Emit O } }")
                '((module& MODULE0 (I) (O) (every& I (emit& O)))))

  (check-equal? (p "MODULE0 Module { Trap K { Pause Exit K(2) } }")
                '((module& MODULE0 () () (trap& K pause& (exit& K)))))
  
  (check-equal? (p "Hello Module +A { }")
                '((module& Hello () (A))))

  (check-equal? (p "Hello Module -A { } World Module +B -C { Emit B }")
                '((module& Hello (A) ())
                  (module& World (C) (B) (emit& B)))))


; A Hiphop-output is [List-of Hiphop-output-item]

; A Hiphop-output-item is one of:
; - '!reset
; - `(,[List-of Symbol] => ,[List-of Symbol])

(define-tokens hiphop-output-tokens
  (PROMPT SIGNAL))

(define-empty-tokens hiphop-output-empty-tokens
  (OUTPUT SEMICOLON RESET-COMMAND RESET-RESPONSE OUTPUT-EOF))

(define-lex-abbrev output-identifier (:+ (:or alphabetic numeric #\_)))

(define hiphop-output-lexer
  (lexer
   (#\; (token-SEMICOLON))
   ("--- Output:" (token-OUTPUT))
   ("!reset" (token-RESET-COMMAND))
   ((:: output-identifier #\>)
    (token-PROMPT lexeme))
   (output-identifier
    (token-SIGNAL (string->symbol lexeme)))
   ((:: "--- Automaton " output-identifier " reset")
    (token-RESET-RESPONSE))
   (whitespace (hiphop-output-lexer input-port))
   ((eof) (token-OUTPUT-EOF))))

(define hiphop-output-parser
  (parser
   (start sequence)
   (end OUTPUT-EOF)
   (error void)
   (tokens hiphop-output-tokens hiphop-output-empty-tokens)
   (grammar
    (sequence
      [() '()]
      [(cycle sequence) (cons $1 $2)])
    (cycle
     [(PROMPT signals SEMICOLON OUTPUT signals)
      `(,$2 => ,$5)]
     [(PROMPT RESET-COMMAND SEMICOLON RESET-RESPONSE)
      '!reset])
    (signals
     [() '()]
     [(SIGNAL signals) (cons $1 $2)]))))

; parse-hiphop-output : Input-port -> Hiphop-output
(define (parse-hiphop-output port)
  (hiphop-output-parser (λ () (hiphop-output-lexer port))))

; parse-hiphop-output/string : String -> Hiphop-output
(define (parse-hiphop-output/string output)
  (parse-hiphop-output (open-input-string output)))

(module+ test
  (define o parse-hiphop-output/string)

  (check-equal? (o "abortpar> ;
                    --- Output: O\n")
                '((() => (O))))
  (check-equal? (o "abortpar> ;
                    --- Output: O
                    abortpar> I;
                    --- Output:
                    abortpar> ;
                    --- Output: \n")
                '((() => (O)) ((I) => ()) (() => ())))
  (check-equal? (o "ABCRO> C B;
                    --- Output: O R S\n")
                '(((C B) => (O R S))))
  (check-equal? (o "abortpar> ;
                    --- Output:
                    abortpar> !reset;
                    --- Automaton abortpar reset
                    abortpar> ;
                    --- Output: O\n")
                '((() => ()) !reset (() => (O)))))

; hiphop-output->input-signals : Hiphop-output -> [List-of Symbol]
; Gets all the symbols used as input signals in a hiphop.js output log.
(define (hiphop-output->input-signals output)
  (apply set-union (map first (filter cons? output))))

; hiphop-output->output-signals : Hiphop-output -> [List-of Symbol]
; Gets all the symbols used as output signals in a hiphop.js output log.
(define (hiphop-output->output-signals output)
  (apply set-union (map third (filter cons? output))))

; load-hiphop-modules : path-string? -> [List-of Hiphop-module&]
(define (load-hiphop-modules path)
  (parse-hiphop/string (pretty-print path)))

; load-hiphop-output : path-string? -> Hiphop-output
(define (load-hiphop-output path)
  (call-with-input-file (path-replace-extension path ".out")
    parse-hiphop-output))

; split-hiphop-output : Hiphop-output -> [List-of Hiphop-output]
; Splits hiphop output on resets.
(define (split-hiphop-output output)
  (define-values (x xs) (splitf-at output cons?))
  (if (empty? xs)
      (list x)
      (cons x (split-hiphop-output (rest xs)))))

; hiphop-module->machine : Hiphop-module& -> S-expression
(define (hiphop-module->machine module)
  (match-define `(module& ,name ,input-signals ,output-signals ,@body) module)
  `(define-esterel-machine ,name
     #:inputs ,input-signals
     #:outputs ,output-signals
     (seq& ,@body)))

; hiphop-output->tests : Symbol Hiphop-output -> S-expression
(define (hiphop-output->tests name output)
  (map (λ (script) `(test-seq ,name ,@script))
       (split-hiphop-output output)))

; load-hiphop-tests : path-string? -> S-expression
(define (load-hiphop-test path)
  (define modules         (load-hiphop-modules path))
  (define output          (load-hiphop-output path))
  (define machine-name    (second (first modules)))
  `(test-case ,(format "~a" path)
     ,@(map hiphop-module->machine (reverse modules))
     ,@(hiphop-output->tests machine-name output)))
