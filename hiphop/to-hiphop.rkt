#lang racket
(require redex/reduction-semantics net/base64)
(provide redex->hiphop redex->hiphop/port id->hiphop hiphop->id)
(define-logger hiphop)

; redex->hiphop : Esterel-module -> string?
; Converts a whole Esteral module to hiphop syntax.
(define (redex->hiphop program)
  (call-with-output-string
    (λ (port) (redex->hiphop/port port program))))

(define hiphop-prologue
  (string-append "\"require hopscript\"\n"
                 "let hh = require(\"hiphop\");\n"
                 "let inSig = {accessibility: hh.IN};\n"
                 "let outSig = {accessibility: hh.OUT};\n"))

(define (redex->hiphop/port output program)
  (define port (open-output-string))
  (match program
    [`(,name ,isigs ,osigs ,body)
      (define-values (body-str obj-vars)
        (redex-term->hiphop body))
      (display hiphop-prologue port)
      (for ([i obj-vars])
        (fprintf port "let ~a;\n" (global-var-name i)))
      (fprintf port "let prg = <hh.module~a~a>~a</hh.module>;\n"
               (signals->hiphop-attributes "inSig" isigs)
               (signals->hiphop-attributes "outSig" osigs)
               body-str)
      (fprintf port "let machine = new hh.ReactiveMachine(prg, \"~a\");\n"
               name)])
  (define s (get-output-string port))
  (log-hiphop-debug s)
  (fprintf output s))

; signals->hiphop-attributes : string? [List-of symbol?] -> string?
; Turns a list of signals into a list of signal attributes with the
; given `attr-value`.
(define (signals->hiphop-attributes attr-value sigs)
  (apply string-append
         (map (λ (sig) (format " ~a=${~a}" (id->hiphop sig) attr-value)) sigs)))

; redex-term->hiphop : esterel-p -> string? natural?
; Converts the parenthesized representation of Esterel terms
; the hiphop syntax accepted by the Esterel compiler. The second result
; is the number of generated variables to be declared.
(define (redex-term->hiphop t)
  (define env (make-env))
  (define out (redex-term->hiphop/env t env))
  (values out (unbox (env-obj-vars env))))

; A translation environment with:
; - trap depth
; - known signals
; - mapping from source var names to object var names
; - box containing number of object vars generated
(struct env [depth sigs vars obj-vars])

; -> env?
; A fresh environment
(define (make-env)
  (env 0 '() '() (box 0)))

; symbol? env? -> env?
; Binds a signal in the environment.
(define (add-sig s e)
  (env (env-depth e)
       (cons s (env-sigs e))
       (env-vars e)
       (env-obj-vars e)))

; env? -> env?
; Updates the trap depth in the environment.
(define (next-trap e)
  (env (add1 (env-depth e))
       (env-sigs e)
       (env-vars e)
       (env-obj-vars e)))

; symbol? env? -> symbol? env?
; Creates a new obj var for the given symbol
(define (bind-var x e)
  (define n (unbox (env-obj-vars e)))
  (set-box! (env-obj-vars e) (add1 n))
  (define obj-var (global-var-name n))
  (values obj-var
          (env (env-depth e)
               (env-sigs e)
               (cons (list x obj-var) (env-vars e))
               (env-obj-vars e))))

; natural? -> symbol?
; How to translate natural numbers to variable names.
(define (global-var-name n)
  (string->symbol (format "V_V~a" n)))

; symbol? env? -> symbol?
; Looks up the object variable name to use for a source variable
(define (lookup-var x e)
  (cond
    [(assq x (env-vars e)) => second]
    [else (id->hiphop x)]))

; redex-term->hiphop/env : esterel-p natural? (list-of symbol?) -> string?
; Keeps track of the depth of traps in order to produce correct
; labels for exits.
(define (redex-term->hiphop/env t e)
  (match t
    [`nothing            "<hh.nothing/>"]
    [`pause              "<hh.pause/>"]
    [`(signal ,S ,p)     (format "<hh.local ~a>~a</hh.local>"
                                 (id->hiphop S)
                                 (redex-term->hiphop/env p e))]
    [`(present ,S ,p ,q) (format "<hh.if ~a>~a~a</hh.if>"
                                 (id->hiphop S)
                                 (redex-term->hiphop/env p e)
                                 (redex-term->hiphop/env q e))]
    [`(emit ,S)          (format "<hh.emit ~a/>"
                                 (id->hiphop S))]
    [`(par ,p ,q)        (format "<hh.parallel>~a~a</hh.parallel>"
                                 (redex-term->hiphop/env p e)
                                 (redex-term->hiphop/env q e))]
    [`(loop ,p)  (format "<hh.loop>~a</hh.loop>"
                                 (redex-term->hiphop/env p e))]
    [`(seq ,p ,q)        (format "<hh.sequence>~a~a</hh.sequence>"
                                 (redex-term->hiphop/env p e)
                                 (redex-term->hiphop/env q e))]
    [`(suspend ,p ,S)    (format "<hh.suspend ~a>~a</hh.suspend>"
                                 (id->hiphop S)
                                 (redex-term->hiphop/env p e))]
    [`(trap ,p)          (format "<hh.trap T~a>~a</hh.trap>"
                                 (add1 (env-depth e))
                                 (redex-term->hiphop/env p (next-trap e)))]
    [`(exit ,m)          (format "<hh.exit T~a/>" (- (env-depth e) m))]
    ; state forms
    [`(shared ,s := ,expr ,p)
                         (format
                          "<hh.local ~a=${{initApply: function () {return ~a} , combine: function (x,y) { return x + y; } }}>~a</hh.local>"
                          (id->hiphop s)
                          (expr->hiphop expr e)
                          (redex-term->hiphop/env p (add-sig s e)))]
    [`(<= ,s ,expr)      (format "<hh.emit ~a apply=${ function () {return ~a} }/>"
                                 (id->hiphop s)
                                 (expr->hiphop expr e))]
    [`(var ,x := ,expr ,p)
                         (define-values (x* e*) (bind-var x e))
                         (format "<hh.sequence><hh.atom apply=${function () {~a = ~a;}}/>~a</hh.sequence>"
                                 x*
                                 (expr->hiphop expr e)
                                 (redex-term->hiphop/env p e*))]
    [`(:= ,x ,expr)      (format "<hh.atom apply=${function () {~a = ~a;}}/>"
                                 (lookup-var x e)
                                 (expr->hiphop expr e))]
    [`(if ,x ,p ,q)      (format "<hh.if apply=${function () {return !(~a == 0)}}>~a~a</hh.if>"
                                 (lookup-var x e)
                                 (redex-term->hiphop/env p e)
                                 (redex-term->hiphop/env q e))]))

; expr->hiphop : esterel-e env? -> String
(define (expr->hiphop e env)
  (match e
    [`(+)              "0"]
    [`(+ ,e1 . ,es)    (foldl (λ (y x) (format "~a + ~a"
                                               x
                                               (atom->hiphop y env)))
                              (atom->hiphop e1 env)
                              es)]
    [else              (error 'expr->hiphop "Unknown operator")]))

; atom->hiphop : (or symbol? integer?) env? -> String
(define (atom->hiphop s e)
  (cond
    [(member s (env-sigs e)) (format "this.value.~a" (id->hiphop s))]
    [(symbol? s) (lookup-var s e)]
    [else (format "~a" s)]))

(define (id->hiphop id)
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

(define (hiphop->id id)
  (define elems (rest (string-split (symbol->string id) "_")))
  (string->symbol
   (apply
    string
    (for/list ([e (in-list elems)])
      (cond
        [(string->number e) =>
         (lambda (x) (integer->char x))]
        [(= 1 (string-length e)) (string-ref e 0)]
        [else (error 'hiphop->id "unknown id element ~a in ~a") e id])))))

(module+ test
  (require rackunit)

  (define e expr->hiphop)
  (define env0 (make-env))
  (check-equal? (e `(+) env0)
                "0")
  (check-equal? (e `(+ 4) env0)
                "4")
  (check-equal? (e `(+ a b) env0)
                "V_a + V_b")
  (check-equal? (e `(+ a 5 b) env0)
                "V_a + 5 + V_b")
  (check-equal? (e `(+ a 5 b) (add-sig 'b env0))
                "V_a + 5 + this.value.V_b")

  (define (c term)
    (define-values (result _) (redex-term->hiphop term))
    result)
  (define a string-append)
  (check-equal? (c `nothing)
                "<hh.nothing/>")
  (check-equal? (c `pause)
                "<hh.pause/>")
  (check-equal? (c `(signal A pause))
                "<hh.local V_A><hh.pause/></hh.local>")
  (check-equal? (c `(seq pause nothing))
                "<hh.sequence><hh.pause/><hh.nothing/></hh.sequence>")
  (check-equal? (c `(seq pause (signal A pause)))
                (a "<hh.sequence>"
                     "<hh.pause/>"
                     "<hh.local V_A>"
                       "<hh.pause/>"
                     "</hh.local>"
                   "</hh.sequence>"))
  (check-equal? (c `(signal A (par (emit A) pause)))
                (a "<hh.local V_A>"
                     "<hh.parallel>"
                       "<hh.emit V_A/>"
                       "<hh.pause/>"
                     "</hh.parallel>"
                   "</hh.local>"))
  (check-equal? (c `(loop pause))
                "<hh.loop><hh.pause/></hh.loop>")
  (check-equal? (c `(present A (emit O) (emit B)))
                "<hh.if V_A><hh.emit V_O/><hh.emit V_B/></hh.if>")
  (check-equal? (c `(suspend pause S))
                "<hh.suspend V_S><hh.pause/></hh.suspend>")
  (check-equal? (c `(trap (exit 0)))
                "<hh.trap T1><hh.exit T1/></hh.trap>")
  (check-equal? (c `(trap (trap (exit 0))))
                "<hh.trap T1><hh.trap T2><hh.exit T2/></hh.trap></hh.trap>")
  (check-equal? (c `(trap (trap (exit 1))))
                "<hh.trap T1><hh.trap T2><hh.exit T1/></hh.trap></hh.trap>")
  (check-equal? (c `(loop (seq (par (emit A) pause)
                               (emit O))))
                (a "<hh.loop>"
                     "<hh.sequence>"
                       "<hh.parallel>"
                         "<hh.emit V_A/>"
                         "<hh.pause/>"
                       "</hh.parallel>"
                       "<hh.emit V_O/>"
                     "</hh.sequence>"
                   "</hh.loop>"))
  (check-equal? (c `(shared s := (+ 3) pause))
                "<hh.local V_s=${{initApply: function () {return 3} , combine: function (x,y) { return x + y; } }}><hh.pause/></hh.local>")
  (check-equal? (c `(shared s := (+ 3) (<= s (+ s 1))))
                (a "<hh.local V_s=${{initApply: function () {return 3} , combine: function (x,y) { return x + y; } }}>"
                     "<hh.emit V_s apply=${ function () {return this.value.V_s + 1} }/>"
                   "</hh.local>"))

  (check-equal?
   (redex->hiphop `(ABRO
                      (A B R)
                      (O)
                      (loop (seq (par (emit A) (emit B)) pause))))
   (a hiphop-prologue
      "let prg = <hh.module V_A=${inSig} V_B=${inSig} "
                           "V_R=${inSig} V_O=${outSig}>"
        "<hh.loop>"
          "<hh.sequence>"
            "<hh.parallel>"
              "<hh.emit V_A/>"
              "<hh.emit V_B/>"
            "</hh.parallel>"
            "<hh.pause/>"
          "</hh.sequence>"
        "</hh.loop>"
      "</hh.module>;\n"
      "let machine = new hh.ReactiveMachine(prg, \"ABRO\");\n"))

  (check-equal?
   (redex->hiphop `(VARS
                      ()
                      (O)
                      (var x := (+ 2)
                           (seq (seq (if x nothing (emit O))
                                     pause)
                                (seq (:= x (+ 0))
                                     (if x nothing (emit O)))))))
   (a hiphop-prologue
      "let V_V0;\n"
      "let prg = <hh.module V_O=${outSig}>"
        "<hh.sequence>"
          "<hh.atom apply=${function () {V_V0 = 2;}}/>"
          "<hh.sequence>"
            "<hh.sequence>"
              "<hh.if apply=${function () {return !(V_V0 == 0)}}>"
                "<hh.nothing/>"
                "<hh.emit V_O/>"
              "</hh.if>"
              "<hh.pause/>"
            "</hh.sequence>"
            "<hh.sequence>"
              "<hh.atom apply=${function () {V_V0 = 0;}}/>"
              "<hh.if apply=${function () {return !(V_V0 == 0)}}>"
                "<hh.nothing/>"
                "<hh.emit V_O/>"
              "</hh.if>"
            "</hh.sequence>"
          "</hh.sequence>"
        "</hh.sequence>"
      "</hh.module>;\n"
      "let machine = new hh.ReactiveMachine(prg, \"VARS\");\n"))
)
