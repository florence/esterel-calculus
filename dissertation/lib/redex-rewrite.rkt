#lang racket

(require esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/instant
         esterel-calculus/redex/model/eval
         (prefix-in calculus: esterel-calculus/redex/model/calculus)
         (prefix-in standard: esterel-calculus/redex/model/reduction)
         scribble/base
         pict
         redex/pict
         redex/reduction-semantics
         "util.rkt"
         (except-in "proof-extras.rkt" =)
         syntax/parse/define
         (for-syntax syntax/parse)
         racket/lazy-require)
;; load this dynamically so that a rewriter change
;; doesn't require recompiling everything.
(lazy-require
 ["redex-rewrite-dynamic.rkt" (with-paper-rewriters/proc)])

(define current-reduction-arrow (make-parameter 'calculus))
(define (reduction-arrow)
  (match (current-reduction-arrow)
    ['calculus
     (drop-below-ascent (text "⇀" Linux-Liberterine-name (default-font-size)) 2)]
    ['standard-reduction
     (drop-below-ascent (text "⇁" Linux-Liberterine-name (default-font-size)) 2)]))

(set-arrow-pict! '--> reduction-arrow)

;; es short for esterel, in the spirit of @racket[]
(provide es es/unchecked esblock define/esblock
         with-paper-rewriters
         (contract-out
          [rule (-> is-rule-label? pict?)])
         current-reduction-arrow
         indent
         words bords ;; bords = bold words
         leading-∀
         es/unchecked/dynamic)

(define (rule name)
  (define (t s) (text s Linux-Liberterine-name))
  (define (b s) (text s (cons 'bold Linux-Liberterine-name)))
  (hbl-append (t "[") (b (~a name)) (t "]")))

(define is-rule-label?
  (let ([rule-names (apply set
                           (append (reduction-relation->rule-names calculus:R)
                                   (reduction-relation->rule-names standard:R)))])
    (λ (x)
      (cond
        [(symbol? x) (set-member? rule-names x)]
        [(string? x) (set-member? rule-names (string->symbol x))]
        [else #f]))))

(define-syntax es
  (syntax-parser
    [(es e)
     (quasisyntax/loc this-syntax
       (with-paper-rewriters (term->pict/checked esterel/typeset e)))]))
(define-syntax-rule
  (es/unchecked e)
  (with-paper-rewriters (term->pict esterel/typeset e)))
(define-syntax es/unchecked/dynamic
  (syntax-parser
    [(es/unchecked/dynamic e)
     #`(es/unchecked #,(datum->syntax #'e (syntax->datum #'e)))]))
(define-syntax (esblock stx)
  (syntax-parse stx
    [(_ e:expr #:run-instants input-env-vss final-program output-signals)
     (with-syntax ([source (syntax-source stx)]
                   [line (syntax-line stx)])
       #'(begin0 (esblock e)
                 (check-it-reduces 'source line
                                   (term e)
                                   input-env-vss
                                   (redex-match? esterel-eval final-program)
                                   'final-program
                                   output-signals)))]
    [(_ e:expr #:equal? expected)
     (with-syntax ([source (syntax-source stx)]
                   [line (syntax-line stx)])
       #'(begin0 (esblock e)
                 (check-equality 'source line (term e) (term expected))))]
    [(_ e:expr ...)
     #'(centered (with-paper-rewriters (vl-append 4 (term->pict esterel-eval e) ...)))]))

(define-simple-macro
  (define/esblock term-x:id block-x:id e)
  (begin
    (define block-x (esblock e))
    (define term-x (term e))))

(define (check-equality source line actual expected)
  (unless (equal? actual expected)
    (error 'esblock
           "~a:~a: expected and actual results differ:\n  expected ~s\n    actual ~s"
           source line expected actual)))

(define p? (redex-match? esterel-eval p))
(define (check-it-reduces source line p input-env-vss
                          final-program-ok? final-program-pattern
                          expected-present-signals)
  (define-values (final-p actual-present-signals) (run-instants p input-env-vss))
  (unless (final-program-ok? final-p)
    (error 'esblock
           "~a:~a: final-p does not match\n expected ~s, got:\n~a"
           source line final-program-pattern
           (pretty-format final-p #:mode 'write)))
  (unless (equal? expected-present-signals actual-present-signals)
    (error 'esblock
           "~a:~a: signals do not line up\n expected ~s\n   actual: ~s"
           source line
           expected-present-signals
           actual-present-signals)))

(define-syntax with-paper-rewriters
  (syntax-parser
    [(_ e1 e ...)
     (quasisyntax/loc this-syntax
       (with-paper-rewriters/proc
        #,(syntax/loc this-syntax (λ () e1 e ...))))]))


(define (words str)
  (text str (default-style) (default-font-size)))

(define (bords str)
  (text str (cons 'bold (default-style)) (default-font-size)))

(define-syntax (with-atomic-rewriters stx)
  (syntax-case stx ()
    [(_ () b ...) #'(let () b ...)]
    [(_ ([x e] . more) b ...) #'(with-atomic-rewriter x e (with-atomic-rewriters more b ...))]))

(define (indent p) (hc-append (blank 10 0) p))

(define (leading-∀) (hbl-append (term->pict esterel-eval ∀) (words " ")))