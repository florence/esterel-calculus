#lang racket

(require esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/instant
         (prefix-in calculus: esterel-calculus/redex/model/calculus)
         (prefix-in standard: esterel-calculus/redex/model/reduction)
         scribble/base
         (except-in pict text)
         redex/pict
         redex/reduction-semantics
         "util.rkt"
         (except-in "proof-extras.rkt" =)
         syntax/parse/define
         (for-syntax syntax/parse)
         racket/lazy-require
         racket/runtime-path
         (rename-in (only-in racket =>)
                    [=> ==>]))
;; load this dynamically so that a rewriter change
;; doesn't require recompiling everything.
(lazy-require
 ["redex-rewrite-dynamic.rkt" (with-paper-rewriters/proc render-op text mf-t def-t render-op/instructions)])


(provide es es/unchecked esblock define/esblock
         with-paper-rewriters
         mf-t
         def-t
         render-op
         rule
         hookup
         retag
         indent
         words bords ;; bords = bold words
         leading-∀
         es/unchecked/dynamic render-op/instructions)

(define (retag p)
  (cond 
    [(compute-tag p)
     ==>
     (lambda (t) (pict+tag p t))]
    [else p]))

(define hookup
  (drop-below-ascent
   (text "⇀" font-name (default-font-size) #:kern? #f)
   2))
  

(define (compute-tag p)
  (cond
    [(and (converted-pict? p)
          (pict+tag? (converted-pict-parent p)))
     (pict+tag-tag (converted-pict-parent p))]
    [else
     (let loop ([v #f]
                [l (pict-children p)])
       (cond
         [(empty? l) v]
         [else
          (define x (compute-tag (child-pict (first l))))
          (define next
            (cond
              [(and x v)
               (string-append v x)]
              [else (or x v)]))
          (loop next (rest l))]))]))
       
(define (rule name)
  (define (t s) (text s font-name (default-font-size)))
  (define (b s) (text (lookup-bold s) (cons 'bold font-name) (default-font-size)))
  (define (sub s) (text (lookup-bold s) (list* 'bold 'subscript font-name) (default-font-size)))
  (define-values (head tail)
    (match (string-split (~a name) "_")
      [(list head tail)
       (values head tail)]
      [_ (values name "")]))
    
  (hbl-append (t "[")
              (b (~a head))
              (sub tail)
              (t "]")))


(define-syntax es
  (syntax-parser
    [(es e)
     (quasisyntax/loc this-syntax
       (retag
        (with-paper-rewriters
         #,(quasisyntax/loc this-syntax
             (term->pict/checked esterel/typeset e)))))]))
(define-syntax-rule
  (es/unchecked e)
  (retag (with-paper-rewriters (term->pict esterel/typeset e))))


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