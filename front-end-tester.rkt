#lang racket

(require esterel-calculus/front-end
         rackunit
         (for-syntax racket/match
                     syntax/parse
                     racket/syntax))
(provide (all-defined-out)
         (all-from-out esterel-calculus/front-end)
         (all-from-out rackunit))

(define-logger front-end)

(begin-for-syntax
  (define-splicing-syntax-class (reactions m)
    #:datum-literals (=>)
    #:attributes (test-expr)
    (pattern (~and this [(ins:id ...) (~optional =>) #:causality-error])
             #:with test-expr
             (quasisyntax/loc #'this
               (check-exn
                #rx"failed to evaluate"
                (lambda ()
                  #,(quasisyntax/loc #'this
                      (eval-top #,m
                                (begin
                                  (log-front-end-debug (printf "running on ~a\n" '(ins ...)))
                                  '(ins ...))))))))
    (pattern (~var head (reaction-spec m))
             #:attr test-expr #'head.test-clause)
    (pattern (~seq (~var head (reaction-spec m))
                   (~var body (reactions #'head.test-clause)))
             #:attr test-expr #'body.test-expr))
  (define-syntax-class (reaction-spec m)
    #:datum-literals (=>)
    #:attributes (test-clause)
    (pattern [(ins:id ...) (~optional =>) (~and out (outs:id ...))]
             #:attr test-clause
             (quasisyntax/loc #'out
               (let ()
                 (define-values (m* out*)
                   #,(quasisyntax/loc #'out
                       (eval-top #,m
                                 (begin
                                   (log-front-end-debug (printf "running on ~a\n" '(ins ...)))
                                   '(ins ...)))))
                 #,(quasisyntax/loc #'out (#,(quasisyntax/loc #'out check-equal?)
                                           #,(quasisyntax/loc #'out (list->set out*))
                                           #,(quasisyntax/loc #'out (list->set 'out))))
                 m*)))))

(define-syntax test-seq
  (syntax-parser
    #:datum-literals (=>)
    [(_ machine
        (~optional (~and debug?/i #:debug) #:defaults ([debug?/i #'#f]))
        (~var test (reactions #'machine)))
     (define/with-syntax debug? (and (syntax-e #'debug?/i) #t))
     (if (syntax-e #'debug?)
         #'(time test.test-expr)
         #'test.test-expr)]))


(define-namespace-anchor tester-anchor)
(define tester-ns (namespace-anchor->namespace tester-anchor))

(define (eval-front-end-test test-case)
  (parameterize ([current-namespace tester-ns])
    (eval test-case)))
