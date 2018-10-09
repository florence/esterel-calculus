#lang racket

(require esterel-calculus/front-end
         rackunit
         (for-syntax racket/match
                     syntax/parse
                     racket/syntax))
(provide (all-defined-out)
         (all-from-out esterel-calculus/front-end)
         (all-from-out rackunit))

(define-syntax test-seq
  (syntax-parser
    #:datum-literals (=>)
    [(_ machine
        (~optional (~and debug?/i #:debug) #:defaults ([debug?/i #'#f]))
        (ins (~optional =>) outs)
        ...)
     (define/with-syntax debug? (and (syntax-e #'debug?/i) #t))
     (define/with-syntax test
       (let loop ([ins (syntax->list #'(ins ...))]
                  [outs (syntax->list #'(outs ...))]
                  [m #'machine])
         (match* (ins outs)
           [((cons in rin)
             (cons out rout))
            (loop
             rin
             rout
             (quasisyntax/loc out
               (let ()
                 (define-values (m* out*)
                   #,(quasisyntax/loc out
                       (eval-top #,m
                                 (begin
                                   (when debug?
                                     (printf "running on ~a\n" '#,in))
                                   '#,in))))
                 #,(quasisyntax/loc out (#,(quasisyntax/loc out check-equal?)
                                         #,(quasisyntax/loc out (list->set out*))
                                         #,(quasisyntax/loc out (list->set '#,out))))
                 m*)))]
           [(_ _) m])))
     (if (syntax-e #'debug?)
         #'(time test)
         #'test)]))


(define-namespace-anchor tester-anchor)
(define tester-ns (namespace-anchor->namespace tester-anchor))

(define (eval-front-end-test test-case)
  (parameterize ([current-namespace tester-ns])
    (eval test-case)))
