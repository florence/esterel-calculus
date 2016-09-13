#lang racket
(provide test-seq)
(require "../front-end.rkt"
         rackunit
         (for-syntax syntax/parse racket/sequence racket/syntax
                     racket/list))
(define-syntax test-seq
  (syntax-parser
    #:datum-literals (=>)
    [(_ machine:expr
        (~seq
         (~optional (~seq #:equivalence ((x:id => n:nat y:id) ...))
                    #:defaults ([(x 1) null]
                                [(n 1) null]
                                [(y 1) null]))
         (~and ops ((ins:id ...) (outs:id ...))) ...))

     (define matching-table
       (apply hash (append-map values (syntax->datum #'((x (n y)) ...)))))
     (define (get-equiv i/o-pair)
       (syntax-parse i/o-pair
         [((x) (a ...))
          (hash-ref matching-table (syntax-e #'x)
                    #f)]
         [else #f]))
     (define-values (p _)
       (for/fold ([prog null] [mach #'machine])
                 ([i/o-pair (in-syntax #'(ops ...))])
         (define/with-syntax ((ins ...) (outs ...)) i/o-pair)
         (define/with-syntax next (generate-temporary))
         (define/with-syntax out (generate-temporary))
         (define nstx
           (cond [(get-equiv i/o-pair) =>
                  (lambda (matching)
                    (define pass
                      #`(let ()
                          (for/fold ([out (set)] [next #,mach])
                                    ([_ (in-range (sub1 #,(car matching)))])
                            (define-values (a b) (eval-top next '#,(cdr matching)))
                            (values (set-union a out) b))))
                    #`(begin
                        (define-values (out next)
                          (let-values ([(out next) #,pass])
                            (define-values (a b) (eval-top next '(#,(cdr matching) ins ...)))
                            (values (set-union a out) b)))
                        #,(quasisyntax/loc i/o-pair
                            (check-equal? out (set  'outs ...)
                                          (~a '#,i/o-pair)))))]
                 [else
                  #`(begin
                      #|
                      (pretty-print '#,i/o-pair)
                      (displayln 'old:)
                      (pretty-print (machine-prog #,mach))
                      |#
                      (define-values (out next) (eval-top #,mach '(ins ...)))
                      #|
                      (displayln 'new:)
                      (pretty-print (machine-prog next))
                      (displayln "\n\n\n")
                      |#
                      #,(quasisyntax/loc i/o-pair
                          (check-equal? out (set 'outs ...)
                                        (~a '#,i/o-pair))))]))
         (values (cons nstx prog) #'next)))
     #`(let () #,@(reverse p))]))
