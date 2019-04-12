#lang racket
(require (except-in redex/reduction-semantics
                    test-->
                    test-->>
                    test-->>∃
                    test-judgment-holds
                    test-equal)
         racket/require
         rackunit
         syntax/parse/define
         (for-syntax syntax/parse)
         esterel-calculus/redex/rackunit-adaptor
         esterel-calculus/redex/model/shared
         (multi-in esterel-calculus/redex/model/calculus/variants
                   (base closed-and-control graph))
         (rename-in esterel-calculus/redex/model/reduction
                    [R std->])
         esterel-calculus/redex/test/generator)

(define-simple-macro (list/names n:id ...)
  (list (list n 'n) ...))

(define good (list/names R-no-control
                         R-E
                         R-control-closed
                         R-safe-after-reduction))
(define correct std->)

(define (complete? p)
    (redex-match? esterel-eval complete p))
#;
(parameterize ([current-cache-all? #t])
  (redex-check
   esterel-check
   (p-check (name i ((S_!_g status-check) (S_!_g status-check_1 ...))))
   (let ()
     (define env
       (let loop ([i (term i)])
         (match i
           [empty (term ·)]
           [(cons a r)
            (list a (loop r))])))
     (define p (term (ρ ,env p-check)))
     (define std
       (andmap complete? (apply-reduction-relation* std-> p)))
     (define matching
       (for/list ([l (in-list good)])
         (match l
           [(list r n)
            (list (andmap complete? (apply-reduction-relation* r p))
                  n)])))
     (for/and ([m (in-list matching)])
       (define r (equal? (first m) std))
       (unless r (displayln (second m)))
       r))
   #:prepare fixup))

  



