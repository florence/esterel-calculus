#lang racket
(provide
 (rename-out
  [in:test-->* test-->]
  [in:test-->>* test-->>])
 test-->>∃
 test--/>
 test--?>
 test-->>P
 expect-failures)
(require redex/reduction-semantics
         rackunit
         (for-syntax syntax/parse)
         syntax/parse/define)

(define (default-equiv-set-equal? a b)
  (for/and ([a (in-list a)])
    (for/or ([b (in-list b)])
      ((default-equiv) a b))))
      

(define-syntax in:test-->*
  (syntax-parser
    [(_ R term results ...)
     (syntax/loc this-syntax
       (test--> R term (list results ...)))]))
(define-syntax in:test-->>*
  (syntax-parser
    [(_ R term results ...)
     (syntax/loc this-syntax
       (test-->> R term (list results ...)))]))

(define-check (test--> R term expected)
  (define res (apply-reduction-relation R term))
  (unless (equal? (list->set res)
                  (list->set expected))
    (with-check-info
     (['results res]
      ['expected expected])
     (fail-check "Did not match reductions in one step"))))

(define-check (test-->> R term results ...)
  (define res (apply-reduction-relation* R term))
  (define expected (list results ...))
  (unless (equal? (list->set res)
                  (list->set expected))
    (with-check-info
     (['results res]
      ['expected expected])
     (fail-check "Did not match reductions in many"))))

(define-check (test-->>∃ R term expected)
  (define res (apply-reduction-relation* R term #:all? #t))
  (unless (memf (curry (default-equiv) expected) res)
    (with-check-info
     (['results res]
      ['expected expected])
     (fail-check "could not find term not match reductions in many steps"))))

(define-check (test--/> R term)
  (define res (apply-reduction-relation R term))
  (unless (empty? res)
    (with-check-info
     (['results res])
     (fail-check "could not find term not match reductions in many steps"))))

(define-check (test--?> R term t)
  (define res (apply-reduction-relation R term))
  (if t
      (when (empty? res)
        (fail-check "had no reductions when it should have"))
      (unless (empty? res)
        (with-check-info
         (['results res])
         (fail-check "could not find term not match reductions in many steps")))))

(define-check (test-->>P R term P)
  (define res (apply-reduction-relation* R term))
  (define failed
    (for/list ([r (in-list res)]
               #:unless (P r))
      r))
  (unless (empty? failed)
    (with-check-info
     (['all-results res]
      ['failed failed])
     (fail-check "Some terminal reductions failed property"))))

(define-syntax expect-failures
  (syntax-parser
    [(_ body ...)
     #`(let ()
         (define something-failed? #f)
         (define handle
           (lambda (f)                   
             (with-handlers ([(negate exn:break?)
                              (lambda (_) (set! something-failed? #t))])
               (f))))
         (parameterize ([current-test-case-around handle]
                        [current-check-around handle])
           body ...)
         #,(syntax/loc this-syntax
             (check-true something-failed? "Expected something in this test case to fail")))]))
                         