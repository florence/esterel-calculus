#lang racket
(provide cases)

(require (for-syntax syntax/parse)
         syntax/parse/define
         redex/reduction-semantics
         redex/pict
         "redex-rewrite.rkt"
         scribble/core
         scribble/decode)


(define-language base
  (n m ::= natural)
  (nat mat ::= 0 (Suc nat))
  (x y a b ::= any))

(define-syntax cases
  (syntax-parser
    [(_
      (~alt
       (~once
        (~optional
         (~seq #:language lang:id)
         #:defaults ([lang #'base])))
       (~once (~seq #:of c:expr))
       (~once (~optional (~and #:induction i)))
       (~once (~optional (~seq #:checks n)
                         #:defaults ([n #'1000]))))
      ...
      [#:case p:expr body ...] ...)
     #'(begin
         (test-cases-covered #:checks n lang c (p ...))
         (render-cases (~? i) lang c (p body ...) ...))]
    [(_
      (~alt
       (~once
        (~optional
         (~seq #:language lang:id)
         #:defaults ([lang #'base])))
       (~once (~seq #:of/unchecked of))
       (~once (~optional (~and #:induction i))))
      ...
      [#:case p body ...] ...)
     #'(render-cases/basic (~? i)
                           lang
                           of
                           (p body ...)
                           ...)]))


(define-simple-macro (test-cases-covered #:checks n lang:id c:expr (pat:expr ...))
  (redex-check
   lang c
   (unless (or (redex-match? lang pat (term c)) ...)
     (error "missing case!"))
   #:attempts n
   #:print? #f))

(define-simple-macro (render-cases/derivation lang:id c:expr (pat:id body ...) ...)
  (list
   "Cases of " (with-paper-rewriters (term->pict lang c)) ":\n\n"
   (nested-flow (style "case" '())
                (decode-flow
                 (list (list "[" (symbol->string 'pat) "]")
                       (element "newline" '())
                       body ...))) ...))

(define-syntax render-cases
  (syntax-parser
    [(_ (~optional (~and #:induction i))
        lang:id c:expr (pat:expr body ...) ...)
     #:with desc #`#,(if (attribute i) "Induction on " "Cases of ")
     #'(list
        desc (with-paper-rewriters (term->pict lang c)) ":\n\n"
        (nested-flow (style "casesp" '())
                     (decode-flow
                      (append
                       (list
                        (element "item" '())
                        (list (with-paper-rewriters (term->pict lang c))
                              (es =)
                              (with-paper-rewriters (term->pict lang pat)))
                        (element "newline" '())
                        body ...)
                       ...))))]))
(define-simple-macro (render-cases/basic lang:id of:expr (pat:expr body ...) ...)
  (list
   "Cases of " of ":\n\n"
   (nested-flow (style "casesp" '())
                (decode-flow
                 (append
                  (list (element "item" '())
                        pat
                        (element "newline" '())
                        body ...)
                  ...)))))
   
   