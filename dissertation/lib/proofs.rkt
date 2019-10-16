#lang racket
(provide cases state)

(require (for-syntax syntax/parse)
         syntax/parse/define
         redex/reduction-semantics
         redex/pict
         "redex-rewrite.rkt"
         scribble/core
         scribble/decode
         scribble-abbrevs/latex)


(define-language base
  (n m ::= natural)
  (nat mat ::= 0 (Suc nat))
  (x y a b ::= any))

(define-simple-macro (state e)
  (list (exact "\\newline") (es e) (exact "\\newline")))

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
       (~once (~seq #:of/count of (~commit n:nat)))
       (~once (~optional (~and #:induction i))))
      ...
      [#:case p body ...] ...)
     #:fail-when (not (equal? (length (syntax->list #'(p ...)))
                              (syntax-e #'n)))
     (format "Expected ~a cases, found ~a cases"
             (length (syntax->list #'(p ...)))
             (syntax-e #'n))
     #'(render-cases/basic (~? i)
                           lang
                           of
                           (p body ...)
                           ...)]
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
   "\nCases of " (with-paper-rewriters (term->pict lang c)) ":"
   (exact "\\noindent")
   (nested-flow (style "case" '())
                (decode-flow
                 (list (list "[" (symbol->string 'pat) "]")
                       (nested-flow (style "nopar" '(command))
                                     (decode-flow (list body ...))))))
   ...))

(define-syntax render-cases
  (syntax-parser
    [(_ (~optional (~and #:induction i))
        lang:id c:expr (pat:expr body ...) ...)
     #:with desc #`#,(if (attribute i) "Induction on " "Cases of ")
     #'(list
        "\n" (exact "\\noindent")
        desc (with-paper-rewriters (term->pict lang c)) ":"
        (exact "\\noindent")
        (nested-flow (style "casesp" '())
                     (decode-flow
                      (append
                       (list
                        (element "item" '())
                        (list (with-paper-rewriters (term->pict lang c))
                              (es =)
                              (with-paper-rewriters (term->pict lang pat)))
                        (nested-flow (style "nopar" '(command))
                                     (decode-flow (list body ...))))
                       ...))))]))
(define-simple-macro (render-cases/basic lang:id of:expr (pat:expr body ...) ...)
  (list
   "\n"
   (exact "\\noindent")
   "Cases of " of ":"
   (exact "\\noindent")
   (nested-flow (style "casesp" '())
                (decode-flow
                 (append
                  (list (element "item" '())
                        pat
                        (nested-flow (style "nopar" '(command))
                                     (decode-flow (list body ...))))
                  ...)))))
   
   