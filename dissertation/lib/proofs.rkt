#lang racket
(provide cases state sequenced base)

(require (for-syntax syntax/parse
                     redex/private/term-fn
                     racket/list
                     racket/stxparam-exptime
                     racket/format)
         (only-in redex/private/struct
                  metafunc-proc-cases)
         (only-in redex/private/reduction-semantics
                  metafunction
                  metafunction-proc)
         racket/stxparam
         syntax/parse/define
         redex/reduction-semantics
         redex/pict
         pict
         "redex-rewrite.rkt"
         (only-in "util.rkt" lift-to-compile-time-for-effect! render-case-body
                  term->pict/checked
                  wrap-latex-begin-end
                  exact-chars-element)
         esterel-calculus/redex/model/shared
         syntax/location
         (except-in scribble/core table)
         scribble/decode
         scribble-abbrevs/latex
         (only-in scribble/base item itemlist))


(define-language base
  (n m ::= natural)
  (nat mat ::= 0 (Suc nat))
  (x y a b ::= any))

(define-simple-macro (state e)
  (list (exact "\\newline") (es e) (exact "\\newline")))

(define-syntax derive
  (syntax-parser
    [(_ e)
     #'(with-paper-rewriters
        (let ()
          (define devs (build-derivations e))
          (if (empty? devs)
              (text "no derivations")
              (render-derivation (first devs)))))]))

(define (render-derivation r)
  (match-define (derivation term name subs) r)
  (define t (render-term/pretty-write esterel-eval term))
  (define child (apply hbl-append 10 (map render-derivation subs)))
  (define line-width (max (pict-width t) (pict-width child)))
  (define nam (if name (text (string-append " [" name "]")) (blank)))
  (inset
   (vc-append
    child
    (inset (hc-append (hline line-width 5) nam) 0 0 (- (pict-width nam)) 0)
    t)
   0 0 (pict-width nam) 0))


(define-for-syntax (do-judgment? stx)
  (syntax-parse stx
    [(x:id _ ...)
     (judgment-form? (syntax-local-value #'x (lambda () #f)))]
    [x:id
     (judgment-form? (syntax-local-value #'x (lambda () #f)))]
    [else #f]))

(define-for-syntax (do-mf? stx)
  (syntax-parse stx
    [(x:id _ ...)
     (term-fn? (syntax-local-value #'x (lambda () #f)))]
    [x:id
     (term-fn? (syntax-local-value #'x (lambda () #f)))]
    [else #f]))

(define-syntax dj?
  (lambda (stx)
    (datum->syntax stx (do-judgment? stx))))

(define-syntax-parameter in-sequence #f)

(define-syntax sequenced
  (syntax-parser
    [(_ _:string ... (~seq (~and cloc (#:step n:id body:expr ...)) _:string ...) ...)
     #:with prefix
     (if (syntax-parameter-value #'in-sequence)
         (~a (syntax-parameter-value #'in-sequence) ".")
         "")
     #:with (c ...)
     (for/list ([x (in-list (syntax->list #'(n ...)))]
                [i (in-naturals 1)])
       #`(~a 'prefix '#,i))
     #`(match-let ([n (~a "(" c ")")] ...)
         (wrap-latex-begin-end
          "enumerate"
          #:followup "[label*=\\arabic*.]"
          (append
           (list
            (exact-chars-element #f "\\item")
            (syntax-parameterize ([in-sequence c]) 
              (nested-flow (style "nopar" '(command))
                           (render-case-body (quote-srcloc-string cloc) (list body ...)))))
           ...)))]))

(define-for-syntax basic-subcases
  (lambda (stx)
    (raise-syntax-error 'subcases
                        "No subcases remaining"
                        stx)))
(define-syntax-parameter subcases basic-subcases)

(define-for-syntax (make-subcases-expander ps fst? lang checks)
  (with-syntax ([(pst ...) ps]
                [box box]
                [lang lang])
    #`(syntax-parser
        [(...
          (_ (~seq [#:case (pat:expr ...) body ...] _:string ...) ...))
         #:when
         (...
          (for/and ([l1 (in-list (syntax->list #'((pat ...) ...)))])
            (equal? (length (syntax->list (first (syntax->list #'((pat ...) ...)))))
                    (length (syntax->list l1)))))
         #:do
         [(define nl (- (length (syntax->list #'(pst ...)))
                        (length (syntax->list (first (syntax->list (... #'((pat ...) ...))))))))
          (define-values (now later)
            (split-at (syntax->list #'(pst ...))
                      (- (length (syntax->list #'(pst ...)))
                         nl)))]
         #:with new-sc
         (cond
           [(< nl 0) (raise-syntax-error 'subcases "too many patterns" this-syntax)]
           [(zero? nl)
            #'basic-subcases]
           [(> nl 0)
            (make-subcases-expander later
                                    #f
                                    #'lang
                                    #'checks)])
         #:with (... (n ...)) now
         #:with (... ((prot ...) ...))
         (apply map list
                (map syntax->list (syntax->list #'(... ((pat ...) ...)))))
         #:with ps (pst ...)
               
         #`(...
            (syntax-parameterize ([subcases new-sc])
              #,(syntax-loc this-syntax (begin (test-cases-covered #:checks #,checks lang n (prot ...)) ...))
              (render-cases #,@(if fst? #'(#:lexicographic ps) #'(#:lexicographic-sub (... (n ...))))
                            lang
                            (n ...)
                            ((pat ...) body ...) ...)))])))


(define-for-syntax (cases+loc cc)
  (for/list ([c (in-list (syntax->list cc))])
    (syntax-parse c
      [(#:case p body ...)
       (syntax/loc c (p body ...))])))
            

(define-syntax cases
  (syntax-parser
    [(_
      (~alt
       (~once
        (~optional
         (~seq #:language lang:id)
         #:defaults ([lang #'base])))
       (~once (~seq #:of c:expr))
       (~once (~optional
               (~seq #:drawn-from d:expr)))
       (~once (~optional (~and #:induction i)))
       (~once (~optional (~and #:tuplize t)))
       (~once (~optional (~seq #:checks n)
                         #:defaults ([n #'1000]))))
      ...
      _:string ... 
      (~seq (~and cc [#:case p:expr body ...]) _:string ...) ...)
     #:with (cases ...)
     (cases+loc #'(cc ...))
     #`(begin
         #,(syntax/loc this-syntax (test-cases-covered #:checks n lang (~? d c) (p ...)))
         (render-cases (~? i) (~? t) lang c cases ...))]
     
    [(_
      (~alt
       (~once
        (~optional
         (~seq #:language lang:id)
         #:defaults ([lang #'base])))
       (~once (~seq #:of (c:expr ...)))
       (~once #:lexicographic)
       (~once (~optional (~seq #:checks n)
                         #:defaults ([n #'1000]))))
      ...
      _:string ... 
      (~seq [#:case (p:expr ...) body ...]  _:string ...) ...)
     
     #:with sc (make-subcases-expander  #'(c ...) #t #'lang #'n)
     #'(syntax-parameterize ([subcases sc])
         (subcases [#:case (p ...) body ...] ...))]
    [(_
      (~alt
       (~once
        (~optional
         (~seq #:language lang:id)
         #:defaults ([lang #'base])))
       (~once (~seq #:of/count of:expr n:nat))
       (~once (~optional (~and #:induction i)))
       (~once (~optional (~and #:no-check nc)))
       (~once (~optional (~and #:tuplize t)))
       (~once (~optional (~and #:simple-cases s))))
      ...
      _:string ... 
      (~seq (~and cc [#:case p body ...]) _:string ...) ...)
     #:fail-when (not (equal? (length (syntax->list #'(p ...)))
                              (syntax-e #'n)))
     (format "Expected ~a cases, found ~a cases"
             (length (syntax->list #'(p ...)))
             (syntax-e #'n))
     #:with (cases ...)
     (cases+loc #'(cc ...))
     #`(render-cases (~? i)
                     (~? s)
                     (~? t)
                     #:just-render
                     #,@(if (attribute nc) #'() #'(#:do-check))
                     lang
                     of
                     cases ...)]
    [(_
      (~alt
       (~once
        (~optional
         (~seq #:language lang:id)
         #:defaults ([lang #'base])))
       (~once (~seq #:of/unchecked of))
       (~once (~optional (~and #:induction i)))
       (~once (~optional (~and #:simple-cases s))))
      ...
      _:string ... 
      (~seq (~and cc [#:case p body ...]) _:string ...) ...)
     #:with (cases ...)
     (cases+loc #'(cc ...))
     #'(render-cases (~? i)
                     (~? s)
                     lang
                     of
                     cases ...)]))

(define-syntax test-cases-covered
  (syntax-parser
    [(test-cases-covered #:checks n lang:id (mf _ ...) p)
     #:when (do-mf? #'mf)
     #:fail-unless
     (andmap (lambda (x) (eq? (syntax-e x) '_))
             (syntax->list #'p))
     "Expected only `_` for patterns when checking a metafunction"
     #`(lift-to-compile-time-for-effect!
        #,(syntax/loc this-syntax
            (unless
                (equal? (length 'p)
                        (length (metafunc-proc-cases (metafunction-proc (metafunction mf)))))
              (error 'cases
                     '"wrong number of cases for metafunction ~a. Expected ~a got ~a."
                     'mf
                     (length (metafunc-proc-cases (metafunction-proc (metafunction mf))))
                     (length 'p)))))]
    [(test-cases-covered #:checks n lang:id (j _ ...) p)
     #:when (do-judgment? #'j)
     #:with (~and ~! (names ...)) (judgment-form-rule-names (syntax-local-value #'j))
     #:with (clause:id ...) #'p
     #:fail-unless (andmap values (syntax->list #'(names ...)))
     "Cannot check cases for a judgment form where some cases are not named"
     #`(lift-to-compile-time-for-effect!
        #,(syntax/loc this-syntax
            (unless (equal? (set (~a 'clause) ...)
                            (set 'names ...))
              (error 'cases
                     '"missing or unexpected case. Expected ~a, got ~a"
                     (map string->symbol '(names ...))
                     '(clause ...)))))]
    [(test-cases-covered #:checks n lang:id c:expr (pat:expr ...))
     #:when (and (not (do-mf? #'c)) (not (do-judgment? #'c)))
     #`(lift-to-compile-time-for-effect!
        #,(syntax/loc this-syntax
            (redex-check
             lang c
             (unless (or (redex-match? lang pat (term c)) ...)
               (error "missing case!"))
             #:attempts 'n
             #:print? '#f)))]))

(define (tuplize . p)
  (if (= 1 (length p))
      (first p)
      (apply hbl-append
             (with-paper-rewriters (text "⟨" (default-style) (default-font-size)))
             (append
              (add-between (map (lambda (x)
                                  (if (string? x)
                                      (text x (default-style) (default-font-size))
                                      x))
                                p)
                           (text ", " (default-style) (default-font-size)))
              (list (with-paper-rewriters (with-paper-rewriters (text "⟩" (default-style) (default-font-size)))))))))

(define-syntax cfst
  (syntax-parser
    [(x:id _ ...)
     #''x]))
(define-syntax render-cases
  (syntax-parser
    [(_ (~and l (~or (~and #:lexicographic) #:lexicographic-sub))
        (all:expr ...)
        lang:id (c:expr ...) (~and clause-loc ((pat:expr ...) body ...)) ...)
     #:with desc #`#,(if (equal? (syntax-e #'l) '#:lexicographic)
                         "Lexicographic Induction over " "Cases of ")
     #:with (item-label ...)
     #'((list
         (tuplize
          (if (dj? c)
              (~a "[" (~a (cfst c) "]"))
              (with-paper-rewriters (term->pict lang c)))
          ...)
         (es =)
         (tuplize (with-paper-rewriters (term->pict lang pat)) ...))
        ...)
     #`(list
        "\n" (exact "\\noindent")
        desc (tuplize (with-paper-rewriters (term->pict lang all)) ...) ":"
        (exact "\\noindent")
        (nested-flow (style "casesp" '())
                     (decode-flow
                      (append
                       (list
                        (element "item" '())
                        item-label
                        (nested-flow (style "nopar" '(command))
                                     (render-case-body (quote-srcloc-string clause-loc) (list body ...))))
                       ...))))]
    [(_ (~optional (~and #:induction i))
        (~optional (~and #:simple-cases s))
        (~optional (~and #:tuplize t))
        (~optional (~and #:just-render j))
        (~optional (~and #:do-check chk))
        lang:id c:expr (~and cloc (pat:expr body ...)) ...)
     #:with desc
     #`#,(string-append
          (if (attribute i) "Induction on " "Cases of ")
          (if (and (not (attribute j)) (do-mf? #'c))
              "the clauses of "
              ""))
     #:with tz (if (attribute t) #'tuplize #'values)
     #:with ((pat1 ...) ...)
     (if (attribute t) #'(pat ...) #'((pat) ...))
     #:with (c1 ...)
     (if (attribute t) #'c #'(c))
     #:with trm->
     (if (attribute chk) #'term->pict/checked #'term->pict)
     #:with (item-label ...)
     (cond
       [(attribute s)
        #'((tz (with-paper-rewriters (trm-> lang pat1)) ...) ...)]
       [(and (not (attribute j)) (not (attribute t)) (do-mf? #'c))
        (for/list ([_ (in-list (syntax->list #'(pat ...)))])
          #'"")]
       [(and (not (attribute j)) (not (attribute t)) (do-judgment? #'c))
        #'((with-paper-rewriters (text (~a "[" (~a 'pat) "]") (default-style) (default-font-size))) ...)]
       [else #'((list (tz (with-paper-rewriters (term->pict lang c1)) ...)
                      (es =)
                      (tz (with-paper-rewriters (trm-> lang pat1)) ...))
                ...)])
         
     
     #'(list
        "\n" (exact "\\noindent")
        desc (tz (with-paper-rewriters (trm-> lang c1)) ...) ":"
        (exact "\\noindent")
        (nested-flow (style "casesp" '())
                     (decode-flow
                      (append
                       (list
                        (element "item" '())
                        item-label
                        (nested-flow (style "nopar" '(command))
                                     (render-case-body (quote-srcloc-string cloc) (list body ...))))
                       ...))))]))