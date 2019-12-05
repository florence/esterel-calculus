#lang racket

(require scriblib/footnote pict racket/draw
         scriblib/figure
         (only-in scribble/core style element nested-flow content? block?
                  delayed-element
                  make-paragraph
                  plain)
         scribble/decode
         scribble/latex-properties
         scribble-abbrevs/latex
         redex/reduction-semantics
         redex/pict
         (only-in plot/utils treeof)
         racket/runtime-path
         (only-in scribble/base bold italic)
         (for-syntax syntax/parse
                     racket/list
                     (except-in redex/reduction-semantics judgment-form?)
                     redex/private/term-fn))
(module+ test (require rackunit))

(provide (rename-out [-note note])
         in-footnote?
         Linux-Liberterine-name
         Inconsolata-name
         LatinModernMath-Regular-name
         subtitle-font-adjust
         paper-title-style
         get-the-font-size
         sub-e
         why-do-i-need-this-spacer-thingy?!
         (contract-out
          [format-number (-> natural? string?)])
         with-normal-height
         latex-lit
         definition
         noindent newline
         
         theorem theorem-ref Theorem-ref
         lemma lemma-ref Lemma-ref
         (contract-out
          
          [proof
           (->*
            (#:label string? #:statement (treeof pre-flow?))
            (#:annotations list?
             #:interpretation (treeof pre-flow?)
             #:type (or/c 'lemma 'theorem)
             #:title (or/c #f string?))
            #:rest (treeof pre-flow?)
            (treeof pre-flow?))])
         proof-ref
         Proof-ref
         default-term->pict/checked-attempts
         term->pict/checked)

(define noindent (element "noindent" '()))
(define newline (element "newline" '()))

(define (latex-lit name #:extras [extras empty] . args)
  (element (style name (cons 'exact-chars extras)) args))

(define in-footnote? (make-parameter #f))
(define (get-the-font-size) (if (in-footnote?) 10 13))

(define-syntax-rule
  (-note . args)
  (parameterize ([in-footnote? #t])
    (note . args)))


(define Linux-Liberterine-name "Linux Libertine O")
(define Inconsolata-name "Inconsolata")
(define LatinModernMath-Regular-name "Latin Modern Math")
(define (check-font name)
  (unless (member name (get-face-list))
    (eprintf "expected the font ~a to be installed\n" name)))
(check-font Inconsolata-name)
(check-font Linux-Liberterine-name)
(check-font LatinModernMath-Regular-name)

(define right-figure-sizes '(4 5 6 7 8 9 10 11 15 17 18))

(define (number->tag n)
  (apply
   string
   (for/list ([i (in-string (~a n))])
     (integer->char
      (+ (- (char->integer i) (char->integer #\0))
         (char->integer #\A))))))

(define (mk-rightfigure i wide?)
  (define the-width (if wide? 2.8 2.1))
  (string->bytes/utf-8
   (format (string-append "\\newcommand{\\RightFigure~a~a}[1]"
                          "{\\begin{wrapfigure}[~a]{R}{~ain}"
                          "\\hspace*{-.08in}\\fbox{\\begin{minipage}{~ain}#1\\end{minipage}}"
                          "\\end{wrapfigure}}\n")
           (number->tag i)
           (if wide? "W" "")
           i
           the-width
           the-width)))

(define extra-tex-code
  (apply
   bytes-append
   #"\\usepackage{wrapfig}\n"
   #"\\setlength\\intextsep{0pt}\n"
   #"\\newcommand{\\SubTitleFontAdjust}[1]{\\fontsize{10}{14}\\selectfont{}#1}\n"
   #"\\newcommand{\\TheoremSpacer}[0]{\\hbox to .3in{}}\n"
   #"\\newcommand{\\SubE}[0]{$_{e}$}\n"
   #"\\newcommand{\\Whydoineedthisspacerthingy}{\\hbox to .1in{}}\n"
   #"\\usepackage{amsmath, amsthm}"
   #"\\newtheoremstyle{case}{}{}{}{}{}{:}{ }{}\n"
   #"\\theoremstyle{case}\n"
   #"\\newtheorem{case}{Case}\n"
   #"\\usepackage{enumitem}\n"
   #"\\newlist{casesp}{enumerate}{3}\n"
   #"\\setlist[casesp]{align=left, %% alignment of labels
                 listparindent=\\parindent, %% same indentation as in normal text
                 %parsep=\\parskip, %% same parskip as in normal text
                 font=\\normalfont\\scshape, %% font used for labels
                 %leftmargin=0pt, %% total amount by which text is indented
                 %labelwidth=0pt, %% width of labels (=how much they stick out on the left because align=left)
                 itemindent=12pt,labelsep=12pt, %% space between label and text
%                 topsep=??, %% vertical space above and below list
                 %partopsep=0pt, %% extra vertical space above and below if separate paragraph
%                 itemsep=??, %% vertical space after each item
                 }\n"
   #"\\setlist[casesp,1]{label=Case~\\arabic*:,ref=\\arabic*}\n"
   #"\\setlist[casesp,2]{label=Case~\\thecasespi.\\roman*:,ref=\\thecasespi.\\roman*}\n"
   #"\\setlist[casesp,3]{label=Case~\\thecasespii.\\alph*:,ref=\\thecasespii.\\alph*}\n"
   #"\\let\\degree\\relax\n"
   (append
    (for/list ([i (in-list right-figure-sizes)])
      (mk-rightfigure i #f))
    (for/list ([i (in-list right-figure-sizes)])
      (mk-rightfigure i #t)))))


(define why-do-i-need-this-spacer-thingy?! (element (style "Whydoineedthisspacerthingy" '()) '()))

(define (subtitle-font-adjust . args)
  (element "SubTitleFontAdjust" args))

(provide right-figure)
(define (right-figure #:lines lines #:caption caption #:tag tag
                      #:wide? [wide? #f]
                      . stuff)
  (unless (member lines right-figure-sizes)
    (raise-argument-error 'right-figure (format "an element of ~a" right-figure-sizes)
                          lines))
  (nested-flow (style (format "RightFigure~a~a" (number->tag lines) (if wide? "W" ""))
                      '(command))
               (decode-flow
                (append
                 stuff
                 (list
                  (Figure-target tag)
                  caption)))))

(define-runtime-path style.tex "style.tex")
(define-runtime-path nuthesis.cls "nuthesis.cls")
(define-runtime-path scribble-load.tex "scribble-load.tex")
(define paper-title-style
  (style #f
         (list
          (latex-defaults+replacements    
           (bytes-append
            #"\\documentclass{nuthesis}\n"
            extra-tex-code)
           style.tex
           (list nuthesis.cls)
           (hash "scribble-load-replace.tex"
                 scribble-load.tex)))))

(define sub-e
  (element "SubE" '()))

(define proof-name-table
  (make-hash))
(define proof-type-table
  (make-hash))

(define (definition
          #:notation notation
          #:read-as [read-as #f]
          . def)
  (decode-flow
   (append
    (list (exact "\\vspace{1ex}\n")
          (exact "\\noindent")
          (bold "Definition: "))
    (flatten notation)
    (if read-as
        (list
         (make-paragraph
          plain
          (append
           (list (italic "read as: "))
           (flatten read-as))))
        empty)
    (list (make-paragraph plain def))
    (list (exact "\\vspace{1ex}\n")))))
  

(define (proof #:label label
               #:annotations [annotations empty]
               #:statement statement
               #:interpretation [interp #f]
               #:type [type 'lemma]
               #:title [title #f]
               . the-proof)
  (when (hash-has-key? proof-name-table label)
    (error 'proof "attempted to make two proofs with the label ~a" label))
  (hash-set! proof-name-table label title)
  (hash-set! proof-type-table label type)
  (list
   (wrap-latex-begin-end
    (case type
      [(lemma) "lemma"]
      [(theorem) "theorem"])
    #:followup (and title (string-append "[\\scshape " title "]"))
    (decode-flow
     (list*
      (element (style "label" '(exact-chars)) (list (string-append "p:" label)))
      (decode-flow (list statement)))))
   (if interp
       (nested-flow (style "interpretation" '())
                    (decode-flow (list interp)))
       "")
   (nested-flow (style "proof" '())
                (decode-flow the-proof))))

(define (exact-chars-element styl . strs)
  (match (cons styl strs)
    [(cons (? values) (? pair?))
     (element (style styl '(exact-chars)) strs)]
    [(cons (? values) '())
     (element styl "")]
    [(cons #f (? pair?))
     (element (style #f '(exact-chars)) strs)]))

(define (wrap-latex-begin-end env content #:followup [followup #f])
  (decode-flow
   (list
    (exact-chars-element #f
                         (cond
                           [followup (format "\\begin{~a}~a" env followup)]
                           [else (format "\\begin{~a}" env)]))
    content
    (exact-chars-element #f (format "\\end{~a}" env)))))

(define (proof-ref str)
  (list (proof-type-ref str "lemma~" "theorem~" "undefined theorem~")
        (element (style "ref" '(exact-chars)) (list (string-append "p:" str)))
        (proof-title-ref str)))

(define (Proof-ref str)
  (list (proof-type-ref str "Lemma~" "Theorem~" "Undefined theorem~")
        (element (style "ref" '(exact-chars)) (list (string-append "p:" str)))
        (proof-title-ref str)))

(define (proof-type-ref str l p u)
  (delayed-element
         (lambda _
           (define t (hash-ref proof-type-table str #f))
           (define label
             (case t
               [(lemma) l]
               [(theorem) p]
               [(#f)
                (log-error "undefined theorem: ~a" str)
                u]))
           (element (style "relax" '(exact-chars)) (list label)))
        (lambda () "")
        (lambda () "")))

(define (proof-title-ref str)
  (delayed-element
   (lambda _ (cond
               [(hash-ref proof-name-table str #f)
                =>
                (lambda (x)
                  (element
                   #f
                   (list " "
                         (sc (~a "(" x ")")))))]
               [else (list)]))
   (lambda () "")
   (lambda () "")))
(define (format-number n)
  (apply
   string-append
   (reverse
    (let loop ([chars (reverse (string->list (~a n)))]
               [i 0])
      (cond
        [(null? chars) '()]
        [else (cons (if (and (= (modulo i 3) 2)
                             (pair? (cdr chars)))
                        (~a "," (car chars))
                        (~a (car chars)))
                    (loop (cdr chars)
                          (+ i 1)))])))))

(module+ test
  (check-equal? (format-number 0) "0")
  (check-equal? (format-number 1) "1")
  (check-equal? (format-number 12) "12")
  (check-equal? (format-number 123) "123")
  (check-equal? (format-number 1234) "1,234")
  (check-equal? (format-number 12345) "12,345")
  (check-equal? (format-number 123456) "123,456")
  (check-equal? (format-number 1234567) "1,234,567")
  (check-equal? (format-number 12345678) "12,345,678"))

(define (with-normal-height p)
  (define x (ghost (text "x" Linux-Liberterine-name (get-the-font-size))))
  (inset (refocus (lbl-superimpose x p) x)
         0 0 (- (pict-width p) (pict-width x)) 0))


(define-syntax the-default-term->pict/checked-attempts (box 10))
(define-syntax default-term->pict/checked-attempts
  (syntax-parser
    [(_) #`#,(unbox (syntax-local-value #'the-default-term->pict/checked-attempts))]
    [(_ x:nat)
     (set-box!
      (syntax-local-value #'the-default-term->pict/checked-attempts)
      (syntax-e #'x))
     #'(void)]))

(define-syntax term->pict/checked
  (syntax-parser
    [(_ (~optional (~seq #:attempts attempts:nat)
                   #:defaults
                   ([attempts #`#,(unbox (syntax-local-value #'the-default-term->pict/checked-attempts))]))
        lang:id term:expr)
     #'(begin
         (test-valid-term lang term attempts)
         (term->pict lang term))]))

(define-syntax test-valid-term
  (syntax-parser
    [(_ lang trm at)
     #:with (pats comps) (get-pats #'trm)
     (define forms-to-require
       (let loop ([l #'(lang trm)])
         (syntax-parse l
           [i:id
            (define x (identifier-binding #'i))
            (cond
              [(and (list? x) (not (empty? x))
                    (module-path-index? (first x))
                    (path? (resolved-module-path-name (module-path-index-resolve (third x)))))
               (list
                (syntax-local-introduce
                 (datum->syntax #'i
                                `(only ,(resolved-module-path-name (module-path-index-resolve (third x)))
                                       ,#'i))))]
              [else empty])]
           [(a . b) (append (loop #'a) (loop #'b))]
           [else empty])))
     (cond
       [(and (ormap symbol? (flatten (syntax->datum #'pats)))
             (not (empty? (flatten (syntax->datum #'comps)))))
        (syntax-local-lift-require
         #`(for-meta #,(add1 (syntax-local-phase-level))
                     #,@forms-to-require)
         (syntax-local-introduce
          #`(let-syntax
                ([whatever
                  (lambda (_)
                    #,(quasisyntax/loc this-syntax
                        (redex-check
                         lang
                         pats
                         #,(if (do-judgment? #'trm)
                               #`(void (judgment-holds trm))
                               #`(void (term trm)))
                         #:attempts at
                         #:print? #f))
                    #'(void))])
              (whatever trm))))]
       [else #'(void)])]))

(define-for-syntax (do-judgment? stx)
  (syntax-parse stx
    [(x:id . _)
     (judgment-form? (syntax-local-value #'x (lambda () #f)))]
    [else #f]))
  

(define-for-syntax (get-pats trm)
  (syntax-parse trm
    #:literals (in-hole)
    [in-hole #'(#f '())]
    [x:id #'(x ())]
    [(x:id y ...)
     #:when (or (term-fn? (syntax-local-value #'x (lambda () #f)))
                (judgment-form? (syntax-local-value #'x (lambda () #f)))
                (free-identifier=? #'in-hole #'x))
     #:with ((pat cmp) ...) (map get-pats (syntax->list #'(y ...)))
     #`((pat ...)
        (x cmp ...))]
    [(y ...)
     #:with ((pat cmp) ...) (map get-pats (syntax->list #'(y ...)))
     #'((pat ...) (cmp ...))]
    [else #'(#f ())]))
(define (theorem #:label label . args)
  (list
   (nested-flow
    (style "theorem" '())
    (decode-flow (list* (element (style "relax" '(exact-chars)) '("~"))
                        (element "newline" '())
                        (element (style "label" '(exact-chars)) (list label))
                        args)))
   (element (style #f '(exact-chars))
            (list "\\vspace{-16pt}\n\n"))))

(define (theorem-ref str)
  (list (element (style #f '(exact-chars)) '("theorem~"))
        (element (style "ref" '(exact-chars)) (list str))))

(define (Theorem-ref str)
  (list (element (style #f '(exact-chars)) '("Theorem~"))
        (element (style "ref" '(exact-chars)) (list str))))


(define (lemma #:label label . args)
  (nested-flow
   (style "lemma" '())
   (decode-flow (list* (element (style #f '(exact-chars)) '("~"))
                       (element "newline" '())
                       (element (style "label" '(exact-chars)) (list label))
                       args))))

(define (lemma-ref str)
  (list (element (style "relax" '(exact-chars)) '("lemma~"))
        (element (style "ref" '(exact-chars)) (list str))))

(define (Lemma-ref str)
  (list (element (style "relax" '(exact-chars)) '("Lemma~"))
        (element (style "ref" '(exact-chars)) (list str))))
