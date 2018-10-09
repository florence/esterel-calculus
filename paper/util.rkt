#lang racket

(require scriblib/footnote pict racket/draw
         scriblib/figure
         (only-in scribble/core style element nested-flow)
         scribble/decode
         scribble/latex-properties)
(provide (rename-out [-note note])
         in-footnote?
         Linux-Liberterine-name
         Inconsolata-name
         LatinModernMath-Regular-name
         subtitle-font-adjust
         paper-title-style
         get-the-font-size
         theorem theorem-ref Theorem-ref
         sub-e
         why-do-i-need-this-spacer-thingy?!)

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
                          "\\fbox{\\begin{minipage}{~ain}#1\\end{minipage}}"
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

(define paper-title-style (style #f (list (tex-addition extra-tex-code))))

(define (theorem #:label label #:break? [break? #f] . args)
  (nested-flow (style "theorem" '())
               (cond
                 [break?
                  (decode-flow (list* (element (style "relax" '(exact-chars)) '("~"))
                                      (element "newline" '())
                                      (element "TheoremSpacer" '())
                                      (element (style "label" '(exact-chars)) (list label))
                                      args))]
                 [else (decode-flow args)])))

(define sub-e
  (element "SubE" '()))

(define (theorem-ref str)
  (list (element (style "relax" '(exact-chars)) '("theorem~"))
        (element (style "ref" '(exact-chars)) (list str))))

(define (Theorem-ref str)
  (list (element (style "relax" '(exact-chars)) '("Theorem~"))
        (element (style "ref" '(exact-chars)) (list str))))
