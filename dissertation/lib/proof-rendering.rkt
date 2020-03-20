#lang at-exp racket
(provide
 de
 render
 statement)
(require "proof-extras.rkt"
         "proofs.rkt"
         pict
         "redex-rewrite.rkt"
         (for-syntax syntax/parse)
         (only-in scribble/base linebreak)
         syntax/parse/define)


(begin-for-syntax
  (define-splicing-syntax-class elide
    (pattern
     (~optional (~and elide? #:elide))))
  (define-syntax-class dev
    #:literals (de)
    #:datum-literals (ctx trans step refl sym hole)
    #:attributes (derive render elide? p q)
    [pattern
     (de hole :elide p:expr q:expr)
     #:attr derive
     #'(begin
         (log-disseration-warning "hole in proof")
         (derivation
          (list '≡j (term p) (term q))
          "hole"
          (list)))
     #:attr render
     #'"TODO"]
    [pattern
     (de :elide ctx p:expr q:expr deriv:de-c)
     #:attr derive
     #'(derivation
        (list '≡j (term p) (term q))
        "ctx"
        (list deriv.derive))
     #:attr render
     #'[list
        [linebreak]
        @sequenced[
 @#:step[fst]{@deriv.render}
 @#:step[_]{By @rule["ctx"] and @fst, @hc-append[(es p) (es ≡) (es p)]}]]]
    [pattern
     (de :elide
         trans
         p:expr
         deriv1:de-c r:expr
         deriv2:de-c q:expr)
     #:attr derive
     #'(derivation
        (list '≡j (term p) (term q))
        "trans"
        (list deriv1.derive deriv2.derive))
     #:attr render
     #'[list [linebreak]
        [sequenced
         @#:step[fst]{@deriv1.render}
         @#:step[snd]{@deriv2.render}
         @#:step[lst]{By @rule["trans"], and @fst through @snd, @(hc-append 5 (es p) (es ≡) (es q))}]]]
    [pattern
     (de :elide trans
        p:expr 
        (~seq derivh:de-c h:expr)
        (~seq derivr:de-c r:expr) ...+
        deriv:de-c q:expr)
     #:with in:dev
     #`(de trans
           p
           derivh
           h
           (de trans h (~@ derivr r) ... deriv q)
           q)
     #:attr derive #'in.derive
     #:attr render
     #'[list
        @[linebreak]
        @sequenced[
 @#:step[fst]{@derivh.render}
 @#:step[_]{@derivr.render} ...
 @#:step[lst]{@deriv.render}
 @#:step[_]{By @rule["trans"], and @fst through @lst, @hc-append[(es p) (es ≡) (es q)]}
 ]]]
    
    [pattern
     (de :elide sym
         p:expr
         q:expr
         deriv:de-c)
     #:attr derive
     #'(derivation
        (list '≡j (term p) (term q))
        "sym"
        (list deriv.derive))
     #:attr render
     #'[list
        @[linebreak]
        [sequenced
         @#:step[fst]{@deriv.render}
         @#:step[_]{By @rule["sym"] and @fst, @(hc-append 5 (es p) (es ≡) (es q))}]]]
    
    [pattern
     (de :elide refl p:expr)
     #:attr derive
     #'(derivation
        (list '≡j (term p) (term p))
        "refl")
     #:attr q #'p
     #:attr render
     #'@list{By @rule["refl"], @hc-append[(es p) (es ≡) (es q)]}]
    [pattern
     (de :elide step p:expr q:expr rule-name)
     #:attr derive
     #'(derivation
        (list '≡j (term p) (term q))
        "step"
        (list
         (derivation
          (list '⇀j (term p) (term q) rule-name)
          #f
          empty)))
     #:attr render
     #'@list{By @rule[rule-name], @(hc-append 5 (es p) [es ≡] (es q))}
     ])
  
  (define-syntax-class de-c
    #:attributes (derive render statement)
    [pattern
     d:dev
     #:attr statement #'(hc-append 5 (es d.p) (es ≡) (es d.q))
     #:attr derive
     #`(let ([y d.derive])
         (if (judgment-holds ≡j y)
             y
             #,(syntax/loc this-syntax
                 (error 'de "failed judgment for ~a\n as ~a:\n ~a"
                        (pretty-format 'd #:mode 'write)
                        (pretty-format (term d) #:mode 'write)
                        (pretty-format y #:mode 'write)))))
     #:attr render (if (attribute d.elide?) #'elide-pict #'d.render)]))

(define-syntax de
  (syntax-parser
    [x:de-c #'x.derive]))

(define-simple-macro (statement x:de-c)
  x.statement)

(define-simple-macro (render x:de-c)
  x.render)