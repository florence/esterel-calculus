#lang racket
(require redex/reduction-semantics
         (for-syntax syntax/parse)
         sexp-diff)
(provide (all-defined-out))
(module+ test (require rackunit))

(define-syntax define/ppl 
 (syntax-parser
   #:literals (propigate/remove*)
   [(_ name propigate/remove* before body ...) 
    #'(begin (define-term name (propigate/remove* before body ...))
             (assert-subset-class (term before) (term name))
             (for-each pretty-write (term name)))]
   [(_ name f:id before body ...) 
    #'(begin (define-term name (f before body ...))
             (assert-same-class (term before) (term name))
             (for-each pretty-write (term name)))]
   [(_ name #:no-check
       body) 
    #'(begin (define-term name body)
             (for-each pretty-write (term name)))]))

(define-language constructive
  (P ::= (e ...))
  (e ::= (a = p))
  (p q ::= (and p q) (or p q) (not p) const a)
  (a b c ::= variable-not-otherwise-mentioned)
  (const ::= true false ⊥)
  (C ::=
     hole
     (and C p)
     (and p C)
     (or C p)
     (or p C)
     (not C)))

(define-language classical
  (P ::= (e ...))
  (e ::= (a = p))
  (p q ::= (and p q) (or p q) (not p) const a)
  (a b c ::= (ann a*) a*)
  (ann ::= + -)
  (a* b* ::= variable-not-otherwise-mentioned)
  (const ::= true false)
  (C ::=
     hole
     (and C p)
     (and p C)
     (or C p)
     (or p C)
     (not C)))
     

(define-union-language both (class: classical) (con: constructive))


(define-metafunction both
  convert-P : con:P -> class:P
  [(convert-P ()) ()]
  [(convert-P (con:e_1 con:e ...))
   (class:e_1 class:e_2 class:e_rest ...)
   (where (class:e_1 class:e_2)
          (convert-e con:e_1))
   (where (class:e_rest ...)
          (convert-P (con:e ...)))])

(define-metafunction both
  convert-e : con:e -> (class:e class:e)
  [(convert-e (con:a = con:p))
   (((+ con:a) = (convert-p + con:p))
    ((- con:a) = (convert-p - con:p)))])

(define-metafunction both
  convert-p : class:ann con:p -> class:p
  [(convert-p + (and con:p con:q))
   (and (convert-p + con:p) (convert-p + con:q))]
  [(convert-p - (and con:p con:q))
   (or (convert-p - con:p) (convert-p - con:q))]
  [(convert-p + (or con:p con:q))
   (or (convert-p + con:p) (convert-p + con:q))]
  [(convert-p - (or con:p con:q))
   (and (convert-p - con:p) (convert-p - con:q))]
  [(convert-p - (not con:p))
   (convert-p + con:p)]
  [(convert-p + (not con:p))
   (convert-p - con:p)]
  [(convert-p class:ann con:a)
   (class:ann con:a)]
  [(convert-p + true)
   true]
  [(convert-p - true)
   false]
  [(convert-p + false)
   false]
  [(convert-p - false)
   true]
  [(convert-p + ⊥)
   false]
  [(convert-p - ⊥)
   false])

(module+ test
  (check-equal?
   (term (convert-P ((a = b))))
   (term (((+ a) = (+ b)) ((- a) = (- b))))))

#|
The COS circuit for:

|#
#;(signal S1
    (present
     S1
     (seq
      (emit S2)
      (present
       S2
       nothing
       (emit S1)))
     nothing))

(define a-circuit
  (term
   ([START = true]
    [present-S1-else = (and (not S1) START)]
    [present-S1-then = (and S1 START)]
    [S2 = present-S1-then]
    [present-S2-then = (and S2 present-S1-then)]
    [present-S2-else = (and (not S2) present-S1-then)]
    [S1 = present-S2-else]
    [present-S2-term = (or present-S2-else present-S2-else)]
    [term = (or present-S1-else
                present-S2-term)])))
(define b-circuit (term (convert-P ,a-circuit)))

(define-metafunction classical
  remove : P a ... -> P
  [(remove P) P]
  [(remove (e_1 ... (a = p) e_2 ...) a b ...)
   (remove (e_1 ... e_2 ...) b ...)])

(define-metafunction classical
  propigate/remove* : P a ... -> P
  [(propigate/remove* P a ...)
   (remove (propigate* P a ...) a ...)])

(define-metafunction classical
  propigate* : P a ... -> P
  [(propigate* P) P]
  [(propigate* P a b ...)
   (propigate* (propigate P a) b ...)])

(define-metafunction classical
  propigate : P a -> P
  [(propigate P a)
   (replace P a (get a P))])

(define-metafunction classical
  get : a P -> p
  [(get a (_ ... (a = p) _ ...))
   p])

(define-metafunction classical
  replace* : P (p p) ... -> P
  [(replace* P) P]
  [(replace* P (q_1 q_2) any_r ...)
   (replace* (replace P q_1 q_2) any_r ...)])

(define-metafunction classical
  replace : P p p -> P
  [(replace ((a = p) ...) q_1 q_2)
   ((a = (replace-p p q_1 q_2)) ...)])
(define-metafunction classical
  replace-p : p p p -> p
  [(replace-p q_1 q_1 q_2)
   q_2]
  [(replace-p (not p)  q_1 q_2)
   (not (replace-p p q_1 q_2))]
  [(replace-p (and p q)  q_1 q_2)
   (and (replace-p p q_1 q_2)
        (replace-p q q_1 q_2))]
  [(replace-p (or p q)  q_1 q_2)
   (or (replace-p p q_1 q_2)
       (replace-p q q_1 q_2))]
  [(replace-p p_other  q_1 q_2)
   p_other])

;                                              
;                                              
;                                              
;                                    ;;;;;     
;    ;;;;;;;                            ;;     
;    ;;                                 ;;     
;    ;;                                 ;;     
;    ;;        ;;     ;;   ;;;;;        ;;     
;    ;;         ;     ;    ;   ;;       ;;     
;    ;;         ;;   ;;         ;;      ;;     
;    ;;;;;;     ;;   ;;         ;;      ;;     
;    ;;          ;   ;      ;;;;;;      ;;     
;    ;;          ;  ;;     ;;   ;;      ;;     
;    ;;          ;; ;     ;;    ;;      ;;     
;    ;;           ; ;     ;;    ;;      ;;     
;    ;;           ;;;      ;;  ;;;      ;;  ;  
;    ;;;;;;;      ;;       ;;;;  ;       ;;;;  
;                                              
;                                              
;                                              
;                                              
;                                              


(define-metafunction constructive
  interp-con : P -> (P ...)
  [(interp-con P)
   (P_1 ... ...)
   (where (((a = const) ...) ...)
          (all-con P))
   (where ((P_1 ...) ...)
          ((eval-con P ((a = const) ...)) ...))])
(define-metafunction classical
  interp-class : P -> (P ...)
  [(interp-class P)
   (P_1 ... ...)
   (where (((a = const) ...) ...)
          (all-class P))
   (where ((P_1 ...) ...)
          ((eval-clas P ((a = const) ...)) ...))])
   
(define-metafunction constructive
  all-con : P -> (((a = const) ...) ...)
  [(all-con ((a = p) ...))
   (get-vals-con
   ,(remove-duplicates
     (remove* (term (a ...))
              (term (b ... ...)))))
   (where ((b ...) ...)
          ((vars p) ...))])

(define-metafunction constructive
  get-vals-con : (a ...) -> (((a = const) ...) ...)
  [(get-vals-con ()) (())]
  [(get-vals-con (a b ...))
   (((a = true) (c = const) ...) ...
    ((a = false) (c = const) ...) ...
    ((a = ⊥) (c = const) ...) ...)
   (where (((c = const) ...) ...)
          (get-vals-con (b ...)))])

(define-metafunction classical
  all-class : P -> (((a = const) ...) ...)
  [(all-class ((a = p) ...))
   (get-vals-class
    ,(sort
      (remove-duplicates
       (remove* (term (a ...))
                (term (b ... ...))))
      a<))
          
   (where ((b ...) ...)
          ((vars p) ...))])

(define (a< x y)
  ((term-match/single
    evalu
    [(a* b*)
     (symbol<? (term a*) (term b*))]
    [((+ a*) (- a*))
     #t]
    [((- a*) (+ a*))
     #f]
    [((ann_1 a*) (ann_2 b*))
     (symbol<? (term a*) (term b*))])
   (list x y)))

(define-metafunction classical
  get-vals-class : (a ...) -> (((a = const) ...) ...)
  ;; expects inputs sorted by `a<`
  [(get-vals-class ()) (())]
  [(get-vals-class ((+ a*) (- a*) b ...))
   ((((+ a*) = false) ((- a*) = false) (c = const) ...) ...
    (((+ a*) = true) ((- a*) = false) (c = const) ...) ...
    (((+ a*) = false) ((- a*) = true) (c = const) ...) ...)
   (where (((c = const) ...) ...)
          (get-vals-class (b ...)))]
  [(get-vals-class (a b ...))
   (((a = true) (c = const) ...) ...
    ((a = false) (c = const) ...) ...)
   (where (((c = const) ...) ...)
          (get-vals-class (b ...)))])

(define-metafunction classical
  vars : p -> (a ...)
  [(vars (and p q))
   (a ... b ...)
   (where (a ...) (vars p))
   (where (b ...) (vars q))]
  [(vars (or p q))
   (a ... b ...)
   (where (a ...) (vars p))
   (where (b ...) (vars q))]
  [(vars (not p)) (vars p)]
  [(vars a) (a)]
  [(vars const) ()])

(define-extended-language evalu classical
  [const ::= .... ⊥]
  [env ::= ((a = const) ...)]
  [E ::=
     (unevalable ... (a = E*) e ...)]
  [unevalable ::=
              (p = const)
              (p = unevalable-p)]
  [unevalable-p ::=
              a
              (or ⊥ unevalable-p)
              (or unevalable-p ⊥)
              (or unevalable-p unevalable-p)
              (and unevalable-p unevalable-p)
              (and ⊥ unevalable-p)
              (and unevalable-p ⊥)
              (not unevalable-p)]
  [v ::= const unevalable-p]
  [E* ::=
      hole
      (and E* p)
      (and v E*)
      (or E* p)
      (or v E*)
      (not E*)])

(define-metafunction evalu
  eval-con : P ((a = const) ...) -> ((unevalable ...) ...)
  [(eval-con P ((a = const) ...))
   ,(apply-reduction-relation* ->b (term (replace* P (a const) ...)))])

(define-metafunction evalu
  eval-clas : P ((a = const) ...) -> ((unevalable ...) ...)
  [(eval-clas P ((a = const) ...))
   ,(apply-reduction-relation* ->b (term (replace* P (a const) ...)))])

(define ->b
  (reduction-relation
   evalu
   #:domain P
   ;; and
   [-->
    (in-hole E (and true p))
    (in-hole E p)
    and-1-left]
   [-->
    (in-hole E (and p true))
    (in-hole E p)
    and-1-right]
   [-->
    (in-hole E (and false p))
    (in-hole E false)
    and-0-left]
   [-->
   (in-hole E (and p false))
    (in-hole E false)
    and-0-right]
   [-->
    (in-hole E (and ⊥ ⊥))
    (in-hole E ⊥)
    and-⊥]
   ;; or
   [-->
    (in-hole E (or true p))
    (in-hole E true)
    or-1-left]
   [-->
    (in-hole E (or p true))
    (in-hole E true)
    or-1-right]
   [-->
    (in-hole E (or false p))
    (in-hole E p)
    or-0-left]
   [-->
    (in-hole E (or p false))
    (in-hole E p)
    or-0-right]
   [-->
    (in-hole E (or ⊥ ⊥))
    (in-hole E ⊥)
    or-⊥]
   ;; not
   [-->
    (in-hole E (not true))
    (in-hole E false)
    not-1]
   [-->
    (in-hole E (not false))
    (in-hole E true)
    not-0]
   [-->
    (in-hole E (not ⊥))
    (in-hole E ⊥)
    not-⊥]
   ;; update-envs
   [-->
    (unevalable ...)
    (replace*
     (unevalable ...)
     (c_1 const_1)
     (c const) ...)
    (where
     ((c_1 = const_1)
      (c = const) ...)
     (consts-of (unevalable ...)))
    (side-condition
     (not
      (equal?
       (term (unevalable ...))
       (term
        (replace*
         (unevalable ...)
         (c_1 const_1)
         (c const) ...)))))
    update-env]))

(define-metafunction evalu
  consts-of : P -> env
  [(consts-of ()) ()]
  [(consts-of ((a = const) (b = p) ...))
   ((a = const) (c = const_1) ...)
   (where ((c = const_1) ...)
          (consts-of ((b = p) ...)))]
  [(consts-of ((a = q) (b = p) ...))
   (consts-of ((b = p) ...))])

(define (assert-subset-class p q)
  (define p*
    (list->set (term (interp-class ,p))))
  (define q*
    (list->set (term (interp-class ,q))))
  (define bad empty)
  (for ([q (in-set q*)])
    (unless
        (for/first ([p (in-set p*)]
                    #:when (subset? (list->set q)
                                    (list->set p)))
          #t)
      (set! bad (cons q bad))))
  (unless (empty? bad)
    (error 'subset-class
           "second class had:\n ~a\nwhich had no corresponding element in:\n ~a"
           (pretty-format bad)
           (pretty-format p*))))
(module+ test
  (check-not-exn
   (λ ()
     (assert-subset-class '((a = c) (c = d)) '((a = d))))))

(define (assert-same-class p q)
  (define p*
    (term (interp-class ,p)))
  (define q*
    (term (interp-class ,q)))
  (unless (equal? (list->set p*) (list->set q*))
    (error 'equal-class
           "the diff:\n ~a"
           (pretty-format (sexp-diff p* q*)))))


(module+ test
  (define (map-conv x)
    (map (lambda (x) (term (convert-P ,x)))
         x))
  (check-equal?
   (list->set (term (interp-con ((a = b)))))
   (set (term ((a = true)))
        (term ((a = false)))
        (term ((a = ⊥)))))
  (check-equal?
   (list->set (term (interp-class ((a = b)))))
   (set (term ((a = true)))
        (term ((a = false)))))
  (check-equal?
   (list->set (term (interp-class (convert-P ((a = b))))))
   (set (term (((+ a) = false) ((- a) = false)))
        (term (((+ a) = true) ((- a) = false)))
        (term (((+ a) = false) ((- a) = true)))))
  (check-equal?
   (apply-reduction-relation*
    ->b
    (term
     ((K0 = (and left (and right both)))
      (right = (or true rem)))))
   (term
    (((K0 = (and left both))
      (right = true)))))
  (test-begin
   (check-equal?
    (list->set (map-conv (term (interp-con ((a = (and true true)))))))
    (list->set (term (interp-class (convert-P ((a = (and true true))))))))
   (let ()
     (define-term s
       ((K0 = (and left (and right both)))
        (left = (or l0 lem))
        (right = (or r0 rem))
        (l0 = GO)
        (lem = (not (or GO false)))
        (rem = (not (or GO sel)))
        (both = (or l0 r0))))
     (check-equal?
      (list->set (map-conv (term (interp-con s))))
      (list->set (term (interp-class (convert-P s))))))
   (redex-check
    constructive
    P
    (equal?
     (list->set (map-conv (term (interp-con P))))
     (list->set (term (interp-class (convert-P P))))))))