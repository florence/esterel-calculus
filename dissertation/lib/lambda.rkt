#lang at-exp racket
(provide (all-defined-out))
(require redex/reduction-semantics
         redex/pict
         pict
         esterel-calculus/redex/model/shared
         (for-syntax syntax/parse)
         ppict/pict
         "util.rkt"
         esterel-calculus/redex/model/lset
         esterel-calculus/dissertation/lib/redex-rewrite)


(define-syntax lam
  (syntax-parser
    [(_ e)
     #`(retag
        (with-paper-rewriters
        #,(quasisyntax/loc this-syntax
            (term->pict/checked λ_σ e))))]))



(define-syntax lam/unchecked
  (syntax-parser
    [(_ e (~optional (~seq #:rewriters rewriters) #:defaults ([rewriters #'with-paper-rewriters])))
     #`(retag
        (rewriters
        #,(quasisyntax/loc this-syntax
            (term->pict λ_σ e))))]))

(define-language λ_v
  (p q r ::= e)
  (e ::=
     x
     (λ x e)
     (e e ...)
     const)
  (E ::=
     hole
     (v ... E e ...))
  (v ::= (λ x e) const)
  (c ::= number)
  (x ::= variable-not-otherwise-mentioned)
  (C ::=
     hole
     (e ... C e ...)
     (λ x C))
  #:binding-forms
  (λ x e #:refers-to x))
(define-extended-language λ_σ λ_v
  
  (e ::= ....
     (ρ1 θ e)
     (set! x e))
  (E ::= .... (set! x E))
  (θ ::= · ((x v) θ)))

(define-extended-language λ_σ2 λ_v
  
  (e ::= ....
     (ρ1 θ e)
     (set! x e))
  (E ::=
     hole
     (v ... E e ...)
     (set! x E))
  (θ ::= · ((x v) θ)))

(define-judgment-form λ_v
  #:mode (≡λ I I)
  [(⇀λ2 e_i e_o)
   ----------- step
   (≡λ e_i e_o)]
  [----------- refl
   (≡λ e e)]
  [(≡λ e_1 e_2)
   (where/hidden C hole)
   ----------- ctx
   (≡λ (in-hole C e_1) (in-hole C e_2))]
  [(where/hidden e 1)
   (≡λ e_1 e) (≡λ e e_2) 
   ----------- trans
   (≡λ e_1 e_2)]
  [(≡λ e_2 e_1)
   ----------- sym
   (≡λ e_1 e_2)])

(define-judgment-form λ_σ
  #:mode (≡σ I I)
  [(⇀σ e_i e_o)
   ----------- step
   (≡σ e_i e_o)]
  [----------- refl
   (≡σ e e)]
  [(≡σ e_1 e_2)
   (where/hidden C hole)
   ----------- ctx
   (≡σ (in-hole C e_1) (in-hole C e_2))]
  [(where/hidden e 1)
   (≡σ e_1 e) (≡σ e e_2) 
   ----------- trans
   (≡σ e_1 e_2)]
  [(≡σ e_2 e_1)
   ----------- sym
   (≡σ e_1 e_2)])

(define-judgment-form λ_v
  #:mode (⇀λ2 I O)
  [------------------- β_v
   (⇀λ2 ((λ x e) v) (subst e x v))]
  [------------------- δ
   (⇀λ2 (const v ...) (δ* const v ...))])

(define ⇀λ
  (reduction-relation
   λ_v 
   (--> ((λ x e) v) (subst e x v) β_v)
   (--> (const v ...) (δ* const v ...) δ)))

(define ⇀α
  (reduction-relation
   λ_v
   (--> (λ x e) (λ x_2 (subst e x x_2))
        (where/hidden x_2 z) 
        (judgment-holds (L¬∈ x_2 (FV e)))
        α)))

(define-metafunction λ_σ
  mtθ+x : x v -> θ
  [(mtθ+x x v) ((x v) ·)])

(define-judgment-form λ_σ
  #:mode (⇀σ I I)
  [(where (_ .... e_2 _ ...)
          ,(apply-reduction-relation ⇀s (term e_1)))
   ----
   (⇀σ e_1 e_2)])


(define ⇀s
  (reduction-relation
   λ_σ
   (--> ((λ x e) v) (ρ (mtθ+x x v) e) β_σ)
   (--> (ρ1 θ (in-hole E (set! x v))) (ρ1 (<- θ (mtθ+x x v)) (in-hole E 42))
        (judgment-holds (L∈dom x θ))
        σ)
   (--> (ρ1 θ (in-hole E x)) (ρ θ (in-hole E (θ-ref θ x)))
        (judgment-holds (L∈dom x θ))
        D)
   (--> (ρ1 θ_1 (in-hole E (ρ θ_2 e))) (ρ1 (parens (<- θ_1 θ_2)) (in-hole E e))
        lift)
   (--> (const v ...) (δ* const v ...) δ)))

(define ⇁2
  (reduction-relation
   λ_v
   #:arrow ==>
   (==> (in-hole E ((λ x e) v))
        (in-hole E (subst e x v)))
   (==> (in-hole E (const v ...))
        (in-hole E (δ* const v ...)))))


(define-metafunction λ_v
  name-of-function : e ... -> e)

(rule-pict-style 'horizontal)

(define-metafunction λ_v
  subst : e x e -> e) 

(define-judgment-form λ_v
  #:mode (⇁* I O)
  [---- (⇁* a b)])

(define-metafunction λ_v
  evalλ : e -> const or procedure
  [(evalλ e) const
   (judgment-holds (≡λ e const))]
  [(evalλ e) procedure
   (judgment-holds (≡λ e (λ x e_1)))])

(define-metafunction λ_v
  EVAL : e e -> c or procedure
  [(EVAL e) const
   (judgment-holds (⇁* e const))]
  [(EVAL e) procedure
   (judgment-holds (⇁* e (λ x e_1)))])
  
     
     



(define (derivation-steps r)
  (match-define (derivation term name subs) r)
  (add1 (for/sum ([r (in-list subs)]) (derivation-steps r))))
  
(define (render-derivation* r [me 0])
  (match-define (derivation term name subs) r)
  (cond
    [(pict? term) term]
    [else 
     (define t (inset (with-paper-rewriters (render-term/pretty-write λ_v term)) 0 0 0 0))
     (define child
       (apply hbl-append 10
              (for/fold ([c empty]
                         [o 1]
                         #:result (reverse c))
                        ([r (in-list subs)])
                (values (cons (render-derivation* r (+ o me)) c)
                        (+ o (derivation-steps r))))))
     (define line-width (max (pict-width t) (pict-width child)))
     (define nam
       (cond
         [name (rule name)]
         [else (blank)]))
     (inset
      (vc-append
       child
       (inset (hc-append (hline line-width 5) nam) 0 0 (- (pict-width nam)) 0)
       t)
      0 0 (pict-width nam) 0)]))


(define one* (derivation '(≡ (+ 1 1) 2)
                         "step"
                         (list (derivation '(⇀ (+ 1 1) 2) "δ" empty))))
(define eq1
  (render-derivation* one*))
(define one (derivation (text "<1+1≡2>"'(bold)) #f empty))
(define two-a (derivation (quote (≡ (+ (+ 1 1) (+ 1 1)) (+ 2 (+ 1 1))))
                          "ctx"
                          (list one)))
(define two-b (derivation '(≡ (+ 2 (+ 1 1)) (+ 2 2))
                          "ctx"
                          (list one)))
(define two (derivation '(≡ (+ (+ 1 1) (+ 1 1)) (+ 2 2))
                        "trans"
                        (list two-a two-b)))
(define three (derivation (quote (≡ ((λ x (+ x x)) 2) (+ 2 2)))
                          "step"
                          (list (derivation (quote (⇀ ((λ x (+ x x)) 2) (+ 2 2)))
                                            "β_v"
                                            empty))))
(define four (derivation (quote (≡ (+ 2 2) ((λ x (+ x x)) 2)))
                         "sym"
                         (list three)))
(define five (derivation (quote (≡ ((λ x (+ x x)) 2) ((λ x (+ x x)) (+ 1 1))))
                         "ctx"
                         (list 
                          (derivation (quote (≡ 2 (+ 1 1)))
                                      "sym"
                                      (list one)))))
(define partd (render-derivation* two-b))
(define big-deriv-part-1
  (render-derivation*
   (derivation '(≡ (+ (+ 1 1) (+ 1 1)) (+ 2 2))
               "trans"
               (list two-a
                     (derivation (text "<part d>"'(bold)) #f empty)))))
(define partc (render-derivation* five))
(define big-deriv-part-2
  (render-derivation*
   (derivation '(≡ (+ 2 2) ((λ x (+ x x)) (+ 1 1)))
               "trans"
               (list four (derivation (text "<part c>"'(bold)) #f empty)))))

(define big-deriv-part-3
  (render-derivation*
   (derivation
    (quote (≡ (+ (+ 1 1) (+ 1 1)) ((λ x (+ x x)) (+ 1 1))))
    "trans"
    (list
     (derivation (text "<part a>"'(bold)) #f empty)
     (derivation (text "<part b>"'(bold)) #f empty)))))
(define (enframe p) (frame (inset p 5)))
(define big-deriv
  (let ()
    (define line-width
      (apply max
             (map pict-width
                  (list
                   (hb-append eq1 partd)
                   big-deriv-part-1
                   partc
                   big-deriv-part-2
                   big-deriv-part-3))))
    (define line (hline line-width 10))
    (define spaces (blank line-width 0))
    (vc-append
     10
     (hb-append
      20
      (vl-append
       (text "<1+1≡2> :=" '(bold))
       (enframe eq1))
      (vl-append
       (text "<part d> :=" '(bold))
       (enframe partd)))
     (vl-append
      (text "<part c> :=" '(bold))
      spaces)
     (enframe partc)
     (vl-append
      (text "<part a> :=" '(bold))
      spaces)
     (enframe big-deriv-part-1)
     (vl-append
      (text "<part b> :=" '(bold))
      spaces)
     (enframe big-deriv-part-2)
     big-deriv-part-3)))