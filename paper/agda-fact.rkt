#lang racket/base

(require "redex-rewrite.rkt"
         "util.rkt"
         esterel-calculus/cross-tests/calculus-example
         esterel-calculus/redex/model/shared
         esterel-calculus/cross-tests/send-lib
         redex/reduction-semantics redex/pict
         racket/match
         racket/list
         racket/format
         (for-syntax racket/base syntax/parse)
         pict)
(module+ test (require rackunit))

(provide equiv check-the-examples
         var-prem fact-prem hidden-prem
         newline-prem newline-prem-with-indent
         leading-∀
         not-equiv)

(define (⇒-pict)
  (let ([x (ghost (text "xx" (default-style) (default-font-size)))])
    (drop-below-ascent
     (refocus
      (cc-superimpose x (text "⇒" LatinModernMath-Regular-name (default-font-size)))
      x)
     2)))

(struct prem (agda pict))
(struct newline-prem () #:transparent)
(struct newline-prem-with-indent newline-prem (indent) #:transparent)
(define (newline-prem-indent n)
  (cond
    [(newline-prem-with-indent? n)
     (newline-prem-with-indent-indent n)]
    [(newline-prem? n)
     0]))
    

(define-syntax (var-prem stx)
   (syntax-parse stx
     [(_ redex (~optional (~seq #:with-rewriters with-rewriters:id)))
      (with-syntax ([with-rewriters (if (attribute with-rewriters)
                                        #'with-rewriters
                                        #'with-paper-rewriters)])
        #'(prem (var-prem-redex->agda 'redex)
                (with-rewriters (term->pict esterel-eval redex))))]))

(define-syntax (fact-prem stx)
  (syntax-parse stx
    [(_ redex (~optional (~seq #:with-rewriters with-rewriters:id)))
     (with-syntax ([with-rewriters (if (attribute with-rewriters)
                                       #'with-rewriters
                                       #'with-paper-rewriters)])
       #'(prem (fact-prem-redex->agda 'redex)
               (with-rewriters (term->pict esterel-eval redex))))]))

(define (fact-prem-redex->agda exp)
  (let loop ([exp exp])
    (match exp
      [`(∀ ,S ,p)
       (~a "(∀ " S " -> " (loop p) ")")]
      [`(L¬∈ ,S ,set)
       (~a "(Signal.unwrap " S " utility.∉ " (loop set) ")")]
      [`(->S (Can ,p ,env))
       (~a "(Canₛ " (loop p) " " (loop env) ")")]
      [`(mtθ+S ,S ,signal)
       (~a "(Θ SigMap.[ " S " ↦ " signal " ] [] [])")]
      [`(CB ,p)
       (~a "(CB " (loop p) ")")]
      [`(done ,p)
       (~a "(done " (loop p) ")")]
      [`(≡e ,_ ,_ ,_ ,p ,q)
       (~a "(" (loop p) " ≡ₑ " (loop q) " # [])")]
      [`(⇀ ,p ,q)
       (~a "(" (loop p) " ⟶₁ " (loop q) ")")]
      [`(same (FV ,p) ∅)
       (~a "(FVars " (loop p) " Prop.≡  base)")]
      [`(same ,p ,q)
       (~a "(" (loop p) " Prop.≡ " (loop q) ")")]
      [`(Eval ,_ ,_ ,_ ,p ,θ ,L-S)
       (~a "(eval≡ₑ " (loop p) " " (loop θ) " " (loop L-S) ")")]

      ;; ps
      [`(par ,p ,q)
       (~a "(" (loop p) " ∥ " (loop q) ")")]
      [`(seq ,p ,q)
       (~a "(" (loop p) " >> " (loop q) ")")]
      [`(ρ ,θ ,p)
       (~a "(ρ " (loop θ) " · " (loop p) ")")]
      [`(present ,S ,p ,q)
       (~a "(present " (loop S) "  ∣⇒ " (loop p) " ∣⇒  " (loop q) ")")]
      [`(signal ,S ,p)
       (~a "(signl " (loop S) " " (loop p) ")")]
      [`(in-hole ,C ,p)
       (~a "(" (loop C) " ⟦ " (loop p) " ⟧c)")]
      

      ;; vars
      [(or (? p-or-q-symbol?)
           'C
           'θ 'θ_1 'θ_2
           '𝕊_1 '𝕊_2 'L-S_1 'L-S_2
           'S)
       (~a (remove-underscores-for-unicode exp))])))

(define-syntax (hidden-prem stx)
  (syntax-case stx ()
    [(_ agda)
     #'(prem agda #f)]))

(define (var-prem-redex->agda var)
  (match var
    [(? S?) (~a "(" (remove-underscores-for-unicode var) " : Signal)")]
    [(? p-or-q-symbol?) (~a "(" (remove-underscores-for-unicode var) " : Term)")]
    ['C "(C : Context)"]
    [(or 'θ 'θ_1 'θ_2) (format "(~a : Env)" (remove-underscores-for-unicode var))]
    [(or 'L-S_1 'L-S_2 '𝕊_1 '𝕊_2 '𝕊_p '𝕊_q)
     (format "(~a : eval-result)"
             (remove-underscores-for-unicode var))]
    ['n "(n : ℕ)"]))

(define (p-or-q-symbol? s)
  (and (symbol? s)
       (regexp-match #rx"^[pq]" (symbol->string s))))

(define-syntax (equiv stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:with-rewriters with-rewriters:id))
        var-premises fact-premises conc
        (~optional (~seq #:agda-conc agda-conc))
        proof)
     (with-syntax ([file (syntax-source stx)]
                   [line (syntax-line stx)]
                   [with-rewriters (if (attribute with-rewriters)
                                       #'with-rewriters
                                       #'with-paper-rewriters)])
       #`(let ()
           (define var-premises-x var-premises)
           (define fact-premises-x fact-premises)
           (register-calculus-example
            (map prem-agda (filter prem? (append var-premises-x fact-premises-x)))
            #,(if (attribute agda-conc) #''agda-conc #'(term conc))
            proof
            #:source-file 'file
            #:source-line 'line)
           (layout-fact (with-rewriters
                         (term->pict esterel-eval conc))
                        var-premises-x
                        fact-premises-x
                        (λ (t) (with-rewriters (t))))))]))

(define-syntax (not-equiv stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:with-rewriters with-rewriters:id))
        var-premises fact-premises conc)
     (with-syntax ([file (syntax-source stx)]
                   [line (syntax-line stx)]
                   [with-rewriters (if (attribute with-rewriters)
                                       #'with-rewriters
                                       #'with-paper-rewriters)])
       #`(let ()
           (define var-premises-x var-premises)
           (define fact-premises-x fact-premises)
           (layout-fact (with-rewriters
                         (term->pict esterel-eval conc))
                        var-premises-x
                        fact-premises-x
                        (λ (t) (with-rewriters (t))))))]))

(define (layout-fact conclusion-pict var-premises fact-premises-with-newlines with-rewriters)
  (define premise-gap-space 6)
  (with-rewriters (λ ()
   (define vars-prems
     (apply hbl-append
            (add-between (map prem-pict var-premises)
                         (text " , " (default-style) (default-font-size)))))
   (define and-pict (hbl-append (blank premise-gap-space 0)
                                (⇒-pict)))

   (struct fact-premise (indent things) #:transparent)
   (define fact-premisess
     (let loop ([fact-premises-with-newlines fact-premises-with-newlines]
                [indent 0])
       (define index-of-newline (find-newline fact-premises-with-newlines))
       (cond
         [index-of-newline
          (cons (fact-premise indent (take fact-premises-with-newlines index-of-newline))
                (loop (drop fact-premises-with-newlines (+ index-of-newline 1))
                      (newline-prem-indent (list-ref fact-premises-with-newlines index-of-newline))))]
         [(null? fact-premises-with-newlines) (list (fact-premise 0 '()))]
         [else (list (fact-premise indent fact-premises-with-newlines))])))

   (define facts-start-with-newline?
     (and (pair? fact-premisess)
          (null? (fact-premise-things (car fact-premisess)))))

   (define (add-at-end l x) (append l (list x)))
   (define (drop-last l) (reverse (cdr (reverse l))))

   (define fact-premiseses+conclusion
     (add-at-end (drop-last fact-premisess)
                 (fact-premise
                  0
                  (add-at-end (fact-premise-things (last fact-premisess))
                              conclusion-pict))))

   ;; one per pict line, no var premises yet
   (define fact-premises-picts
     (for/list ([fact-premises (in-list fact-premiseses+conclusion)])
       (define indent (fact-premise-indent fact-premises))
       (define the-picts
         (for/list ([fact-premise-or-conclusion (in-list (fact-premise-things fact-premises))]
                    #:when (or (pict? fact-premise-or-conclusion)
                               (pict? (prem-pict fact-premise-or-conclusion))))
           (if (prem? fact-premise-or-conclusion)
               (prem-pict fact-premise-or-conclusion)
               fact-premise-or-conclusion)))
       (apply htl-append
              (blank indent 0)
              (add-between the-picts
                           (hbl-append and-pict (blank premise-gap-space 0))))))

   (define var-prems-with-∀
     (hbl-append (leading-∀)
                 vars-prems
                 (text "." (default-style) (default-font-size))))
   
   (define first-prems-line
     (cond
       [facts-start-with-newline?
        var-prems-with-∀]
       [else
        (hbl-append var-prems-with-∀
                    (text " " (default-style) (default-font-size))
                    (blank premise-gap-space 0)
                    (car fact-premises-picts))]))
   (define all-lines
     (cons first-prems-line
           (cdr fact-premises-picts)))
   (define last-line-index (- (length all-lines) 1))
   
   (define all-lines-with-ands-at-ends-as-appropriate
     (for/list ([line (in-list all-lines)]
                [i (in-naturals)])
       (if (or (= i last-line-index)
               (and (= i 0) facts-start-with-newline?))
           line
           (hbl-append line and-pict))))
   
   (apply vl-append all-lines-with-ands-at-ends-as-appropriate))))
  
(define (find-newline prems)
  (for/or ([prem (in-list prems)]
           [i (in-naturals)]
           #:when (newline-prem? prem))
    i))
(module+ test
  (check-equal? (find-newline (list)) #f)
  (check-equal? (find-newline (list 'a 'b 'c)) #f)
  (check-equal? (find-newline (list 'a 'b 'c (newline-prem))) 3)
  (check-equal? (find-newline (list 'a 'b 'c (newline-prem) 'd 'e 'f)) 3))
