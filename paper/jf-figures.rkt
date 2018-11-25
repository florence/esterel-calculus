#lang racket
(require esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/eval
         esterel-calculus/redex/model/lset
         (prefix-in S: esterel-calculus/redex/model/reduction)
         (only-in esterel-calculus/redex/test/binding CB)
         esterel-calculus/redex/model/potential-function
         pict
         "redex-rewrite.rkt"
         redex/reduction-semantics
         redex/pict)

(provide standard-meta-pict
         CB-pict
         standard-reduction-aux-pict
         eval-pict
         ≡e-pict
         →-pict)
         

(define (with-layout layout render-the-judgment-form
          #:v-append [v-append vc-append])
  (with-paper-rewriters
   (apply
    v-append
    20
    (for/list ([this-line-cases (in-list layout)])
      (apply hbl-append
             25
             (for/list ([this-case (in-list this-line-cases)])
               (parameterize ([judgment-form-cases (list this-case)]
                              [judgment-form-show-rule-names #f])
                 (render-the-judgment-form))))))))


(define (check-the-names judgment-form-name filename layout-names)
  (define (right-name? found-name) (equal? found-name judgment-form-name))
  (define all-the-names
    (call-with-input-file filename
      (λ (port)
        (read-line port)
        (let loop ()
          (define exp (read port))
          (when (eof-object? exp)
            (error 'calculus-figures.rkt
                   "error in hack parsing that is designed to find all of the rule names"))
          (define (check-clauses clauses)
            (for/list ([clause (in-list clauses)])
              (for/first ([thing (in-list clause)]
                          #:when (string? thing))
                thing)))
          (match exp
            [`(define-judgment-form ,lang
                #:mode (,(? right-name? I) ,_ ...)
                #:contract ,_
                ,clauses ...)
             (check-clauses clauses)]
            [`(define-judgment-form ,lang
                #:contract ,_
                #:mode (,(? right-name? I) ,_ ...)
                ,clauses ...)
             (check-clauses clauses)]
            [`(define-judgment-form ,lang
                #:mode (,(? right-name? I) ,_ ...)
                ,clauses ...)
             (check-clauses clauses)]
            [_ (loop)])))))
  (unless (andmap string? all-the-names)
    (error 'calculus-figures.rkt
           "error in check-the-names hack that is designed to find all of the rule names for ~a"
           filename))
  (let ([all-names (sort all-the-names string<?)]
        [used-names (sort (flatten layout-names) string<?)])
    (unless (equal? all-names used-names)
      (error 'calculus-figures.rkt
             "mismatch between layout names and full set of names for ~a:\n  all: ~s\n used: ~s\n  ~a"
             judgment-form-name all-names used-names filename))))



(define CB-layout
  '(("nothing" "pause" "emit")
    ("signal" "present")
    ("shared" "<=")
    ("seq" "suspend" "ρ")
    ("par" ":=")
    ("loop^stop" "var")
    ("loop" "trap" "exit" "if")))

(check-the-names 'CB
                 (collection-file-path "binding.rkt" "esterel-calculus" "redex" "test")
                 CB-layout)

(define (relation-type-frame p) (frame (inset p 4)))

(define CB-pict
  (with-paper-rewriters
   (rt-superimpose
    (vr-append
     10
     (relation-type-frame (es (CB p)))
     (frame (inset (vl-append
                    5
                    (vl-append
                     (hbl-append
                      (es BV)
                      (words " : ")
                      (es p)
                      (words " → (Setof «var»)"))
                     (hbl-append
                      (es FV)
                      (words " : ")
                      (es p)
                      (words " → (Setof «var»)")))
                    (indent
                     (vl-append (words "Computes the bound and")
                                (words "free variables, respectively.")
                                (words "The variables include signals,")
                                (words "shared variables and")
                                (words "sequential variables."))))
                   6 4 4 6)))
    (inset 
     (with-layout CB-layout #:v-append vl-append
       (λ () (render-judgment-form CB)))
     0 10 0 0))))

(define-values (standard-reduction-aux-pict standard-meta-pict)
  (with-paper-rewriters
   (parameterize ([current-reduction-arrow 'standard-reduction])
    
     (define blocked-layout
       '(("var" "set-seq")
         ("present"  "suspend" "trap")
         ("par-both" "parl" "parr")
         ("seq" "loop^stop")
         ("shared" "set-shared")))

     (check-the-names 'blocked
                      (collection-file-path "reduction.rkt" "esterel-calculus" "redex" "model")
                      blocked-layout)

     (define blocked-pict (with-layout blocked-layout (λ () (render-judgment-form S:blocked))))

     (define blocked-e-layout
       '(("old" "new")))

     (check-the-names 'blocked-e
                      (collection-file-path "reduction.rkt" "esterel-calculus" "redex" "model")
                      blocked-e-layout)

     (define blocked-e-pict (with-layout blocked-e-layout (λ () (render-judgment-form S:blocked-e))))

     (define good-layout
       '(("seq" "loop^stop" "hole")
         ("suspend" "trap")
         ("parl" "par-done" "par-blocked")))

     (check-the-names 'good
                      (collection-file-path "reduction.rkt" "esterel-calculus" "redex" "model")
                      good-layout)

     (define good-pict (with-layout good-layout (λ () (render-judgment-form S:good))))

     (define blocked-type (inset (relation-type-frame (es (blocked θ p))) 0 -5 0 0))
     (define blocked-e-type (relation-type-frame (es (blocked-e θ e))))
     (define good-type (inset (relation-type-frame (es (good θ E))) 0 -10 0 0))
     (define without-labels
       (vc-append
        35
        (vc-append 20
                   blocked-pict
                   (hc-append blocked-e-pict (blank 20 0)))
        good-pict
        ))
     (define (add-a-label main pict label)
       (define-values (x y) (ct-find main pict))
       (pin-over
        main
        (- (pict-width main) (pict-width label))
        y
        (inset label 0 -0 0 0)))
     (values
      (inset
       (add-a-label
        (add-a-label
         (add-a-label
          without-labels
          good-pict good-type)
         blocked-e-pict blocked-e-type)
        blocked-pict blocked-type)
      
       

       0 20 ;; to make space for the label on the top
       0 0)
      (vc-append
       (parameterize ([metafunction-pict-style 'up-down/compact-side-conditions])
         (htl-append
          20
          (render-metafunction Lset-all-absent2 #:contract? #t)
          (render-metafunction Lset-all-ready #:contract? #t)))
       (parameterize ([metafunction-arrow-pict
                       (λ ()
                         (text " ↛ " (default-style) (default-font-size)))])
         (render-metafunctions par-⊓  #:contract? #t)))))))

(define ≡-layout
  '(("step" "sym")
    ("ref" "trn")))

(check-the-names '≡e
                 (collection-file-path "eval.rkt" "esterel-calculus" "redex" "model")
                 ≡-layout)

(define →*-layout
  '(("step" "ref")))

(check-the-names '→*
                 (collection-file-path "eval.rkt" "esterel-calculus" "redex" "model")
                 →*-layout)

(define →-layout
  '(("context")))

(check-the-names '→
                 (collection-file-path "eval.rkt" "esterel-calculus" "redex" "model")
                 →-layout)

(define ≡e-pict (with-layout ≡-layout (λ () (render-judgment-form ≡e))))
(define →-pict (with-layout →-layout (λ () (render-judgment-form →))))

(define eval-pict
  (with-paper-rewriters
   (hc-append
    40
    (vc-append
     25
     (render-judgment-form Eval)
     ≡e-pict
     →-pict
     (with-layout →*-layout (λ () (render-judgment-form →*))))
    (render-language esterel-eval #:nts '(C)))))
