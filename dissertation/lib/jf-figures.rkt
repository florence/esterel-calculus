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
         redex/pict
         (only-in "proof-extras.rkt" ≡j eval^boolean)
         esterel-calculus/dissertation/proofs/adequacy/can-props)

(provide CB-pict
         CB-loop-pict
         CB-host-pict
         eval-pict
         ≡e-pict
         →-pict
         blocked-pict
         pure-blocked-pict
         loop-blocked-pict
         blocked-e-pict
         all-bot-rec-pict
         blocked-pict
         blocked-e-pict
         ≡j-pict
         eval^boolean-pict
         leftmost-pict
         leftmost*-pict
         with-layout)
         

(define (with-layout layout render-the-judgment-form
          #:v-append [v-append vc-append])
  (with-paper-rewriters
   (apply
    v-append
    15
    (for/list ([this-line-cases (in-list layout)])
      (apply hbl-append
             10
             (for/list ([this-case (in-list this-line-cases)])
               (parameterize ([judgment-form-cases (list this-case)]
                              [judgment-form-show-rule-names #t])
                 (render-the-judgment-form))))))))






(define CB-layout
  '(("nothing" "pause" "emit")
    ("exit" "trap")
    ("signal" "if")
    ("seq" "suspend" "ρ")
    ("par")))
(define CB-loop-layout
  '(("loop" "loop^stop")))
(define CB-host-layout
  '(("shared" "<=")
    ("var" ":=")
    ("if0")))


(define (relation-type-frame p) (frame (inset p 4)))

(define CB-pict
  (with-paper-rewriters
   (rt-superimpose
    (vr-append
     5
     (frame (inset (vl-append
                    5
                    (vl-append
                     (hbl-append
                      (es BV)
                      (words " : ")
                      (es p)
                      (words " → (Setof «var»)"))
                     (hbl-append
                      (es/unchecked FV)
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
     0 0 0 0))))

(define CB-loop-pict
  (with-paper-rewriters
   (with-layout CB-loop-layout #:v-append vl-append
                (λ () (render-judgment-form CB)))))
(define CB-host-pict
  (with-paper-rewriters
   (with-layout CB-host-layout #:v-append vl-append
                (λ () (render-judgment-form CB)))))


(define blocked-layout
  '(("set-shared-wait")
    ("shared" "set-shared")
    ("var" "set-seq")))

(define pure-blocked-layout
  '(("if" "emit-wait")
    ("suspend" "trap")
    ("seq")
    ("parl" "parr")
    ("par-both")))
(define loop-blocked-layout
  '(("loop^stop")))

(define blocked-pict (with-layout blocked-layout (λ () (render-judgment-form S:blocked))))
(define pure-blocked-pict (with-layout pure-blocked-layout (λ () (render-judgment-form S:blocked-pure))))
(define loop-blocked-pict (with-layout loop-blocked-layout (λ () (render-judgment-form S:blocked-pure))))



(define blocked-e-layout
  '(("not ready")))


(define blocked-e-pict (with-layout blocked-e-layout (λ () (render-judgment-form S:blocked-e))))


(define all-bot-rec-layout
  '(("nothing" "exit" "emit" "pause" )
    ("trap" "suspend")
    ("if-0" "if-1")
    ("if-⊥")
    ("seq-¬0" "seq-0")
    ("par")
    ("signal-0" "signal-⊥")
    ("ρ-{}")
    ("ρ-1")
    ("ρ-0")
    ("ρ-¬⊥")))


(define all-bot-rec-pict
  (with-layout
   all-bot-rec-layout
   (lambda () (render-judgment-form all-bot-rec))))

(define leftmost-pict
  (with-paper-rewriters
   (render-judgment-form S:leftmost)))

(define leftmost*-pict
  (with-layout
   '(("hole")
     ("seq" "loop^stop")
     ("parl" "par-done")
     ("par-blocked")
     ("suspend" "trap"))
   (lambda () (render-judgment-form S:leftmost*))))


#;
(define-values (standard-reduction-aux-pict standard-meta-pict)
  (with-paper-rewriters
   (with-continuation-mark 'current-reduction-arrow 'standard-reduction
    

     (define good-layout
       '(("seq" "loop^stop" "hole")
         ("suspend" "trap")
         ("parl" "par-done" "par-blocked")))

     (check-the-names 'good
                      (collection-file-path "reduction.rkt" "esterel-calculus" "redex" "model")
                      good-layout)

     (define good-pict (with-layout good-layout (λ () (render-judgment-form S:leftmost))))

     
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
       (parameterize ([metafunction-arrow-pict
                       (λ ()
                         (text " ↛ " (default-style) (default-font-size)))])
         (render-metafunctions par-⊓  #:contract? #t)))))))

(define ≡-layout
  '(("step" "sym")
    ("ref" "trn")))


(define →*-layout
  '(("step" "ref")))

(define →-layout
  '(("context")))

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


(define ≡j-layout
  '(("step" "refl")
    ("sym" "trans" "ctx")))

(define ≡j-pict
  (with-layout ≡j-layout (lambda () (render-judgment-form ≡j))))

(define eval^boolean-layout
  '(("id" "deref")
    ("not-0" "not-1")
    ("and-0-left" "and-0-right" "and-1")
    ("or-1-left" "or-1-right" "or-0")))

(define eval^boolean-pict
  (with-layout eval^boolean-layout (lambda () (render-judgment-form eval^boolean))))
