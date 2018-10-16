#lang racket

(require esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/potential-function
         redex/pict
         pict
         "redex-rewrite.rkt")

(provide lang supp-lang
         next-instant-pict
         Can-pict Canθ-pict
         supp-non-terminals
         theta-stuff-1
         theta-stuff-1b
         theta-stuff-2
         theta-stuff-3
         theta-stuff-4
         theta-stuff-5
         e-stuff)

(define lang
  (with-paper-rewriters
   (define lhs-spacer
     (ghost
      (hbl-append
       (text "p" (non-terminal-style) (default-font-size))
       (text ", " (default-style) (default-font-size))
       (text "q" (non-terminal-style) (default-font-size))
       (text " ::=" (default-style) (default-font-size)))))
   (define (nt-∈-line lhs rhs)
     (hbl-append (rbl-superimpose
                  (hbl-append (text lhs (non-terminal-style) (default-font-size))
                              (text " ∈" (default-style) (default-font-size)))
                  lhs-spacer)
                 (text " " (default-style) (default-font-size))
                 (text rhs (default-style) (default-font-size))))
   (vl-append
    (render-language esterel #:nts '(p q))
    (htl-append
     50
     (vl-append (nt-∈-line "S" "signal variables")
                (nt-∈-line "s" "shared variables"))
     (vl-append (nt-∈-line "x" "sequential variables")
                (nt-∈-line "e" "host expressions"))))))

(define theta-join-rules
  (with-paper-rewriters
   (vl-append
    (table
     2
     (list (es (θ-ref-S (id-but-typeset-some-parens (<- θ_1 θ_2)) S (θ-ref θ_2 S)))
           (hbl-append (words "if ")
                       (es (L∈ S (Ldom θ_2))))
           (es (θ-ref-S (id-but-typeset-some-parens (<- θ_1 θ_2)) S (θ-ref θ_1 S)))
           (hbl-append (words "if ")
                       (es (L¬∈ S (Ldom θ_2)))))
     lbl-superimpose lbl-superimpose 10 0)
    (hbl-append (words "... ditto for ")
                (es s)
                (words " and ")
                (es x)))))

(define singleton-thetas
  (with-paper-rewriters
   (vl-append
    (es (mtθ+S S status))
    (es (mtθ+s s n shared-status))
    (es (mtθ+x x n)))))

(define theta-stuff-1
  (with-paper-rewriters
   (hbl-append (bords "Empty Environment")
               (words ": ")
               (es ·))))

(define theta-stuff-1b
  (with-paper-rewriters
   (vl-append
    (hbl-append (bords "Singleton Environments")
                (words ": { « var » ↦ « val » }"))
    (indent singleton-thetas))))

(define theta-stuff-2
  (with-paper-rewriters
   (vl-append
    (hbl-append (bords "Environment Composition")
                (words ": ")
                (es (<- θ θ)))
    (indent theta-join-rules))))

(define theta-stuff-3
  (with-paper-rewriters
   (vl-append
    (hbl-append (bords "Complete Environments")
                (words ": ")
                (es θ/c))
    (indent (vl-append (words "A complete environment is one")
                       (hbl-append (words "where no signals are ")
                                   (es unknown))
                       (hbl-append (words " and all shared variables are ")
                                   (es ready)))))))

(define theta-stuff-4
  (with-paper-rewriters
   (vl-append
    (hbl-append (bords "Resetting Environments")
                (words ": ")
                (es (reset-θ θ/c)))
    (indent (vl-append (words "Resetting a complete environment")
                       (hbl-append (words "updates all signals to ")
                                   (es unknown))
                       (hbl-append (words "and all shared variables to ")
                                   (es old)))))))

(define theta-stuff-5
  (with-paper-rewriters
   (vl-append
    (hbl-append (bords "Restricting the Domain")
                (words ": ")
                (es (Lwithoutdom θ S)))
    (indent (vl-append (words "Restricting the domain of an")
                       (words "environment removes the")
                       (hbl-append (words "binding for ") (es S)))))))

(define e-stuff
  (with-paper-rewriters
   (vl-append
    (bords "Embedded host language expressions")
    (indent
     (vl-append
      (hbl-append (es e) (words ": host expressions"))
      (hbl-append (es (LFV/e e))
                  (words ": all ")
                  (es x)
                  (words " and ")
                  (es s)
                  (words " that appear free in ")
                  (es e))
      (hbl-append (es (δ e θ))
                  (words ": evaluation; produces ")
                  (es n)))))))

(define supp-non-terminals
  (with-paper-rewriters
      (render-language esterel-eval
                    #:nts
                    '(stopped done paused E p q complete
                             status shared-status))))

(define supp-lang
  (with-paper-rewriters
   (htl-append
    20
    (vc-append
     supp-non-terminals
     
     (parameterize ([metafunction-combine-contract-and-rules
                     (λ (c-p rule-p)
                       (vl-append
                        (blank 0 10)
                        (vl-append 2 c-p rule-p)))])
       (vl-append
        (ghost (text "a"))
        (bords "Metafunctions:")
        (render-metafunction harp #:contract? #t))))
    (vl-append
     10
     theta-stuff-1
     theta-stuff-1b
     theta-stuff-2
     theta-stuff-3
     theta-stuff-4
     theta-stuff-5
     e-stuff))))

(define κ-pict
  (with-paper-rewriters
   (parameterize ([rule-pict-style 'vertical])
     (render-language esterel-eval #:nts '(κ)))))

(define ↓-pict
  (with-paper-rewriters
   (parameterize ([metafunction-pict-style 'left-right/vertical-side-conditions]
                  [where-make-prefix-pict (λ () (text "if " (default-style)))])
     (frame (inset (render-metafunction ↓ #:contract? #t)
                   6 4 4 6)))))

(define κmax-stuff
  (with-paper-rewriters
   (frame (inset (vl-append
                  (hbl-append (es max-mf)
                              (words " : ")
                              (es κ)
                              (words " ")
                              (es κ)
                              (words " → ")
                              (es κ))
                  (indent (vl-append
                           (hbl-append (es (max-mf κ_1 κ_2))
                                       (words " computes"))
                           (hbl-append (words "the maximum of ")
                                       (es κ_1) (words " and"))
                           (hbl-append (es κ_2) (words " where we define "))
                           (hbl-append (es nothin) (words " < ")
                                       (es paus) (words " < 0 < 1 < ...")))))
                 6 4 4 6))))

(define Can-pict
  (with-paper-rewriters
   (vl-append
    20
    κ-pict 
    (rt-superimpose
     (parameterize ([metafunction-pict-style 'left-right/vertical-side-conditions]
                    [sc-linebreaks
                     (for/list ([i (in-range 23)])
                       (or (= i 16)
                           (= i 17)))])
       (render-metafunction Can #:contract? #t))
     (vr-append 10 ↓-pict κmax-stuff)))))

(define Canθ-pict
  (with-paper-rewriters
   (parameterize ([metafunction-pict-style 'left-right/vertical-side-conditions])
     (render-metafunction Can-θ #:contract? #t))))

(define next-instant-pict
  (with-paper-rewriters
   (render-metafunction next-instant #:contract? #t)))
