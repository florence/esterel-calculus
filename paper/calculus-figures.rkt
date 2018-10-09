#lang racket

(require esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/calculus
         esterel-calculus/redex/model/eval
         esterel-calculus/redex/model/lset
         (prefix-in S: esterel-calculus/redex/model/reduction)
         esterel-calculus/redex/model/potential-function
         (only-in esterel-calculus/redex/test/binding CB)
         redex/pict
         redex/reduction-semantics
         pict
         "redex-rewrite.rkt")

(provide lang supp-lang
         reduction-relation-pict
         standard-reduction-pict
         next-instant-pict
         Can-pict Canθ-pict CB-pict
         standard-reduction-aux-pict
         eval-pict
         ≡e-pict →-pict supp-non-terminals
         theta-stuff-1
         theta-stuff-1b
         theta-stuff-2
         theta-stuff-3
         theta-stuff-4
         theta-stuff-5
         e-stuff
         standard-meta-pict
          render-rules calculus-rule-groups calculus-side-condition-beside-rules)

;; approximate, determined by experimentation via `frame`
;; and running latex and eyeballing the output
(define page-width 490)

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

(define (indent p) (hc-append (blank 10 0) p))

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
   (vl-append
    (hbl-append (bords "Singleton Environments")
                (words ": { « var » ↦ « val » }"))
    (indent singleton-thetas))))

(define theta-stuff-1b
  (with-paper-rewriters
   (hbl-append (bords "Empty Environment")
               (words ": ")
               (es ·))))

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
                       (words "environment removes all of the bindings")
                       (words "except those listed at the bottom of")
                       (hbl-append (words "the bar, in this case removing ")
                                   (es S)))))))

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

(define calculus-side-condition-beside-rules
  (set 'is-present 'is-absent
       'if-true 'if-false))

(define calculus-rule-groups
  '(("signals" signal emit absence is-present is-absent)
    ("shared variables" shared set-new set-old readyness)
    ("sequential variables" var set-var if-true if-false)
    ("ϱ" merge)
    ("seq" seq-done seq-exit)
    ("trap" trap)
    ("par" par-nothing par-1exit par-2exit par-swap)
    ("" suspend)
    ("loop" loop loop^stop-exit)))

(define standard-side-condition-beside-rules
  (set 'merge 'seq-done 'seq-exit 'trap
       'is-present 'is-absent 'suspend
       'parl 'parr 'if-true 'if-false
       'signal 'loop 'loop^stop-exit))

(define standard-rule-groups
  '(("signals" signal emit absence is-present is-absent)
    ("shared variables" shared set-new set-old readyness)
    ("sequential variables" var set-var if-true if-false)
    ("ϱ" merge)
    ("seq" seq-done seq-exit)
    ("trap" trap)
    ("par" parr parl)
    ("" suspend)
    ("" loop loop^stop-exit)))

(define (render-rules name-for-error reduction-relation rule-groups side-condition-beside-rules
                      #:only-one-rule? [only-one-rule? #f]
                      #:rule-to-skip [rule-to-skip #f])

  (define rules-named-in-rule-groups
    (sort (maybe-cons rule-to-skip (filter symbol? (flatten rule-groups))) symbol<?))
  (define all-rules (sort (reduction-relation->rule-names reduction-relation) symbol<?))
  (cond
    [only-one-rule?
     (unless (= (length rules-named-in-rule-groups) 1)
       (error 'render-rules "promised only a single rule, but there is not just one: ~s"
              rules-named-in-rule-groups))]
    [else
     (unless (equal? rules-named-in-rule-groups all-rules)
       (error 'render-rules "rules in ~a reduction relation don't match rule-groups:\n  ~s\n  ~s"
              name-for-error
              all-rules
              rules-named-in-rule-groups))])
  
  (λ (infos)
    (define (sideways-text str)
      (text str (default-style) (default-font-size) (/ pi 2)))
    (define sideways-gap 4)
    (define rules
      (for/list ([rule-group (in-list rule-groups)])
        (define group-name (car rule-group))
        (define group-rules (cdr rule-group))
        (define group-infos (select group-rules infos))
        (define rule-picts
          (apply
           vl-append
           4
           (for/list ([info (in-list group-infos)])
             (render-a-rule info
                            (- page-width
                               (pict-width (sideways-text "Xy"))
                               sideways-gap)
                            side-condition-beside-rules))))
        (hc-append sideways-gap (sideways-text group-name) rule-picts)))
    (apply
     vl-append
     (add-between rules (inset (frame (blank page-width 0)) 0 4)))))

(define (maybe-cons x l) (if x (cons x l) l))

(define (select rule-names infos)
  (for/list ([rule-name (in-list rule-names)])
    (define ans
      (for/first ([info (in-list infos)]
                  #:when (equal? (rule-pict-info-label info) rule-name))
        info))
    (unless ans (error 'select "didn't find rule names ~s" rule-name))
    ans))
(define (select¬ not-rule-names infos)
  (define rule-names
    (for/list ([rule-name (in-list (map rule-pict-info-label infos))]
               #:unless (member rule-name not-rule-names))
      rule-name))
  (select rule-names infos))

(define (render-a-rule info full-width side-condition-beside-rules)
  (define main-part
    (htl-append 4
                (rule-pict-info-lhs info)
                (arrow->pict (rule-pict-info-arrow info))
                (rule-pict-info-rhs info)))
  (define rule-label (rule (rule-pict-info-label info)))
  (define rule+sc
    (cond
      [(set-member? side-condition-beside-rules (rule-pict-info-label info))
       (define beside-gap 2)
       (define remaining-width (- full-width
                                  (pict-width main-part)
                                  beside-gap
                                  beside-gap
                                  (pict-width rule-label)))
       (htl-append main-part
                   (blank beside-gap 0)
                   (rule-pict-info->side-condition-pict info remaining-width))]
      [else
       (define side-conditions-inset 20)
       (define sc-pict
         (rule-pict-info->side-condition-pict info
                                              (- full-width side-conditions-inset)))
       (vl-append main-part
                  (hbl-append (blank side-conditions-inset 0)
                              sc-pict))]))
  (ltl-superimpose
   rule+sc
   (rtl-superimpose (blank full-width 0) rule-label)))

(define reduction-relation-pict
  (with-paper-rewriters
   (parameterize ([rule-pict-style (render-rules 'calculus
                                                 R*
                                                 calculus-rule-groups
                                                 calculus-side-condition-beside-rules)])
     (render-reduction-relation R*))))

(define standard-reduction-pict
  (parameterize ([current-reduction-arrow 'standard-reduction])
    (with-paper-rewriters
     (parameterize ([rule-pict-style (render-rules 'standard
                                                   S:R
                                                   standard-rule-groups
                                                   standard-side-condition-beside-rules)])
       (render-reduction-relation S:R)))))

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
    ("signal" "present" "ρ")
    ("var" ":=" "if")
    ("par")
    ("seq" "suspend")
    ("loop" "loop^stop")
    ("trap" "exit" "shared" "<=")))

(check-the-names 'CB
                 (collection-file-path "binding.rkt" "esterel-calculus" "redex" "test")
                 CB-layout)


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
