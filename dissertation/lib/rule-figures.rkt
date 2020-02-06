#lang racket
(require esterel-calculus/redex/model/calculus
         (prefix-in S: esterel-calculus/redex/model/reduction)
         redex/pict
         redex/reduction-semantics
         pict
         "redex-rewrite.rkt")

(provide calculus-side-condition-beside-rules
         calculus-rule-groups
         reduction-relation-pict
         render-rules
         render-specific-rules)

;; approximate, determined by experimentation via `frame`
;; and running latex and eyeballing the output,
;; and then some random twiddling
(define page-width 600)

(define (render-rules name-for-error reduction-relation rule-groups side-condition-beside-rules
                      #:only-one-rule? [only-one-rule? #f]
                      #:rule-to-skip [rule-to-skip #f])
  (define do-rule-groups?
    (ormap (lambda (x) (non-empty-string? (first x))) rule-groups))
  (define rules-named-in-rule-groups
    (sort (maybe-cons rule-to-skip (filter symbol? (flatten rule-groups))) symbol<?))
  (define all-rules
    (sort
     (or (render-reduction-relation-rules)
         (reduction-relation->rule-names reduction-relation))
     symbol<?))
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
    (define  max-rule-name-width
      (apply max
             (map
              (lambda (info)
                (pict-width (rule (rule-pict-info-label info))))
              infos)))
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
                            side-condition-beside-rules
                            max-rule-name-width))))
        (if do-rule-groups?
            (hc-append sideways-gap (sideways-text group-name) rule-picts)
            rule-picts)))
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


(define (render-a-rule info full-width side-condition-beside-rules max-rule-name-width)
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
       (define side-conditions-inset (+ max-rule-name-width))
       (define sc-pict
         (rule-pict-info->side-condition-pict info (- full-width side-conditions-inset)))
       (vl-append main-part
                  (hbl-append (blank 20 0) sc-pict))]))
  (ht-append
   3
   (ltl-superimpose rule-label (blank max-rule-name-width 0))
   rule+sc))

(define calculus-side-condition-beside-rules
  (set 'is-present
       'if-true 'if-false))

(define calculus-rule-groups
  '(("signals" signal emit is-present is-absent)
    ("shared variables" shared set-old set-new)
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

(define reduction-relation-pict
  (with-paper-rewriters
   (parameterize ([rule-pict-style (render-rules 'calculus
                                                 R*
                                                 calculus-rule-groups
                                                 calculus-side-condition-beside-rules)])
     (render-reduction-relation R*))))

(define (render-specific-rules r)
  (with-paper-rewriters
   (parameterize* ([render-reduction-relation-rules r]
                   [rule-pict-style (render-rules 'calculus
                                                  R*
                                                  `(("" ,@r))
                                                  calculus-side-condition-beside-rules)])
     (render-reduction-relation R*))))
