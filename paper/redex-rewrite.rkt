#lang racket

(require esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/instant
         esterel-calculus/redex/model/eval
         (prefix-in calculus: esterel-calculus/redex/model/calculus)
         (prefix-in standard: esterel-calculus/redex/model/reduction)
         scribble/base
         pict
         redex/pict
         redex/reduction-semantics
         "util.rkt"
         syntax/parse/define
         (for-syntax syntax/parse))

(define current-reduction-arrow (make-parameter 'calculus))
(define (reduction-arrow)
  (match (current-reduction-arrow)
    ['calculus
     (drop-below-ascent (text "⇀" Linux-Liberterine-name (default-font-size)) 2)]
    ['standard-reduction
     (drop-below-ascent (text "⇁" Linux-Liberterine-name (default-font-size)) 2)]))

(set-arrow-pict! '--> reduction-arrow)

;; es short for esterel, in the spirit of @racket[]
(provide es esblock define/esblock
         with-paper-rewriters
         (contract-out
          [rule (-> is-rule-label? pict?)])
         current-reduction-arrow
         indent
         words bords ;; bords = bold words
         leading-∀)

(define (rule name)
  (define (t s) (text s Linux-Liberterine-name))
  (define (b s) (text s (cons 'bold Linux-Liberterine-name)))
  (hbl-append (t "[") (b (~a name)) (t "]")))

(define is-rule-label?
  (let ([rule-names (apply set
                           (append (reduction-relation->rule-names calculus:R)
                                   (reduction-relation->rule-names standard:R)))])
    (λ (x)
      (cond
        [(symbol? x) (set-member? rule-names x)]
        [(string? x) (set-member? rule-names (string->symbol x))]
        [else #f]))))

(define-syntax-rule
  (es e)
  (with-paper-rewriters (term->pict esterel-eval e)))

(define-syntax (esblock stx)
  (syntax-parse stx
    [(_ e:expr #:run-instants input-env-vss final-program output-signals)
     (with-syntax ([source (syntax-source stx)]
                   [line (syntax-line stx)])
       #'(begin0 (esblock e)
                 (check-it-reduces 'source line
                                   (term e)
                                   input-env-vss
                                   (redex-match? esterel-eval final-program)
                                   'final-program
                                   output-signals)))]
    [(_ e:expr #:equal? expected)
     (with-syntax ([source (syntax-source stx)]
                   [line (syntax-line stx)])
       #'(begin0 (esblock e)
                 (check-equality 'source line (term e) (term expected))))]
    [(_ e:expr ...)
     #'(centered (with-paper-rewriters (vl-append 4 (term->pict esterel-eval e) ...)))]))

(define-simple-macro
  (define/esblock term-x:id block-x:id e)
  (begin
    (define block-x (esblock e))
    (define term-x (term e))))

(define (check-equality source line actual expected)
  (unless (equal? actual expected)
    (error 'esblock
           "~a:~a: expected and actual results differ:\n  expected ~s\n    actual ~s"
           source line expected actual)))

(define p? (redex-match? esterel-eval p))
(define (check-it-reduces source line p input-env-vss
                          final-program-ok? final-program-pattern
                          expected-present-signals)
  (define-values (final-p actual-present-signals) (run-instants p input-env-vss))
  (unless (final-program-ok? final-p)
    (error 'esblock
           "~a:~a: final-p does not match\n expected ~s, got:\n~a"
           source line final-program-pattern
           (pretty-format final-p #:mode 'write)))
  (unless (equal? expected-present-signals actual-present-signals)
    (error 'esblock
           "~a:~a: signals do not line up\n expected ~s\n   actual: ~s"
           source line
           expected-present-signals
           actual-present-signals)))

(define-syntax-rule (with-paper-rewriters e1 e ...) (with-paper-rewriters/proc (λ () e1 e ...)))
(define (with-paper-rewriters/proc thunk)
  (define (binop op lws)
    (define left (list-ref lws 2))
    (define right (list-ref lws 3))
    (append (list ""
                  left
                  (just-after (~a " " op " ") left))
            (if (= (lw-line left)
                   (lw-line right))
                (list "")
                (list))
            (list right
                  "")))
  (define (replace-font param)
    (let loop ([x (param)])
      (cond
        [(cons? x) (cons (car x) (loop (cdr x)))]
        [else Linux-Liberterine-name])))
  (define (def-t str) (text str (default-style) (default-font-size)))
  (define (mf-t str) (text str (metafunction-style) (metafunction-font-size)))
  (define (nt-t str) (text str (non-terminal-style) (default-font-size)))
  (define (nt-sub-t str) (text str (cons 'subscript (non-terminal-style)) (default-font-size)))
  (define (literal-t str) (text str (literal-style) (default-font-size)))
  (define (par-⊓-pict) (hbl-append (def-t "⊓") (inset (def-t "∥") 0 0 0 -6)))
  (define (dot-notation lws field) (list "" (list-ref lws 2) (~a "." field)))
  (define (down-super-n)
    (hbl-append (def-t "↓")
                (text "κ" (cons 'superscript (default-style)) (default-font-size))
                (def-t " ")))
  (define (down-super-p)
    (hbl-append (def-t "↓")
                (text "p" (cons 'superscript (default-style)) (default-font-size))
                (def-t " ")))
  (define (θ-ref-x-typeset lws)
    (define θ (list-ref lws 2))
    (define x (list-ref lws 3))
    (define ev (list-ref lws 4))
    (list "" θ "(" x ") = " ev ""))
  (define (¬θ-ref-x-typeset lws)
    (define θ (list-ref lws 2))
    (define x (list-ref lws 3))
    (define ev (list-ref lws 4))
    (list "" θ "(" x ") ≠ " ev ""))
  #;
  (define (restriction θ S)
    ;; this should match Lset-sub 's typesetting
    (define θ-pict (nt-t (~a θ)))
    (define S-pict (nt-t (~a S)))
    (define spacer (inset (ghost θ-pict) 0 0 (- (pict-width θ-pict)) 0))
    (define drop-amount 10)
    (hbl-append
     (inset (refocus
             (ct-superimpose
              (frame (blank 0 (+ (pict-height θ-pict) drop-amount)))
              spacer)
             spacer)
            2 0)
     (drop-below-ascent
      (hbl-append (def-t "dom(")
                  θ-pict
                  (def-t ") \\ { ")
                  S-pict
                  (def-t " }"))
      drop-amount)))
  (define (assert-no-underscore who what s)
    (unless (no-underscore? s)
      (error 'redex-rewrite.rkt
             "cannot typeset ~a unless the ~a argument is an identifier with no _, got ~s"
             who
             what
             s)))
  (define (no-underscore? s)
    (and (symbol? s)
         (not (regexp-match #rx"_" (symbol->string s)))))

  (define (θ/c-pict)
    (hbl-append (text "θ" (non-terminal-style) (default-font-size))
                (text "c"
                      (cons 'superscript (default-style))
                      (round (* #e1.2 (default-font-size))))))

  (define (in-dom-st-thing-is who what dom-ele equals-what lws)
    (define θ (list-ref lws 2))
    (assert-no-underscore who what (lw-e θ))
    (define θc-pict (text (~a (lw-e θ)) (non-terminal-style) (default-font-size)))
    (list
     (hbl-append
      (def-t "{ ")
      (text dom-ele (non-terminal-style))
      (def-t " ∈ dom("))
     θ
     (hbl-append
      (blank 2 0)
      (def-t ") | ")
      (θ/c-pict)
      (blank 1 0)
      (def-t "(")
      (text dom-ele (non-terminal-style) (default-font-size))
      (def-t ") = ")
      equals-what
      (def-t " }"))))

  (define (alt-ρ) (text "ϱ" (default-style) (default-font-size)))

  (define (in-dom-st-signals-are who what equals-what lws)
    (in-dom-st-thing-is who what "S"
                        (text equals-what (literal-style) (default-font-size))
                        lws))

  (define (in-dom-st-shrd-are-unready who what lws)
    (define res
      (in-dom-st-thing-is who what "s"
                          (hbl-append (def-t "⟨")
                                      (nt-t "ev")
                                      (def-t " , ")
                                      (nt-t "shared-status")
                                      (def-t "⟩"))
                          lws))
    (define extension
      (hbl-append (def-t ", ")
                  (nt-t "shared-status")
                  (def-t " ∈ {")
                  (literal-t "new")
                  (def-t " , ")
                  (literal-t "old")
                  (def-t "}")))
    (append (reverse (cdr (reverse res)))
            (list (hbl-append (last res) extension))))

  (define (L-S-pict) (Setof-an-nt "S"))
  (define (L-s-pict) (Setof-an-nt "s"))
  (define (L-x-pict) (Setof-an-nt "x"))
  (define (L-K-pict) (Setof-an-nt "κ"))
  (define (Setof-an-nt nt-name) (hbl-append (def-t "(Setof ") (nt-t nt-name) (def-t ")")))
  (define (Can-result-pict)
    (hbl-append (def-t "{ S: ")
                (L-S-pict)
                (def-t ", K: ")
                (L-K-pict)
                (def-t ", sh: ")
                (L-s-pict)
                (def-t " }")))
  (define (Lset-all-absent2-name-pict) (def-t "set-absent"))
  (define (Lset-all-ready-name-pict) (def-t "set-ready"))
  (define (loop^stop-pict)
    (define base-seq (literal-t "loop"))
    (define w (pict-width base-seq))
    (define h (pict-height base-seq))
    (define height-mod #e.5)
    (define w-inset #e.1)
    ;; a little more space to avoid the `l`
    (define w-left-offset #e.12)
    (define bar
      (dc
       (λ (dc dx dy)
         (send dc draw-line
               (+ dx (* w (+ w-left-offset w-inset)))
               dy
               (- (+ dx w) (* w w-inset))
               dy))
       w 1))
    (refocus (lbl-superimpose (vc-append (linewidth (round (* h 1/10)) bar)
                                         (blank 0 (* h height-mod)))
                              base-seq)
             base-seq))

  (define (sized-↬-pict)
    (define ↬-pict (nt-t "↬"))
    (define x-pict (nt-t "x"))
    (inset (refocus (lbl-superimpose ↬-pict (ghost x-pict))
                    x-pict)
           0 0
           (- (pict-width ↬-pict) (pict-width x-pict))
           0))

  (define (Can-θ-name-pict)
    (define the-rho (scale (alt-ρ) .7))
    (define too-much-space-below
      (hbl-append
       (mf-t "Can")
       (lift-above-baseline the-rho
                            (* -1/5 (pict-height the-rho)))))
    (define x (mf-t "x"))
    (inset (refocus (lbl-superimpose (ghost x) too-much-space-below)
                    x)
           0
           0
           (- (pict-width too-much-space-below) (pict-width x))
           0))

  (define (CB-judgment-pict)
    (hbl-append
     (text "⊢" (default-style) (default-font-size))
     (text "CB" (cons 'subscript (default-style)) (default-font-size))))

  (define (plus-equals) (hbl-append -1 (def-t "+") (def-t "=")))
  
  (with-compound-rewriters
   (['≡e
     (λ (lws)
       (list ""
             (list-ref lws 5)
             (just-after " ≡e " (list-ref lws 5))
             (list-ref lws 6)
             ""))]
    ['Eval
     (λ (lws)
       (list (hbl-append (text "Eval" (metafunction-style) (default-font-size))
                         (text "(" (default-style) (default-font-size)))
             (list-ref lws 5)
             " , "
             (list-ref lws 6)
             ") = "
             (list-ref lws 7)
             ""))]
    
    ['Lpresentin
     (λ (lws)
       (in-dom-st-signals-are "Lpresentin" "θc" "present" lws))]
    ['Lget-unknown-signals
     (λ (lws)
       (in-dom-st-signals-are "Lget-unknown-signals" "θ" "unknown" lws))]
    ['Lget-unready-shared
     (λ (lws) (in-dom-st-shrd-are-unready "Lget-unready-shared" "θ" lws))]
    ['⇀
     (λ (lws)
       (list ""
             (list-ref lws 2)
             (hbl-append (def-t " ") (reduction-arrow) (def-t " "))
             (list-ref lws 3)
             ""))]
    ['→
     (λ (lws)
       (list ""
             (list-ref lws 3)
             (def-t " → ")
             (list-ref lws 4)
             ""))]
    ['→*
     (λ (lws)
       (list ""
             (list-ref lws 4)
             (hbl-append (def-t " →")
                         (inset (def-t "*") -2 0 0 0)
                         (def-t " "))
             (list-ref lws 5)
             ""))]
    ['CB
     (λ (lws)
       (list (hbl-append (CB-judgment-pict)
                         (text "  " (default-style) (default-font-size)))
             (list-ref lws 2)
             ""))]
    ['δ
     (λ (lws)
       (define e (list-ref lws 2))
       (define θ (list-ref lws 3))
       (list (hbl-append 2
                         (text "Eval" '"Dobkin" 15)
                         ;(text "Eval" '(italic . "Brush Script MT") 10)
                         ;(text "Eval" '"SignPainter" 10)
                         ;(text "Eval" '"Snell Roundhand" 10)
                         ((white-square-bracket) #t))
             e
             " , "
             θ
             ((white-square-bracket) #f)))]
    ['blocked-or-done
     (λ (lws)
       (define p (list-ref lws 3))
       (assert-no-underscore "blocked-or-done" "p" (lw-e p))
       (list "("
             (list-ref lws 2)
             (text " ⊢ " (default-style) (default-font-size))
             (list-ref lws 3)
             (hbl-append
              (def-t " blocked or ")
              (nt-t (~a (lw-e p)))
              (def-t " ∈ ")
              (nt-t "done")
              (def-t ")"))))]
    ['done
     (λ (lws)
       (define p (list-ref lws 2))
       (list ""
             p
             (hbl-append
              (def-t " ∈ ")
              (nt-t "done"))))]
    ['blocked
     (λ (lws)
       (list ""
             (list-ref lws 2)
             (text " ⊢ " (default-style) (default-font-size))
             (list-ref lws 3)
             " blocked"))]

    ['blocked-e
     (λ (lws)
       (list ""
             (list-ref lws 2)
             (text " ⊢ " (default-style) (default-font-size))
             (list-ref lws 3)
             " blocked"))]
    ['good
     (λ (lws)
       (list ""
             (list-ref lws 2)
             (text " ⊢ " (default-style) (default-font-size))
             (list-ref lws 3)
             " det"))]
    ['next-instant (λ (lws) (list (sized-↬-pict) (list-ref lws 2) ""))]
    ['reset-θ (λ (lws) (list "⌊" (list-ref lws 2) "⌋"))]
    ['S-code-s
     (λ (lws)
       (cond
         [(= (lw-line (list-ref lws 2))
             (lw-line (list-ref lws 3)))
          ;; the whole Can expression is on a single line
          (list "{ S = "
                (list-ref lws 2)
                ", K = "
                (list-ref lws 3)
                ", sh = "
                (list-ref lws 4)
                " }")]
         [else
          ;; the Can expression is on three single lines
          ;; so we need to line up the prefixes properly
          (define open-brace (def-t "{"))
          (define raw-S: (def-t "S = "))
          (define raw-k: (def-t "K = "))
          (define raw-sh: (def-t "sh = "))
          (define spacer (ghost (lbl-superimpose raw-S: raw-k: raw-sh:)))
          (define S: (hbl-append open-brace (rbl-superimpose raw-S: spacer)))
          (define k: (hbl-append (ghost open-brace) (rbl-superimpose raw-k: spacer)))
          (define sh: (hbl-append (ghost open-brace) (rbl-superimpose raw-sh: spacer)))
          (list ""
                (just-before S: (list-ref lws 2))
                (list-ref lws 2)
                (just-after "," (list-ref lws 2))
                (just-before k: (list-ref lws 3))
                (list-ref lws 3)
                (just-after "," (list-ref lws 3))
                (just-before sh: (list-ref lws 4))
                (list-ref lws 4)
                (just-after " }" (list-ref lws 4))
                "")]))]
    ['->S (λ (lws) (dot-notation lws "S"))]
    ['->K (λ (lws) (dot-notation lws "K"))]
    ['->sh (λ (lws) (dot-notation lws "sh"))]
    ['all-ready?
     (λ (lws)
       (define L (list-ref lws 2))
       (define θ (list-ref lws 3))
       (list "∀ s ∈ " L ". " θ
             (hbl-append (def-t "(s) = ⟨_ , ") (literal-t "ready") (def-t "⟩"))))]
    ['distinct
     (λ (lws)
       (list ""
             (list-ref lws 2)
             (just-after " ∩" (list-ref lws 2))
             (list-ref lws 3)
             " = ∅ "))]
    ['Xs
     (λ (lws)
       (list (hbl-append (def-t "{ ")
                         (nt-t "x")
                         (def-t " | ")
                         (nt-t "x")
                         (def-t " ∈ "))
             (list-ref lws 2)
             " }"))]
    ['L2set
     (λ (lws)
       (list "{ "
             (list-ref lws 2)
             " , "
             (list-ref lws 3)
             " }"))]
    ['L1set
     (λ (lws)
       (list "{ "
             (list-ref lws 2)
             " }"))]
    ['L0set (λ (lws) (list "∅"))]
    ['Ldom
     (λ (lws)
       (list "dom("
             (list-ref lws 2)
             ")"))]
    ['L∈dom
     (λ (lws)
       (list ""
             (list-ref lws 2)
             " ∈ dom("
             (list-ref lws 3)
             ")"))]
    ['Lwithoutdom
     (λ (lws)
       (define θ (list-ref lws 2))
       (define S (list-ref lws 3))
       (assert-no-underscore "Lwithoutdom" "θ" (lw-e θ))
       (assert-no-underscore "Lwithoutdom" "S" (lw-e S))
       (list (def-t "(")
             θ
             (def-t " \\ {")
             S
             (def-t "})")))]
    ['LFV/e
     (λ (lws)
       (list "FV("
             (list-ref lws 2)
             ")"))]
    ['Lmax*
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (define arg2 (list-ref lws 3))
       (define κ_1 (hbl-append (nt-t "κ") (nt-sub-t "1")))
       (define κ_2 (hbl-append (nt-t "κ") (nt-sub-t "2")))
       (list (hbl-append (def-t "{ ")
                         (es (max-mf κ_1 κ_2))
                         (def-t " | ")
                         κ_1
                         (def-t " ∈ "))
             arg1
             (hbl-append (def-t " , ")
                         κ_2
                         (def-t " ∈ "))
             arg2
             " }"))]
    ['Lresort
     ;; hide resort calls
     (λ (lws)
       (define arg (list-ref lws 2))
       (list "" arg ""))]
    ['Lset-all-absent2
     (λ (lws)
       (define θ (list-ref lws 2))
       (define 𝕊 (list-ref lws 3))
       (list (hbl-append (Lset-all-absent2-name-pict)
                         (def-t "("))
             θ " , " 𝕊 ")"))]
    ['Lset-all-ready
     (λ (lws)
       (define θ (list-ref lws 2))
       (define 𝕊 (list-ref lws 3))
       (list (hbl-append (Lset-all-ready-name-pict)
                         (def-t "("))
             θ " , " 𝕊 ")"))]
    ['max-mf
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (define arg2 (list-ref lws 3))
       (list "max(" arg1 " , " arg2 ")"))]
    ['par-⊓
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (define arg2 (list-ref lws 3))
       (list "" arg1
             (let ()
               (define spacer (ghost (def-t "l")))
               (hbl-append spacer (par-⊓-pict) spacer))
             arg2 ""))]
    
    ['Lharp...
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (list
        (hbl-append (inset (def-t "{") 0 0 1 0)
                    ;;                    v   space is already included in down-super-n
                    (down-super-n) (def-t "x | x ∈ "))
        arg1 (inset (def-t "}") 2 0 0 0)))]
    ['↓
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (list (down-super-n) arg1 ""))]
    ['harp
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (list (down-super-p) arg1 ""))]
    ['greater-than-0
     (λ (lws)
       (define arg1 (list-ref lws 2))
       (list "" arg1 " > 0"))]
    ['without (λ (lws)
                (define K (list-ref lws 2))
                (define n (list-ref lws 3))
                (list "" K " \\ { " n " }"))]
    ['Can-θ (λ (lws)
              (define arg1 (list-ref lws 2))
              (define arg2 (list-ref lws 3))
              (list (hbl-append (Can-θ-name-pict)
                                ((white-square-bracket) #t))
                    arg1
                    ", "
                    arg2
                    ((white-square-bracket) #f)))]
    ['θ-ref (λ (lws)
              (define θ (list-ref lws 2))
              (define arg (list-ref lws 3))
              (list "" θ "(" arg ")"))]
    ['θ-get-S (λ (lws)
                (define θ (list-ref lws 2))
                (define arg (list-ref lws 3))
                (list "" θ "(" arg ")"))]
    ['θ-ref-S (λ (lws)
                (define θ (list-ref lws 2))
                (define S (list-ref lws 3))
                (define status (list-ref lws 4))
                (list "" θ "(" S ") = " status ""))]
    ['θ-ref-s (λ (lws)
                (define θ (list-ref lws 2))
                (define s (list-ref lws 3))
                (define ev (list-ref lws 4))
                (define shared-status (list-ref lws 5))
                (list "" θ "(" s ") = ⟨" ev " , " shared-status "⟩"))]
    ['θ-ref-x θ-ref-x-typeset]
    ['θ-ref-x-but-also-rvalue-false-is-ok-if-ev-is-zero θ-ref-x-typeset]
    ['θ-ref-S-∈ (λ (lws)
                  (define θ (list-ref lws 2))
                  (define S (list-ref lws 3))
                  (define L (list-ref lws 4))
                  (list "" θ "(" S ") ∈ " L ""))]
    ['¬θ-ref-x ¬θ-ref-x-typeset]
    ['¬θ-ref-x-and-also-not-rvalue-false ¬θ-ref-x-typeset]
    ['¬θ-ref-S
     (λ (lws)
       (define θ (list-ref lws 2))
       (define S (list-ref lws 3))
       (define status (list-ref lws 4))
       (list "" θ "(" S ") ≠ " status ""))]
    ['mtθ+S (λ (lws)
              (define S (list-ref lws 2))
              (define status (list-ref lws 3))
              (list "{ " S " ↦ " status " }"))]
    ['mtθ+s (λ (lws)
              (define s (list-ref lws 2))
              (define ev (list-ref lws 3))
              (define shared-status (list-ref lws 4))
              (list "{ " s " ↦ ⟨" ev " , " shared-status "⟩ }"))]
    ['mtθ+x (λ (lws)
              (define x (list-ref lws 2))
              (define ev (list-ref lws 3))
              (list "{ " x " ↦ " ev " }"))]

    ['add2 (λ (lws)
             (define n (list-ref lws 2))
             (list "" n "+2"))]
    ['id-but-typeset-some-parens (λ (lws) (list "(" (list-ref lws 2) ")"))]
    ['∀x (λ (lws)
           (match (lw-e (list-ref lws 2))
             ["“(suc n)”" '("n+1")]
             [else
              (list ""
                    (list-ref lws 2)
                    "")]))]
    ['∀ (λ (lws)
          (define var (list-ref lws 2))
          (define body (list-ref lws 3))
          (cond
            [(= (+ 1 (lw-line var)) (lw-line body))
             (list (hbl-append (words "(") (leading-∀))
                   var
                   (build-lw "."
                             (lw-line var) (lw-line-span var)
                             (+ (lw-column var) (lw-column-span var))
                             1)
                   body ")")]
            [else
             (list (hbl-append (words "(") (leading-∀))
                   var ". " body ")")]))]
    ['sub1 (λ (lws)
             (define n (list-ref lws 2))
             (list "" n "-1"))]
    ['∃ (λ (lws)
          (define var (list-ref lws 2))
          (define type (list-ref lws 3))
          (define body (list-ref lws 4))
          (list "∃ " var ". " body ""))]
    ['ρ (λ (lws)
          (list (list-ref lws 0)
                (just-after (hbl-append (alt-ρ) (def-t " ")) (list-ref lws 0))
                ""
                (list-ref lws 2)
                (just-after "." (list-ref lws 2))
                (list-ref lws 3)
                (list-ref lws 4)))]
    ['<- (λ (lws) (binop "←" lws))]
    ;; note: Lset-sub must match Lwithoutdom / restriction's typesetting
    ['Lset-sub (λ (lws) (binop "\\" lws))]
    ['LU (λ (lws) (binop "∪" lws))]
    ['L⊂ (λ (lws) (binop "⊂" lws))]
    ['L∈ (λ (lws) (binop "∈" lws))]
    ['L∈-OI (λ (lws) (binop "∈" lws))]
    ['L∈-OI/first (λ (lws) (binop "∈" lws))]
    ['L¬∈ (λ (lws) (binop "∉" lws))]
    ['different (λ (lws) (binop "≠" lws))]
    ['same (λ (lws) (binop "=" lws))]
    ['Σ (λ (lws) (binop "+" lws))]
    ['∧ (λ (lws) (binop "∧" lws))]
    ['<= (λ (lws) (list (list-ref lws 0)
                        (hbl-append (plus-equals) (def-t " "))
                        (list-ref lws 2)
                        (list-ref lws 3)
                        (list-ref lws 4)))]
    )
   (with-atomic-rewriters
    (['ρ (λ () (alt-ρ))]

     ;; bring this a bit more together
     [':= (λ () (hbl-append -1 (def-t ":") (def-t "=")))]
     
     ;; we don't want `n` to look like a non-terminal
     ;; currently, ev in the redex model contains hooks
     ;; to include external values in Racket. When presenting
     ;; the calculus, we really want `ev` to be just `n`.
     ['n (λ () (text "n" (default-style) (default-font-size)))]
     ['ev (λ () (text "n" (default-style) (default-font-size)))]

     ;; D is used as a convention to mean a deterministic `E` but
     ;; we forgo this for the typesetting
     ['D (λ () (text "E" (non-terminal-style) (default-font-size)))]

     ['max-mf (λ () (def-t "max"))]
     ['→ (λ () (def-t "→"))]
     ['<- (λ () (text "←" (default-style) (default-font-size)))]
     ['<= (λ () (plus-equals))]
     ['loop^stop (λ () (loop^stop-pict))]

     ;; we're using boldface for non-terminals now, so maybe this
     ;; extra attempt at clarity the "-p" suffixes isn't needed anymore
     ;['complete (λ () (text "complete-p" (non-terminal-style) (default-font-size)))]
     ;['done (λ () (text "done-p" (non-terminal-style) (default-font-size)))]
     ;['stopped (λ () (text "stopped-p" (non-terminal-style) (default-font-size)))]
     ;['paused (λ () (text "paused-p" (non-terminal-style) (default-font-size)))]

     ['↓ (λ () (down-super-n))]
     ['harp (λ () (down-super-p))]

     ['Lset-all-absent2 (λ () (Lset-all-absent2-name-pict))]
     ['Lset-all-ready (λ () (Lset-all-ready-name-pict))]

     
     ['next-instant (λ () (sized-↬-pict))]
     ['par-⊓ (λ () (par-⊓-pict))]
     ['Can-θ (λ () (Can-θ-name-pict))]
     ['CB (λ () (CB-judgment-pict))]
     ['· (λ () (def-t "{}"))]
     ['L-S (λ () (L-S-pict))]
     ['L-s (λ () (L-s-pict))]
     ['L-x (λ () (L-x-pict))]
     ['L-n (λ () (L-K-pict))]
     ['Can-result (λ () (Can-result-pict))]
     ['θ/c (λ () (θ/c-pict))])
    (parameterize ([default-font-size (get-the-font-size)]
                   [metafunction-font-size (get-the-font-size)]
                   [label-style Linux-Liberterine-name]
                   [grammar-style Linux-Liberterine-name]
                   [paren-style Linux-Liberterine-name]
                   [literal-style Inconsolata-name]
                   [metafunction-style Inconsolata-name]
                   [non-terminal-style (cons 'bold Linux-Liberterine-name)]
                   [non-terminal-subscript-style (replace-font non-terminal-subscript-style)]
                   [non-terminal-superscript-style (replace-font non-terminal-superscript-style)]
                   [default-style Linux-Liberterine-name])
      (thunk)))))

(define (words str)
  (text str (default-style) (default-font-size)))

(define (bords str)
  (text str (cons 'bold (default-style)) (default-font-size)))

(define-syntax (with-atomic-rewriters stx)
  (syntax-case stx ()
    [(_ () b ...) #'(let () b ...)]
    [(_ ([x e] . more) b ...) #'(with-atomic-rewriter x e (with-atomic-rewriters more b ...))]))

(define (indent p) (hc-append (blank 10 0) p))

(define (leading-∀) (hbl-append (term->pict esterel-eval ∀) (words " ")))
