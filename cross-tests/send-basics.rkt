#lang racket

;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require "send-lib.rkt"
         redex/reduction-semantics
         (only-in esterel-calculus/redex/model/shared
                  esterel-eval))

(module+ test (require rackunit))

(provide send-p send-e send-θ send-set
         send-E-decomposition send-E
         send-nat-not-in-nat-list
         θ-to-hash
         
         
         send-blocked-or-done
         send-leftmost
         send-all-ready
         send-done
         send-stopped
         send-paused
         send-isSigϵ
         send-isShrϵ
         send-isVar∈)

(define/contract (send-p p)
  (-> p? string?)
  (cond
    [(symbol? p)
     ;; don't bother making new top-level
     ;; declarations for "atomic" 'p's.
     (recur-over-p p (λ args (apply format args)))]
    [else (send-thing p "p" "Term" recur-over-p)]))

(define (recur-over-p p spew)
  (let loop ([p p])
    (match p
      [`(∀x ,abstract ,concrete) (spew (~a (remove-underscores-for-unicode abstract)))]
      [`nothing (spew "nothin")]
      [`pause (spew "pause")]
      [`(signal ,S ,p)
       (spew "(signl ~a " (get-signal S))
       (loop p)
       (spew ")")]
      [`(present ,S ,p ,q)
       (spew "(present ~a " (get-signal S))
       (spew " ∣⇒ ")
       (loop p)
       (spew " ∣⇒ ")
       (loop q)
       (spew ")")]
      [`(emit ,S)
       (spew "(emit ~a)" (get-signal S))]
      [`(par ,p ,q)
       (spew "(")
       (loop p)
       (spew " ∥ ")
       (loop q)
       (spew ")")]
      [`(loop ,p)
       (spew "(loop ")
       (loop p)
       (spew ")")]
      [`(seq ,p ,q)
       (spew "(")
       (loop p)
       (spew " >> ")
       (loop q)
       (spew ")")]
      [`(loop^stop ,p ,q)
       (spew "(loopˢ ")
       (loop p)
       (spew " ")
       (loop q)
       (spew ")")]
      [`(suspend ,p ,S)
       (spew "(suspend ")
       (loop p)
       (spew " ~a)" S)]
      [`(trap ,p)
       (spew "(trap ")
       (loop p)
       (spew ")")]
      [`(exit ,n)
       (spew "(exit ")
       (spew (send-n n))
       (spew ")")]
      [`(shared ,s := ,e ,p)
       (spew "(shared ~a ≔ ~a in: " s (send-e e))
       (loop p)
       (spew ")")]
      [`(<= ,s ,e)
       (spew "(~a ⇐ " s)
       (spew "~a" (send-e e))
       (spew ")")]
      [`(var ,x := ,e ,p)
       (spew "(var ~a ≔ " x)
       (spew "~a" (send-e e))
       (spew " in: ")
       (loop p)
       (spew ")")]
      [`(:= ,x ,e)
       (spew "(~a ≔ ~a)" x (send-e e))]
      [`(if ,x ,p ,q)
       (spew "(if ~a ∣⇒ " x)
       (loop p)
       (spew " ∣⇒ ")
       (loop q)
       (spew ")")]
      [`(ρ ,θ ,A ,p)
       (define θ-id (send-θ θ))
       (spew "(ρ⟨ ~a , ~a ⟩· " θ-id A)
       (loop p)
       (spew ")")])))

(define/contract (get-signal S)
  (-> (or/c S? (list/c '∀x any/c S?)) string?)
  (match S
    [(? symbol?) (~a S)]
    [`(∀x ,abstract ,concrete) (~a (remove-underscores-for-unicode abstract))]))

(define/contract (send-in-C-hole in-hole-C-p)
  (-> any/c string?)
  (send-thing in-hole-C-p "Cp" "Term" recur-over-in-C-hole))

(define (recur-over-in-C-hole in-hole-C-p spew)
  ;; not clear how to do this if there is more
  ;; than one possible decomposition; need to
  ;; actually supply the list of contexts here
  ;; but redex doesn't easily give those out
  (match in-hole-C-p
    [`(in-hole (∀x ,(? symbol? abstract) ,concrete) ,p)
     (spew "(")
     (spew (~a abstract))
     (spew " ⟦ ")
     (spew (send-p p))
     (spew " ⟧c)")]
    [_ (error 'send-in-C-hole "not really implemented ~s" in-hole-C-p)]))

  

(define/contract (send-n n)
  (-> any/c string?)
  (cond
    [(natural? n)
     ;; don't bother making new top-level
     ;; declarations for numbers, just inline them
     (~a n)]
    [else (send-thing n "anat" "ℕ" recur-over-n)]))

(define (recur-over-n n spew)
  (let loop ([n n])
    (match n
      [`(∀x ,abstract ,concrete) (spew (~a abstract))]
      [`(add1 ,n)
       (spew "(suc ")
       (loop n)
       (spew ")")]
      [(? natural?)
       (spew (~a n))])))

(define/contract (send-e e)
  (-> e? string?)
  (send-thing e "e" "Expr" recur-over-e))

(define (recur-over-e e spew)
  (match e
    [`(,f ,s/ls ...)

     (match f
       [`+
        (spew "plus ")]
       [`(rfunc ,any)
        (spew "plus ")])
       
     (cond
       [(null? s/ls) (spew "[]")]
       [else
        (spew "(")
        (for ([s/l (in-list s/ls)]
              [i (in-naturals)])
          (unless (zero? i) (spew " ∷ "))
          (match s/l
            [(? s?)
             (spew "(shr-ref ~a)" s/l)]
            [(? x?)
             (spew "(seq-ref ~a)" s/l)]
            [(? natural?)
             (spew "(num ~a)" s/l)]
            [`(rvalue ,any)
             (error 'ack "not sure what to do here")]))
        (spew " ∷ [])")])]))


(define/contract (send-θ θ)
  (-> θ? string?)
  (send-thing θ "th" "Env" recur-over-θ))

(define (recur-over-θ θ spew)
  (define max-S #f)
  (define max-s #f)
  (define max-x #f)
  (define S-map (make-hash))
  (define s-map (make-hash))
  (define x-map (make-hash))

  (define (max/f a b) (if (and a b) (max a b) (or a b)))
  
  (let loop ([θ θ])
    (match θ
      [`· (void)]
      [`{,env-v ,θ}
       (match env-v
         [`(sig ,S ,status)
          (set! max-S (max/f max-S (var->index S)))
          (hash-set! S-map (var->index S) status)]
         [`(shar ,s ,ev ,shared-status)
          (set! max-s (max/f max-s (var->index s)))
          (hash-set! s-map (var->index s) (cons ev shared-status))]
         [`(var· ,x ,ev)
          (set! max-x (max/f max-x (var->index x)))
          (hash-set! x-map (var->index x) ev)])
       (loop θ)]))

  (define (send-map max-ent the-map send-content)
    (cond
      [max-ent
       (spew "(")
       (for ([i (in-range (+ 1 max-ent))])
         (define val (hash-ref the-map i #f))
         (match val
           [#f (spew "nothing")]
           [_ (spew "(just ") (send-content val) (spew ")")])
         (spew " ∷ "))
       (spew "[])")]
      [else (spew "[]")]))
    
  (spew "(Θ ")
  (send-map max-S S-map
            (λ (val)
              (match val
                [`present (spew "Signal.present")]
                [`absent (spew "Signal.absent")]
                [`unknown (spew "Signal.unknown")])))
  (spew " ")
  (send-map max-s s-map
            (λ (val)
              (spew "(")
              (match (cdr val)
                [`ready (spew "ShVar.ready")]
                [`new (spew "ShVar.new")]
                [`old (spew "ShVar.old")])
              (spew " , ~a)" (car val))))
  (spew " ")
  (send-map max-x x-map
            (λ (val) (spew "~a" val)))
  (spew ")"))

(define/contract (send-E E)
  (-> E? string?)
  (send-thing (invert-E E) "E" "EvaluationContext" recur-over-E))

(define (recur-over-E inverted-E spew)
  (for ([E-frame (in-list inverted-E)])
    (match E-frame
      [(list 1 `(par ,p ,q))
       (spew "(epar₁ ~a)" (send-p q))]
      [(list 2 `(par ,p ,q))
       (spew "(epar₂ ~a)" (send-p p))]
      [(list 1 `(seq ,p ,q))
       (spew "(eseq ~a)" (send-p q))]
      [(list 1 `(loop^stop ,p ,q))
       (spew "(eloopˢ ~a)" (send-p q))]
      [(list 1 `(suspend ,p ,S))
       (spew "(esuspend ~a)" S)]
      [(list 1 `(trap ,p))
       (spew "etrap")])
    (spew " ∷ "))
  (spew "[]"))

;; flips the context inside out based on the location
;; of the hole in the context; this function doesn't work
;; on the actual structure of E, but instead assumes that
;; each nested pair of parens is a separate expression form
;; (e.g., if we had `E ::= ... (let ([x E]) e)` as a context,
;;  this function wouldn't work right because E is three
;;  layers deep inside in the `let` production)
;; the result is the subexpression at each position,
;; as well as the index of the position where the spine
;; of the E continues at the next layer down
(define/contract (invert-E orig-E)
  (-> E? (listof (list/c natural? any/c)))
  (let loop ([E orig-E])
    (cond
      [(hole? E) '()]
      [(list? E)
       (define candidates
         (filter
          values
          (for/list ([E (in-list E)]
                     [i (in-naturals)])
            (define inside (loop E))
            (and inside (list i inside)))))
       (cond
         [(null? candidates)
          #f]
         [(= 1 (length candidates))
          (define candidate (car candidates))
          (cons (list (list-ref candidate 0) E)
                (list-ref candidate 1))]
         [else
          (error 'invert-E "found multiple holes inside ~s, orig ~s" E orig-E)])]
      [else #f])))

(module+ test
  (check-equal? (invert-E (term (seq (par hole pause) nothing)))
                (list (list 1 (term (seq (par hole pause) nothing)))
                      (list 1 (term (par hole pause)))))
  (check-equal? (invert-E (term (seq (par pause hole) nothing)))
                (list (list 1 (term (seq (par pause hole) nothing)))
                      (list 2 (term (par pause hole)))))
  (check-equal? (invert-E (term (par nothing (seq (suspend (trap hole) S) pause))))
                (list (list 2 (term (par nothing (seq (suspend (trap hole) S) pause))))
                      (list 1 (term (seq (suspend (trap hole) S) pause)))
                      (list 1 (term (suspend (trap hole) S)))
                      (list 1 (term (trap hole))))))

(define/contract (uninvert-and-fill-it E-frames p)
  (-> list? p? p?)
  (let loop ([E-frames E-frames])
    (cond
      [(null? E-frames) p]
      [else
       (match (car E-frames)
         [(list 1 `(par ,p ,q))
          `(par ,(loop (cdr E-frames)) ,q)]
         [(list 2 `(par ,p ,q))
          `(par ,p ,(loop (cdr E-frames)))]
         [(list 1 `(seq ,p ,q))
          `(seq ,(loop (cdr E-frames)) ,q)]
         [(list 1 `(suspend ,p ,S))
          `(suspend ,(loop (cdr E-frames)) ,S)]
         [(list 1 `(trap ,p))
          `(trap ,(loop (cdr E-frames)))])])))

(module+ test
  (let ([E (term (par nothing (seq (suspend (trap hole) S) pause)))])
    (check-equal?
     (uninvert-and-fill-it (invert-E E) 'nothing)
     (term (in-hole ,E nothing)))))

(define/contract (send-E-decomposition E p)
  (-> E? p? string?)
  (send-thing E
              "D"
              (~a (send-p (term (in-hole ,E ,p)))
                  " ≐ "
                  (send-E E)
                  " ⟦ "
                  (send-p p)
                  " ⟧e")
              recur-over-E-decomposition))

(define (recur-over-E-decomposition E spew)
  (let loop ([E-frames (invert-E E)])
    (cond
      [(null? E-frames) (spew "dehole")]
      [else
       (match (car E-frames)
         [(list 1 `(par ,p ,q))
          (spew "(depar₁ ")
          (loop (cdr E-frames))
          (spew ")")]
         [(list 2 `(par ,p ,q))
          (spew "(depar₂ ")
          (loop (cdr E-frames))
          (spew ")")]
         [(list 1 `(seq ,p ,q))
          (spew "(deseq ")
          (loop (cdr E-frames))
          (spew ")")]
         [(list 1 `(loop^stop ,p ,q))
          (spew "(deloopˢ ")
          (loop (cdr E-frames))
          (spew ")")]
         [(list 1 `(suspend ,p ,S))
          (spew "(desuspend ")
          (loop (cdr E-frames))
          (spew ")")]
         [(list 1 `(trap ,p))
          (spew "(detrap ")
          (loop (cdr E-frames))
          (spew ")")])])))


(define/contract (send-nat-not-in-nat-list nat nats)
  (-> natural? (listof natural?) string?)
  (send-thing (length nats)
              "nat-not-in-nat-list"
              (~a nat " ∉ (" (to-agda-list nats) ")")
              recur-over-len-of-list))

(define (recur-over-len-of-list n spew)
  (spew "\\ { ")

  (for ([i (in-range n)])
    (spew "(")
    (for ([j (in-range i)])
      (spew "there ("))
    (spew "here ()")
    (for ([j (in-range i)])
      (spew ")"))
    (spew ") ; "))
  
  (for ([i (in-range n)])
    (spew "(there "))
  (spew "()")
  (for ([i (in-range n)])
    (spew ")"))
  (spew " }"))

(module+ test
  
  (define (try-recur-over-len-of-list n)
    (define sp (open-output-string))
    (recur-over-len-of-list n (λ (x) (display x sp)))
    (get-output-string sp))

  (check-equal? (try-recur-over-len-of-list 0)
                "\\ { () }")
  (check-equal? (try-recur-over-len-of-list 1)
                "\\ { (here ()) ; (there ()) }")
  (check-equal? (try-recur-over-len-of-list 2)
                "\\ { (here ()) ; (there (here ())) ; (there (there ())) }"))



(define/contract (send-set e)
  (-> any/c string?)
  (send-thing e "SET" "Set" recur-over-set))
  
(define (recur-over-set e spew)
  (match e
    [`(≡e ,_1 ,_2 ,_3 ,p ,q)
     (define pname (send-p p))
     (define qname (send-p q))
     (spew (~a pname " ≡ₑ " qname " # []"))]
    [`(CB (in-hole ,C ,p))
     (define pname (send-in-C-hole `(in-hole ,C ,p)))
     (spew (~a "CB " pname))]
    [`(CB ,p)
     (define pname (send-p p))
     (spew (~a "CB " pname))]
    [`(same ,(? symbol? x) ,(? symbol? y))
     (spew (~a (remove-underscores-for-unicode x)
               " Prop.≡ "
               (remove-underscores-for-unicode y)))]
    [`(∃ ,(? symbol? var) ,(? symbol? type)
         ,a-set)
     (define (do-stuff thing)
       (let loop ([thing thing])
         (match thing
           [`(∧ ,a ,b)
            (spew "(")
            (loop a)
            (spew " × ")
            (loop b)
            (spew ")")]
           [`(→* ,_ ,_ ,(? symbol? a) ,(? symbol? b))
            (spew "(")
            (spew (~a a))
            (spew " ⟶* ")
            (spew (~a b))
            (spew ")")])))
     (spew "(Σ[ ")
     (spew (~a var))
     (spew " ∈ ")
     (spew (~a type))
     (spew " ] ")
     (do-stuff a-set)
     (spew ")")]))

(define/contract (send-stopped p)
  (-> p? string?)
  (send-thing p "H" (~a "halted " (send-p p)) recur-over-stopped))

(define (recur-over-stopped p spew)
  (match p
    [`nothing (spew "hnothin")]
    [`(exit ,n) (spew "hexit ~a" n)]))

(define/contract (send-paused p)
  (-> p? string?)
  (send-thing p "P" (~a "paused " (send-p p)) recur-over-paused))

(define (recur-over-paused p spew)
  (let loop ([p p])
    (match p
      [`pause (spew "ppause")]
      [`(seq ,paused ,q)
       (spew "(pseq ")
       (loop paused)
       (spew ")")]
      [`(par ,paused1 ,paused2)
       (spew "(ppar ")
       (loop paused1)
       (spew " ")
       (loop paused2)
       (spew ")")]
      [`(suspend ,paused ,S)
       (spew "(psuspend ")
       (loop paused)
       (spew ")")]
      [`(trap ,paused)
       (spew "(ptrap ")
       (loop paused)
       (spew ")")]
      [`(loop^stop ,p1 ,p2)
       (spew "(ploopˢ ")
       (loop p1)
       (spew ")")])))

(define/contract (send-done p)
  (-> p? string?)
  (send-thing p "D" (~a "done " (send-p p)) recur-over-done))

(define (recur-over-done p spew)
  (match p
    [(? stopped?) (spew "dhalted ~a" (send-stopped p))]
    [(? paused?) (spew "dpaused ~a" (send-paused p))]))


(define/contract (send-isSigϵ S θ)
  (-> S? θ? string?)
  (send-thing (list S θ 'Sig) "isS"
              (~a "Env.isSig∈ " S " " (send-θ θ)) spew-isSig/isShr/isVar))

(define/contract (send-isShrϵ s θ)
  (-> s? θ? string?)
  (send-thing (list s θ 'Shr) "isS"
              (~a "Env.isShr∈ " s " " (send-θ θ)) spew-isSig/isShr/isVar))

(define/contract (send-isVar∈ x θ)
  (-> x? θ? string?)
  (send-thing (list x θ 'Var) "isS"
              (~a "Env.isVar∈ " x " " (send-θ θ)) spew-isSig/isShr/isVar))

(define (spew-isSig/isShr/isVar id+θ+Sig/Shr/Var spew)
  (match-define (list id θ Sig/Shr/Var) id+θ+Sig/Shr/Var)
  (spew
   "~s"
   (for/fold ([expr `(here Prop.refl)])
             ([i (in-list (sort (get-var-indicies Sig/Shr/Var θ) <))]
              #:when (< i (var->index id)))
     `(there ,expr))))

(define/contract (get-var-indicies Sig/Shr/Var θ)
  (-> (or/c 'Sig 'Shr 'Var) θ? (listof natural?))
  (let loop ([θ θ])
    (match θ
      [`· '()]
      [`{,env-v ,θ}
       (define i/f
         (match env-v
           [`(sig ,S ,status)
            (and (equal? Sig/Shr/Var 'Sig) (var->index S))]
           [`(shar ,s ,ev ,shared-status)
            (and (equal? Sig/Shr/Var 'Shr) (var->index s))]
           [`(var· ,x ,ev)
            (and (equal? Sig/Shr/Var 'Var) (var->index x))]))
       (if i/f
           (cons i/f (loop θ))
           (loop θ))])))

(define/contract (send-all-ready e θ)
  (-> e? θ? string?)
  (send-thing (list e θ)
              "allready"
              (~a "all-ready " (send-e e) " " (send-θ θ))
              recur-over-e-for-all-ready))

(define (recur-over-e-for-all-ready e+θ spew)
  (match-define (list e θ) e+θ)
  (match e
    [`(+ ,sxns ...)
     (spew "aplus (")
     (for ([sxn (in-list sxns)]
           [i (in-naturals)])
       (match sxn
         [(? natural?) (spew "brnum")]
         [(? x?) (spew "(brseq ~a)" (send-isVar∈ sxn θ))]
         [(? s?) (spew "(brshr ~a Prop.refl)" (send-isShrϵ sxn θ))])
       (spew " All.∷ "))
     (spew "All.[])")]))


(define (send-leftmost θ E deriv)
  (send-thing deriv
              "leftmost"
              (~a #:separator " " "left-most" (send-θ θ) (send-E E))
              recur-over-good))

(define (recur-over-good deriv spew)
  (define (send-inner)
    (match deriv
      [(derivation `(good ,theta ,E) _ (cons a r))
       (redex-let
        esterel-eval
        ([(in-hole E1 E) E])
        (send-leftmost theta (term E) a))]))
  (match deriv
    [(derivation `(good ,theta ,E) "hole" (list))
     (spew "lhole")]
    [(derivation `(good ,theta ,E) "seq" (list a))
     (spew "lseq ~a" (send-inner))]
    [(derivation `(good ,theta ,E) "loop^stop" (list a))
     (spew "lloopˢ ~a" (send-inner))]
    [(derivation `(good ,theta ,E) "parl" (list a))
     (spew "lparl ~a" (send-inner))]
    [(derivation `(good ,theta (par ,E ,p)) "par-done" subs)
     (spew "lparrdone" (send-done p) (send-inner))]
    [(derivation `(good ,theta (par ,E ,p)) "par-blocked" (list g blk))
     (spew "lparrblocked ~a ~a" (send-blocked theta p blk) (send-inner))]
    [(derivation `(good ,theta ,E) "suspend" (list a))
     (spew "lsuspend ~a" (send-inner))]
    [(derivation `(good ,theta ,E) "trap" (list a))
     (spew "ltrap ~a" (send-inner))]))

(define (send-blocked-or-done θ p deriv)
  (send-thing deriv
              "blockedordone"
              (~a #:separator " " "blocked-or-done" (send-θ θ) (send-p p))
              (lambda (deriv spew)
                (match deriv
                  [(derivation _ "done" (list))
                   (spew "inj₁ ~a" (send-done p))]
                  [(derivation _ "blocked" (list a))
                   (send-blocked θ p a)]))))

(define (send-blocked θ p blk)
  (send-thing blk
              "isblocked"
              (~a #:separator " "
                  "blocked" (send-θ θ) (send-p p))
              recur-over-blocked))

(define (recur-over-blocked deriv spew)
  (match deriv
    [(derivation `(blocked ,theta (present ,S ,_ ,_)) "present" _)
     (spew "bsig-exists ~a ~a ~a"
           (get-signal S)
           (send-isSigϵ theta S)
           "Prop.refl")]
    [(derivation `(blocked ,theta (par ,p ,q)) "par-both" (list b1 b2))
     (spew "bpar-both ~a ~a"
           (send-blocked theta p b1)
           (send-blocked theta q b2))]
    [(derivation `(blocked ,theta (par ,p ,q)) "parl" (list b))
     (spew "bpar-left ~a ~a"
           (send-done p)
           (send-blocked theta q b))]
    [(derivation `(blocked ,theta (par ,p ,q)) "parr" (list b))
     (spew "bpar-left ~a ~a"
           (send-blocked theta p b)
           (send-done q))]
    [(derivation `(blocked ,theta (seq ,p ,q)) "seq" (list b))
     (spew "bseq ~a"
           (send-blocked theta p b))]
    [(derivation `(blocked ,theta (loop^stop ,p ,q)) "loop^stop" (list b))
     (spew "bloopˢ ~a"
           (send-blocked theta p b))]
    [(derivation `(blocked ,theta (suspend ,p ,S)) "suspend" (list b))
     (spew "bsusp ~a"
           (send-blocked theta p b))]
    [(derivation `(blocked ,theta (trap ,p)) "trap" (list b))
     (spew "btrap ~a"
           (send-blocked theta p b))]
    [(derivation `(blocked ,theta (shared ,s := ,e ,p)) "shared" (list be))
     (spew "bshared ~a"
           (send-blocked-e theta e be))]
    [(derivation `(blocked ,theta (<= ,s ,e)) "set-shared" (list be))
     (spew "bsset ~a"
           (send-blocked-e theta e be))]
    [(derivation `(blocked ,theta (var ,x := ,e ,p)) "var" (list be))
     (spew "bvar ~a"
           (send-blocked-e theta e be))]
    [(derivation `(blocked ,theta (:= ,x ,e)) "set-seq" (list be))
     (spew "bxset ~a"
           (send-blocked-e theta e be))]))

(define (send-blocked-e θ e be)
  (send-thing be
              "blockede"
              (~a #:separator " "
                  "blocked-e" (send-θ θ) (send-e e))
              recure-over-blocked-e))
(define (recure-over-blocked-e deriv spew)
  (match deriv
    [(derivation `(blocked-e ,θ (+ ,args ...)) _ _)
     (let loop ([args args])
       (define (there l)
         (spew "(there ")
         (loop l)
         (spew ")"))
       (match args
         [(cons a b)
          #:when (s? a)
          (match (term (θ-ref ,θ ,a))
            [`(shar ,_ ,_ ,st)
             #:when (not (eq? st 'ready))
             (define ctor (if (eq? a 'new) "bbshr-new" "bbshr-old"))
             (spew "(here (~a ~a ~a))"
                   ctor
                   (send-isShrϵ θ a)
                   "Prop.refl")]
            [_ (there b)])]
         [(cons _ b) (there b)]))]))