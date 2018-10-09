#lang racket

;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require "send-lib.rkt"
         redex/reduction-semantics)

(module+ test (require rackunit))

(provide send-p send-e send-θ send-set
         send-E-decomposition send-E
         send-nat-not-in-nat-list
         θ-to-hash)

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
      [`(ρ ,θ ,p)
       (define θ-id (send-θ θ))
       (spew "(ρ ~a · " θ-id)
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
