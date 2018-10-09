#lang racket

;; WARNING! QUASIQUOTE IS ACTUALLY QUASIQUOTE IN THIS FILE

(require (except-in "../redex/model/shared.rkt" quasiquote)
         "../redex/model/calculus.rkt"
         "../redex/test/generator.rkt"
         (only-in "../redex/test/binding.rkt" esterel-L)
         racket/runtime-path
         redex/reduction-semantics
         (for-syntax syntax/parse))
(module+ test (require rackunit))

(provide S? s? x? p? e? θ? E? hole? stopped? paused? L?
         send-thing
         var->index
         θ-to-hash
         log-rule report-log
         clean-up-p clean-up-θ
         to-agda-list

         log-S log-s log-x

         add-to-top-level-comment
         establish-context
         run-agda
         scratch-directory

         (struct-out premises)
         add-prefix
         remove-underscores-for-unicode)

(define-syntax (define-extended stx)
  (syntax-parse stx
    [(_ pred-name:id pred)
     #'(define pred-name
         (let ([pred-x pred])
           (λ (x)
             (pred-x (->concrete x)))))]))

(define S? (redex-match? esterel-L S))
(define s? (redex-match? esterel-L s))
(define x? (redex-match? esterel-L x))
(define-extended p? (redex-match? esterel-L p))
(define e? (redex-match? esterel-L e))
(define θ? (redex-match? esterel-L θ))
(define E? (redex-match? esterel-L E))
(define hole? (redex-match? esterel-L hole))
(define-extended stopped? (redex-match? esterel-L stopped))
(define-extended paused? (redex-match? esterel-L paused))
(define L? (redex-match? esterel-L L))

(define esterel-eval-p? (redex-match? esterel-eval p))
(define esterel-eval-e? (redex-match? esterel-eval e))
(define esterel-eval-θ? (redex-match? esterel-eval θ))

(define (->concrete x)
  (let loop ([x x])
    (match x
      [`(∀x ,abstract ,concrete) concrete]
      [(? list?) (map loop x)]
      [_ x])))

(define rules-ht (make-hash))
(define (log-rule label p)
  (define size
    (let loop ([p p])
      (cond
        [(list? p)
         (apply +
                1  ;; count this expression form
                -1 ;; uncount its keyword
                (map loop p))]
        [else 1])))
  (define old (hash-ref rules-ht label '(0 . 0)))
  (hash-set! rules-ht label (cons (+ 1 (car old)) (+ size (cdr old)))))

(define (report-log)
  (printf "\nrule tests generated:\n")
  (pretty-write
   (sort
    (for/list ([k (in-list (sort (reduction-relation->rule-names R*)
                                 symbol<?))])
      (define v (hash-ref rules-ht (symbol->string k) '(0 . 0)))
      (list k
            'count (car v)
            'avg-size (if (zero? (car v)) #f (round (/ (cdr v) (car v))))))
    <
    #:key caddr))
  (printf "\n")
  (flush-output))

(define thing-counters (make-hash))

(define top-level-comments '())
(define var-table (make-hash))

(define current-level (make-parameter 0))
(define current-things-to-send (make-parameter #f))
(define current-things-sent-cache (make-parameter (make-hash)))
(define (get-things-to-send)
  (unless (current-things-to-send)
    (error 'send-lib.rkt "establish-context not called"))
  (current-things-to-send))

(define (add-to-top-level-comment a-comment)
  (set! top-level-comments (cons a-comment top-level-comments)))

(define-syntax-rule
  (establish-context filename e1 e ...)
  (establish-context/proc filename (λ () e1 e ...)))
(define (establish-context/proc where-it-goes thunk)
  (define result
    (parameterize ([current-things-to-send (box '())]
                   [current-things-sent-cache (hash-copy (current-things-sent-cache))])

      (define thunk-result
        (parameterize ([current-level (+ (current-level) 2)])
          (thunk)))

      (cond
        [(zero? (current-level))
         ;; this means we're finishing the top-level;
         ;; where-it-goes should be the name of a file
         (generate-scratch where-it-goes)
         (reset-things-to-send)
         #f]
        [else
         ;; this means we're generating a `let`; where-it-goes
         ;; is a box we fill in with some agda code (in a string)
         (define sp (open-output-string))
         (for ([str (in-list (premises-strs where-it-goes))]
               [i (in-naturals)])
           (fprintf sp "\n")
           (send-indent sp)
           (fprintf sp "~a ->" str))
         (fprintf sp "\n")
         (send-indent sp)
         (fprintf sp "(let\n")
         (parameterize ([current-level (+ (current-level) 2)])
           (for ([thing-to-send (in-list (reverse (unbox (get-things-to-send))))])
             (thing-to-send sp)))
         (send-indent sp)
         (fprintf sp "in ~a)" thunk-result)
         (get-output-string sp)])))
  (when result
    (define (recur-over/premises _ spew)
      (spew (premises-proof where-it-goes))
      (spew "\n"))
    (send-thing (gensym) ;; always unique (hack?)
                (premises-prefix where-it-goes)
                result
                recur-over/premises)))

(define-struct premises (prefix strs proof))

(define (send-indent port)
  (for ([i (in-range (current-level))])
    (display #\space port)))

(define (send-thing thing prefix type recur-over)
  (define key (cons thing type))
  (cond
    [(hash-ref (current-things-sent-cache) key #f)
     => values]
    [else
     (hash-set! thing-counters prefix (+ (hash-ref thing-counters prefix 0) 1))
     (define name (~a prefix (hash-ref thing-counters prefix)))
     (define thing-to-send void)
     (define (spew . stuff)
       (set! thing-to-send
             (let ([thing-to-send thing-to-send])
               (λ (port)
                 (thing-to-send port)
                 (apply fprintf port stuff)))))
     (recur-over thing spew)
     (set-box! (current-things-to-send)
               (cons
                (λ (port)
                  (send-indent port)
                  (fprintf port "~a : ~a\n" name type)
                  (send-indent port)
                  (fprintf port "~a = " name)
                  (thing-to-send port)
                  (fprintf port "\n"))
                (unbox (current-things-to-send))))
     (hash-set! (current-things-sent-cache) key name)
     name]))
(define (reset-things-to-send)
  (set! thing-counters (make-hash))
  (set! top-level-comments '())
  (set! var-table (make-hash)))

(define (agda-safe-var? var)
  (and (symbol? var)
       (and
        ;; no clue if this check is too strict; it is intended to allow
        ;; variables thru without modification that are likely to be valid
        ;; agda identifiers
        (regexp-match #rx"^[a-zA-Z][a-zA-Z0-9]*$"
                      (symbol->string var))
        (not (member var '(Ss sig shr Set seq snd suc sym))))))

(define/contract (var->index var)
  (-> (or/c S? s? x?) natural?)
  (hash-ref var-table
            var
            (λ () (error 'var->index "unknown var: ~a" var))))
(define/contract (log-S S) (-> (and/c S? agda-safe-var?) void?) (log-var S "ₛ" "Signal"))
(define/contract (log-s s) (-> (and/c s? agda-safe-var?) void?) (log-var s "ₛₕ" "SharedVar"))
(define/contract (log-x x) (-> (and/c x? agda-safe-var?) void?) (log-var x "ᵥ" "SeqVar"))
(define var-rewrite-table (make-hash))
(define (log-var agda-safe-var suffix type)
  (unless (hash-ref var-table agda-safe-var #f)
    (define n (hash-count var-table))
    (hash-set! var-table agda-safe-var n)
    (when (current-things-to-send)
      ;; only set these up to send when we're actually sending
      ;; things to agda; sometimes we call this just to
      ;; normalize the variable names
      (set-box! (get-things-to-send)
                (cons
                 (λ (port)
                   (send-indent port)
                   (fprintf port "~a : ~a\n" agda-safe-var type)
                   (send-indent port)
                   (fprintf port "~a = ~a ~a\n" agda-safe-var n suffix))
                 (unbox (get-things-to-send)))))))
(define/contract (var->agda-safe-var var)
  (-> (or/c S? s? x? (list/c '∀x any/c (or/c S? s? x?))) agda-safe-var?)
  (match var
    [`(∀x ,abstract ,concrete) abstract]
    [_
     (define safe-var
       (cond
         [(agda-safe-var? var) var]
         [else
          (define s-var (symbol->string var))
          (hash-ref! var-rewrite-table var
                     (λ () (string->symbol (~a (string-ref s-var 0)
                                               (hash-count var-rewrite-table)))))]))
     (when (S? safe-var) (log-S safe-var))
     (when (s? safe-var) (log-s safe-var))
     (when (x? safe-var) (log-x safe-var))
     safe-var]))

(define prefix #<<--
module _ where

open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List using (List ; _∷_ ; [])
open import Data.List.All using (All)
open import Data.List.Any
open import Data.Maybe using (just ; nothing)
open import Data.Empty
open import Data.Nat as Nat using (ℕ ; suc)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (⌊_⌋ ; from-yes)
import Relation.Binary.PropositionalEquality as Prop
open import context-properties
open import utility
open import calculus
open import sn-calculus
open import blocked using (blocked-dec)
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.Binding
open import Esterel.Lang.PotentialFunction
open import Esterel.Context
open import Esterel.Environment as Env
open import Esterel.Variable.Signal as Signal using (Signal ; _ₛ)
open import Esterel.Variable.Sequential as SeqVar using (SeqVar ; _ᵥ)
open import Esterel.Variable.Shared as ShVar using (SharedVar ; _ₛₕ)
open import Esterel.CompletionCode as Code using () renaming (CompletionCode to Code)

--
  )

(define-runtime-path scratch-directory "scratch")
(unless (directory-exists? scratch-directory) (make-directory scratch-directory))
(define added-prefixes '())
(define (add-prefix p) (set! added-prefixes (cons p added-prefixes)))

;; generates the collected agda code and then resets the
;; global variables to prepare for any future possible sends.
(define (generate-scratch without-scratch-filename)
  (define filename (build-path scratch-directory without-scratch-filename))
  (call-with-output-file filename
    (λ (port)
      (fprintf port "{-\nthis file generated by send-lib.rkt\n\n")
      (for ([comment (in-list (reverse top-level-comments))])
        (fprintf port "~a\n" comment))
      (fprintf port "\n-}\n\n")
      (fprintf port "~a" prefix)
      (for ([added-prefix (in-list added-prefixes)])
        (fprintf port "~a\n" added-prefix))
      (fprintf port "\n")
      (for ([thing-to-send (in-list (reverse (unbox (get-things-to-send))))])
        (thing-to-send port)))
    #:exists 'truncate))

;; run-agda : path -> void
;; runs agda on the filename in the directory `scratch`
(define (run-agda filename)
  (define-values (in out) (make-pipe))
  (thread
   (λ ()
     (for ([l (in-lines in)])
       (unless (or (regexp-match #rx"^ *Skipping" l)
                   (regexp-match #rx"^ *Checking scratch" l)
                   (regexp-match #rx"^ *Finished scratch" l))
         (display l)
         (newline)
         (flush-output)))))
  (define result
    (parameterize ([current-output-port out]
                   [current-directory scratch-directory])
      (system (format "agda ~a" filename))))
  (close-output-port out)
  (unless result (error 'run-agda "failed"))
  (printf "agda finished\n")
  (flush-output))

;; does various cleanup operations:
;; - replaces all variables with agda-safe variables
;; - removes duplicate variables in ρ
;; - removes rfunc and rvalue and dec
(define/contract (clean-up-p p)
  (-> (or/c esterel-eval-p? p?) p?)
  (let loop ([p p])
    (match p
      [`(∀x ,abstract ,concrete) `(∀x ,abstract ,concrete)]
      [`nothing p]
      [`pause p]
      [`(signal ,S ,p) `(signal ,(var->agda-safe-var S) ,(loop p))]
      [`(present ,S ,p ,q) `(present ,(var->agda-safe-var S) ,(loop p) ,(loop q))]
      [`(emit ,S) `(emit ,(var->agda-safe-var S))]
      [`(par ,p ,q) `(par ,(loop p) ,(loop q))]
      [`(loop ,p) `(loop ,(loop p))]
      [`(seq ,p ,q) `(seq ,(loop p) ,(loop q))]
      [`(loop^stop ,p ,q) `(loop^stop ,(loop p) ,(loop q))]
      [`(suspend ,p ,S) `(suspend ,(loop p) ,(var->agda-safe-var S))]
      [`(trap ,p) `(trap ,(loop p))]
      [`(exit ,n) `(exit ,n)]
      [`(shared ,s := ,e ,p) `(shared ,(var->agda-safe-var s) := ,(clean-up-e e) ,(loop p))]
      [`(<= ,s ,e) `(<= ,(var->agda-safe-var s) ,(clean-up-e e))]
      [`(var ,x := ,e ,p) `(var ,(var->agda-safe-var x) := ,(clean-up-e e) ,(loop p))]
      [`(:= ,x ,e) `(:= ,(var->agda-safe-var x) ,(clean-up-e e))]
      [`(if ,x ,p ,q) `(if ,(var->agda-safe-var x) ,(loop p) ,(loop q))]
      [`(ρ ,θ ,p) `(ρ ,(clean-up-θ θ) ,(loop p))])))

(define/contract (clean-up-e e)
  (-> (or/c esterel-eval-e? e?) e?)
  (match e
    [`(dec)
     `(+ ,(random 2))]
    [`(dec ,s/l ,_ ...)
     `(+ 0 ,(clean-up-s/l s/l))]
    [`(,f ,s/l ...)
     `(,(match f
          [`(rfunc ,_) '+]
          [_ f])
       ,@(for/list ([s/l (in-list s/l)]

                    ;; limit arity to 2
                    [_ (in-range 2)])
           (clean-up-s/l s/l)))]))

(define (clean-up-s/l s/l)
  (match s/l
    [(? s?) (var->agda-safe-var s/l)]
    [(? x?) (var->agda-safe-var s/l)]
    [(? natural?) s/l]
    [`(rvalue ,_) (random 10)]))

(define/contract (clean-up-θ θ)
  (-> (or/c esterel-eval-θ? θ?) θ?)
  (define already-seen (make-hash))
  (let loop ([θ θ])
    (match θ
      [`· `·]
      [`{,env-v ,θ}
       (let/ec k
         (define (dup-check/agda-safe var)
           (define agda-safe-var (var->agda-safe-var var))
           (cond
             [(hash-ref already-seen agda-safe-var #f)
              (k (loop θ))]
             [else
              (hash-set! already-seen agda-safe-var #t)
              agda-safe-var]))
         `{,(match env-v
              [`(sig ,S ,status) `(sig ,(dup-check/agda-safe S) ,status)]
              [`(shar ,s ,ev ,shared-status)
               `(shar ,(dup-check/agda-safe s) ,(clean-up-ev ev) ,shared-status)]
              [`(var· ,x ,ev)
               `(var· ,(dup-check/agda-safe x)
                      ,(clean-up-ev ev))])
           ,(loop θ)})])))

(define (clean-up-ev ev)
  (match ev
    [`(rvalue ,any) (random 10)]
    [_ ev]))

(module+ test
  (check-equal? (clean-up-θ `((shar sk 1 old) ((shar sn 1 old) ((shar sk 1 old) ·))))
                `((shar sk 1 old) ((shar sn 1 old) ·))))

(define/contract (θ-to-hash θ)
  (-> θ? hash?)
  (define ht (make-hash))
  (let loop ([θ θ])
    (match θ
      [`· '()]
      [`{,env-v ,θ}
       (match env-v
         [`(sig ,S ,status)
          (hash-set! ht S status)
          (var->index S)]
         [`(shar ,s ,ev ,shared-status)
          (hash-set! ht s (cons ev shared-status))]
         [`(var· ,x ,ev)
          (hash-set! ht x ev)])
       (loop θ)]))
  ht)

(define/contract (to-agda-list ~a-able)
  (-> (listof any/c) string?)
  (apply
   string-append
   (for/fold ([lst '("[]")])
             ([nat (in-list (reverse ~a-able))])
     (list* (~a nat) " ∷ " lst))))

(module+ test
  (check-equal? (to-agda-list '()) "[]")
  (check-equal? (to-agda-list '(1)) "1 ∷ []")
  (check-equal? (to-agda-list '(1 2 3)) "1 ∷ 2 ∷ 3 ∷ []"))


(define (remove-underscores-for-unicode var-maybe-with-underscores)
  (match (regexp-split #rx"_" (symbol->string var-maybe-with-underscores))
    [(list before after)
     (string->symbol
      (string-append
       before
       (match after
         ["1" "₁"]
         ["2" "₂"]
         ["3" "₃"])))]
    [else var-maybe-with-underscores]))

(module+ test
  (check-equal? (remove-underscores-for-unicode 'x) 'x)
  (check-equal? (remove-underscores-for-unicode 'x_1) 'x₁))
