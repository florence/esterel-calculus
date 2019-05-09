#lang racket
(require racket/require
         esterel-calculus/redex/rackunit-adaptor
         rackunit
         (subtract-in redex/reduction-semantics
                      esterel-calculus/redex/rackunit-adaptor)
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/calculus
         esterel-calculus/redex/test/generator)

(define (GOness-maintained? p)
  (define p-has-GO? (has-GO? p))
  (define steps (apply-reduction-relation ⟶ p))
  (for/and ([s (in-list steps)])
    (equal? p-has-GO? (has-GO? s))))

(define (has-GO? p)
  (redex-match? esterel-eval
                (in-hole C (ρ θ GO p))
                p))


(define tracking-table
  (make-hash
   (map (lambda (x) (cons x 0))
        '(WAIT
          GO
          sig
          nothing
          pause
          seq
          par
          trap
          exit
          signal
          suspend
          present
          emit
          loop
          shared
          <=
          var
          :=
          if
          ρ))))
(define largest #f)
(define (track! t)
  (define (inc! s)
    (when (hash-has-key? tracking-table s)
      (hash-update!
       tracking-table
       s
       add1)))
  (match t
    [(? list? body)
     (for-each track! body)]
    [(? symbol? s)
     (inc! s)]
    [else (void)]))

(define (size e)
  (match e
    [(? list?)
     (apply + 1 (map size e))]
    [else 1]))
     
(define (update-largest! e)
  (when (or (not largest)
            (> (size e) (size largest)))
    (set! largest e)))

(check-true
 (GOness-maintained?
  (term
   (ρ · WAIT (ρ · GO nothing)))))
 
(redex-check
 esterel-check
 ((name p-check+θ
        (in-hole (cross p-check+θ)
                 (ρ θ-check_1 A_1
                    (in-hole
                     (cross p-check+θ)
                     (ρ θ-check_2 A_2
                        (in-hole
                         (cross p-check+θ)
                         (ρ θ-check_3 A_3
                            p-check+θ_1)))))))
  () () (() ...))
 (begin
   (track! (term p-check+θ))
   (update-largest! (term p-check+θ))
   (GOness-maintained? (term p-check+θ)))
 #:prepare fixup/allow-empty-signals)
(redex-check
 esterel-check
 ((name p-check+θ
        (in-hole
         E-check+θ_1
         (ρ θ-check_1 A_1
            (in-hole
             E-check+θ_2
             (ρ θ-check_2 A_2
                (in-hole
                 E-check+θ_3
                 (ρ θ-check_3 A_3
                    p-check+θ_1)))))))
  () () (() ...))
 (begin
   (track! (term p-check+θ))
   (update-largest! (term p-check+θ))
   (GOness-maintained? (term p-check+θ)))
 #:prepare
 (curry fixup/allow-empty-signals #:low-signal-chance 0))
;(pretty-print tracking-table)
;largest
