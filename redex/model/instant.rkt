#lang racket

(require redex/reduction-semantics
         (only-in esterel-calculus/cross-tests/send-lib clean-up-p θ-to-hash)
         esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/potential-function
         (prefix-in standard: esterel-calculus/redex/model/reduction)
         (prefix-in calculus: esterel-calculus/redex/model/calculus))
(module+ test (require rackunit))

(provide instant current-check-standard-implies-calculus
         (contract-out
          [run-instants (-> p?
                            (listof (listof env-v?))
                            (values (or/c #f p?) (listof (set/c S?))))]))

(define p? (redex-match? esterel-eval p))
(define env-v? (redex-match? esterel-eval env-v))
(define S? (redex-match? esterel-eval S))

(define current-check-standard-implies-calculus (make-parameter #t))

(define-metafunction esterel-eval
  instant : p (env-v ...) -> (p (S ...)) or #f
  [(instant p (env-v ...))
   (p_*
    (get-signals complete))
   (where (complete)
          ,(apply-reduction-relation*/enforce-single standard:R `(setup p (env-v ...))))
   (where p_* (next-instant complete))]
  [(instant p (env-v ...))
   #f
   (where (p_* ...) ,
          (apply-reduction-relation*/enforce-single standard:R `(setup p (env-v ...))))])

(define (go-to-end-of-instant p env-vs)
  (car (apply-reduction-relation*/enforce-single standard:R `(setup ,p ,env-vs))))

(define complete? (redex-match esterel-eval complete))

(define (run-instants p env-vss)
  (define final-p #f)
  (define emitted-signals
    (let loop ([p p]
               [env-vss env-vss])
      (cond
        [(null? env-vss)
         '()]
        [else
         (define end-of-instant-p (go-to-end-of-instant p (car env-vss)))
         (cond
           [(complete? end-of-instant-p)
            (set! final-p end-of-instant-p)
            (define next-p (term (next-instant ,end-of-instant-p)))
            (define signals (term (get-signals ,end-of-instant-p)))
            (cons (list->set signals)
                  (loop next-p (cdr env-vss)))]
           [else
            (set! final-p #f)
            '()])])))
  (values final-p emitted-signals))

(module+ test
  (check-equal? (term (instant (ρ · (signal S pause)) ()))
                (term ((ρ ((sig S unknown) ·) nothing) ())))
  (check-equal? (term (instant (ρ · (signal S (emit S))) ()))
                (term ((ρ ((sig S unknown) ·) nothing) (S)))))

(define (apply-reduction-relation*/enforce-single R p)
  (match (apply-reduction-relation R p)
    [(list) (list p)]
    [(list q)
     (when (current-check-standard-implies-calculus)
       (unless (standard-implies-calculus p)
         (error 'instant
                (string-append
                 "the term:\n~a\nreduces in the standard reduction"
                 " but doesn't have a corresponding reduction"
                 " in the calculus")
                (pretty-format p #:mode 'write))))
     (apply-reduction-relation*/enforce-single R q)]
    [(list* q)
     (error 'reduction "shouldn't happen! diverged on ~a\n" q)]))

(define (standard-implies-calculus _p)

  ;; I believe this is called only to normalize the θs
  ;; it would be better to make a separate function
  ;; that just does that, as the clean-up function is
  ;; part of the "generate agda code" machinery and
  ;; it does other things, too, that we don't want here
  (define p (clean-up-p _p))
  
  (for/and ([std-q+name (in-list (apply-reduction-relation/tag-with-names standard:R p))])
    (define name (list-ref std-q+name 0))
    (define std-q (list-ref std-q+name 1))
    (case name
      [("absence" "readyness")
       ;; these rules need multiple calculus steps in the calculus
       ;; to match up to a single standard reduction step. to
       ;; find the right steps, we consider only steps in the
       ;; calculus that take us
       ;; directly the way that the standard reduction did
       (define (find-vars-that-changed p q)
         (define p-θ-as-hash (θ-to-hash (list-ref p 1)))
         (define q-θ-as-hash (θ-to-hash (list-ref q 1)))
         (for/set ([(var rhs) (in-hash p-θ-as-hash)]
                   #:unless (equal? rhs (hash-ref q-θ-as-hash var)))
           var))

       (define std-vars-that-changed (find-vars-that-changed p std-q))
       (define calc-q
         (let loop ([p p]
                    [vars-to-change std-vars-that-changed])
           (cond
             [(set-empty? vars-to-change) p]
             [else
              (define next-calc-steps (apply-reduction-relation/tag-with-names calculus:R p))
              (define chosen-calc-q+vars-that-changed-candidates
                (filter
                 values
                 (for/list ([name+calc-q (in-list next-calc-steps)]
                            #:when (equal? name (list-ref name+calc-q 0)))
                   (define calc-q (list-ref name+calc-q 1))
                   (define calc-vars-that-changed (find-vars-that-changed p calc-q))
                   (cond
                     [(and (not (set-empty? calc-vars-that-changed))
                           (subset? calc-vars-that-changed vars-to-change))
                      (vector calc-q calc-vars-that-changed)]
                     [else #f]))))
              (cond
                ;; here we found a calculus reduction that changed some
                ;; vars in the outer (ρ θ ...) and they are vars that
                ;; the standard reduction also changed. So try to change
                ;; more by looping
                [(pair? chosen-calc-q+vars-that-changed-candidates)
                 (define chosen-calc-q+vars-that-changed
                   (car chosen-calc-q+vars-that-changed-candidates))
                 (loop (vector-ref chosen-calc-q+vars-that-changed 0)
                       (set-subtract vars-to-change
                                     (vector-ref chosen-calc-q+vars-that-changed 1)))]
                [else
                 ;; here we didn't find one, so just stick with what we got
                 ;; (I think this will always be the wrong term)
                 p])])))
       (same-p? std-q calc-q)]
      [("parl" "parr")
       ;; if a par-left or par-right rule fires, we apply the
       ;; par-swap rule (all possible ways) and then look at
       ;; how those terms (plus the original term) reduces.
       (define rewritten-terms+names
         (apply-reduction-relation/tag-with-names
          calculus:R
          p))
       (define par-swapped-variants-of-p
         (filter
          values
          (for/list ([rewritten-term+name (in-list rewritten-terms+names)])
            (define name (list-ref rewritten-term+name 0))
            (define rewritten-term (list-ref rewritten-term+name 1))
            (and (equal? name "par-swap")
                 rewritten-term))))
       (for/or ([term-to-try (cons p par-swapped-variants-of-p)])
         (for/or ([calc-q (in-list (apply-reduction-relation calculus:R term-to-try))])
           (same-p? std-q calc-q)))]
      [else
       (for/or ([calc-q (in-list (apply-reduction-relation calculus:R p))])
         (same-p? std-q calc-q))])))

;; compares `p`s, but normalizes and ρ's before comparing them
(define (same-p? p q)
  (let loop ([p p] [q q])
    (match* (p q)
      [(`(ρ ,θ1 ,p) `(ρ ,θ2 ,q))
       (and (equal? (θ-to-hash θ1) (θ-to-hash θ2))
            (loop p q))]
      [((? list?) (? list?))
       (and (= (length p) (length q)))
       (for/and ([p (in-list p)]
                 [q (in-list q)])
         (loop p q))]
      [(p q) (equal? p q)])))

(module+ test
  (require rackunit)
  (check-true (standard-implies-calculus (term (ρ ((sig Sr absent) ((sig Sg unknown) ·)) (exit 0)))))
  (check-true (standard-implies-calculus (term (ρ ((sig Sr unknown) ((sig Sg unknown) ·)) (exit 0)))))
  (check-true (standard-implies-calculus (term (trap (loop pause)))))
  (check-true (standard-implies-calculus (term (ρ ((sig SM unknown) ·) (loop (if xLd nothing pause))))))

  (check-true
   (standard-implies-calculus
    (term (ρ
           ((sig S$D unknown)
            ((sig |S)| present)
             ((sig S/f unknown)
              ((sig S4 unknown)
               ((sig SD unknown)
                ((sig SR unknown)
                 ((sig SU unknown)
                  ((sig SV unknown)
                   ((sig SZ unknown)
                    ((sig Sd unknown)
                     ((sig Sg unknown)
                      ((sig Sr unknown)
                       ((sig Ss unknown)
                        ((sig |S{| unknown) ·))))))))))))))
           (present
            S$D
            (shared s33131 := (+) (suspend nothing |S)|))
            (suspend (signal S33132 (par pause nothing)) S$D))))))

  (redex-check standard:esterel-standard p
               (standard-implies-calculus (term p))
               #:source standard:R))
