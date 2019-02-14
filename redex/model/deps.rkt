#lang racket
(require pict
         pict/code
         ppict/tag
         (for-syntax syntax/parse racket/sequence racket/syntax)
         racket/hash)
  
(define-syntax taged-code
  (syntax-parser
    [(_ x)
     (define-values (pict term hash defs)
       (let loop ([x #'x]
                  [hash #'(hasheq)]
                  [defs null])
         (syntax-parse x
           #:datum-literals (present emit)
           [((~and P present) S p q)
            #:with tag (generate-temporary)
            #:with term (generate-temporary)
            #:with x (syntax/loc #'P (tag-pict (code P) tag))
            #:with y (quasisyntax/loc #'P (#,#'unsyntax x))
            (define-values (ppic pterm phash pdefs)
              (loop #'p hash defs))
            (define-values (qpic qterm qhash qdefs)
              (loop #'q phash pdefs))
            (values (quasisyntax/loc this-syntax (y S #,ppic #,qpic))
                    #',term
                    #`(hash-set #,qhash term tag)
                    (list*
                     #'(define tag (gensym))
                     #`(define term `(present #,(syntax-e #'S) #,pterm #,qterm))
                     qdefs))]
           [((~and E emit) S)
            #:with tag (generate-temporary)
            #:with term (generate-temporary)
            #:with E* (quasisyntax/loc #'E (#,#'unsyntax (tag-pict (code E) tag)))
            (values (quasisyntax/loc this-syntax (E* S))
                    #',term
                    #`(hash-set #,hash term tag)
                    (list*
                     #'(define tag (gensym))
                     #`(define term `(emit S))
                     defs))]
           [(any ...)
            (define-values (inpict interm inhash indefs)
              (for/fold ([pict null]
                         [term null]
                         [hash hash]
                         [defs defs])
                        ([x (in-syntax #'(any ...))])
                (define-values (pr tr hr dr) (loop x hash defs))
                (values (cons pr pict) (cons tr term) hr dr)))
            (values
             (datum->syntax this-syntax (reverse inpict) this-syntax)
             (reverse interm)
             inhash
             indefs)]
           [atom
            (values #'atom #'atom hash defs)])))
     #`(let ()
         #,@(reverse defs)
         (values (code #,pict)
                 `#,term
                 #,hash))]))

(define (flow-graph term)
  (define-values (r _) (control-flow term empty))
  (define sq (emit-dependencies term))
  (hash-union/append sq r))

(define (control-flow term context)
  (match term
    [`(present ,S ,p ,q)
     (define-values (Sp Kp)
      (control-flow p (list term) #;(cons term context)))
     (define-values (Sq Kq)
       (control-flow q (list term) #;(cons term context)))
     (values (hash-union/append (hash-union/append Sp Sq)
                                (for/hasheq ([t (in-list context)])
                                  (values t (list term))))
             (hash-union/append Kp Kq))]
    [`(emit ,S)
     (values
       (for/hasheq ([t (in-list context)])
         (values t (list term)))
       (hash 0 context))]
    [`nothing
     (values (hasheq) (hash 0 context))]
    [`pause
     (values (hasheq) (hash 1 context))]
    [`(exit ,n)
     (values (hasheq) (hash (+ n 2) context))]
    [`(trap ,p)
     (define-values (S K) (control-flow p context))
     (values S (↓k K))]
    [`(par ,p ,q)
     (define-values (Sp Kp)
      (control-flow p context))
     (define-values (Sq Kq)
       (control-flow q context))
     (values (hash-union/append Sp Sq)
             (hash-union/append Kp Kq))]
    [`(seq ,p ,q)
     (define-values (Sp Kp)
       (control-flow p context))
     (define-values (Sq Kq)
       (control-flow
        q
        (append context (hash-ref Kp 0 empty))))
     (values (hash-union/append Sp Sq)
             (hash-union/append (hash-remove Kp 0) Kq))]
    [`(loop ,p)
     ;; the lack of loop control depenencies
     ;; comes from the fact that loops *cannot* instantaniously terminate.
     ;; Therefore control decisions they make are not carried forward
     ;; in the given instant.
     
     ;; but... Is there a difference between single instant control and multi-instant
     ;; PDGs?
     (control-flow p context)]
    [`(signal ,S ,p)
     (control-flow p context)]))

(define (↓k map)
  (for/fold ([m2 (hash)])
            ([(k v) (in-hash map)])
    (match k
      [0 (hash-append m2 0 v)]
      [1 (hash-set m2 1 v)]
      [2 (hash-append m2 0 v)]
      [n (hash-set m2 (sub1 n) v)])))



(define (emit-dependencies t)
  (define em (get-emits t))
  (define ps (get-presents t))
  (for*/fold ([h (hasheq)])
             ([(S es) (in-hash em)]
              [e (in-list es)]
              [p (in-list (hash-ref ps S empty))])
    (hash-cons h e p)))

(define (get-emits e)
  (match e
    [`(emit ,S)
     (hasheq S (list e))]
    [(list any ...)
     (for/fold ([h (hasheq)])
               ([i (in-list any)])
       (hash-union/append h (get-emits i)))]
    [atom (hasheq)]))

(define (get-presents e)
  (match e
    [`(present ,S ,p ,q)
     (hash-union/append
      (hasheq S (list e))
      (hash-union/append (get-presents p)
                         (get-presents q)))]
    [(list any ...)
     (for/fold ([h (hasheq)])
               ([i (in-list any)])
       (hash-union/append h (get-presents i)))]
    [atom (hasheq)]))
     
     

(define (hash-cons h k v)
  (hash-update h
               k
               (lambda (l) (cons v l))
               empty))

(define (hash-append h k v)
  (hash-update h
               k
               (lambda (l) (append v l))
               empty))

(define (hash-union/append h1 h2)
  (hash-union h1 h2 #:combine append))

(define (find-tag* p t)
  (define x (find-tag p t))
  (unless x (error 'find-tag "could not find tag ~a" t))
  x)

(define (draw-deps pict code map)
  (for*/fold ([p pict])
             ([(from tos) (in-hash (flow-graph code))]
              [to (in-list tos)])
    (pin-arrow-line
     10
     p
     (find-tag* p (hash-ref map to))
     lc-find
     (find-tag* p (hash-ref map from))
     lc-find)))

(define-syntax deps
  (syntax-parser
    [(_ code)
     #'(let-values ([(a b c) (taged-code code)])
         (draw-deps a b c))]))

(deps (seq (emit S)
           (present S nothing nothing)))
(deps (present S
               (emit S)
               nothing))

(scale
 (deps
  (signal S1
    (present S1
             (signal S2
               (seq (emit S2)
                    (present S2
                             nothing
                             (emit S1))))
             nothing)))
 3)
(scale
 (deps
  (signal S2
    (seq (emit S2)
         (present S2
                  nothing
                  (emit S1)))))
 3)

(scale
 (deps
  (par
   (seq pause (seq (present S1 nothing nothing) (emit S2)))
   (seq pause (seq (present S2 nothing nothing) (emit S1)))))
 2)

(scale
 (deps
  (par
   (seq pause (present S1
                       (emit S2)
                       nothing))
   (seq pause (present S2
                       (emit S1)
                       nothing))))
 2)

(scale
 (deps
  (par
   (emit S)
   (seq (present S pause nothing)
        (emit S1))))
 2)

(scale
 (deps
  (par (present SL1
                (present SL2
                         (emit SO1)
                         (emit SL3))
                (present SL2
                         (emit SO2)
                         (emit SL3)))
       
       (seq
        (emit SL2)
        (seq (present SL3 pause nothing) (emit SL1)))))
 3)

(scale
 (deps
  (par (present SL1
                (present SL2
                         (emit SO1)
                         (emit SL3))
                (present SL2
                         (emit SO2)
                         (emit SL3)))
       
       (seq
        nothing
        (seq (present SL3 pause nothing) (emit SL1)))))
 3)
(scale
 (deps
  (par (present SL1
                (present SL2
                         (emit SO1)
                         (emit SL3))
                (present SL2
                         (emit SO2)
                         (emit SL3)))
       
       (seq
        nothing
        (seq nothing (emit SL1)))))
 3)
(scale
 (deps
  (par (present SL1
                (present SL2
                         (emit SO1)
                         (emit SL3))
                (present SL2
                         (emit SO2)
                         (emit SL3)))
       
       nothing))
 3)
(scale
 (deps
  (par 
   (present SL2
            (emit SO1)
            (emit SL3))
       
   nothing))
 3)

(scale
 (deps
  (seq (present S (exit 0) (exit 1))
       (emit S1)))
 2)
(scale
 (deps
  (seq (trap (present S (exit 0) (exit 1)))
       (emit S1)))
 2)

#|
(define-values (a b c) (taged-code (present S (emit S) nothing)))
a
b
c
(hash-ref c b #f)
(hash-ref c '(present S (emit S) nothing) #f)
|#