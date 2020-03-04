#lang racket
(require slideshow (for-syntax syntax/parse))

(provide
 (rename-out [-aterm aterm])
 (contract-out
  [add-left-finger (-> aterm? (listof natural?) aterm?)]
  [add-right-finger (-> aterm? (listof natural?) aterm?)]
  [aterm->pict (-> aterm? pict?)]))

(struct aterm (pict left-map right-map) #:transparent
  #:constructor-name make-aterm)

(define (add-left-finger an-aterm path) (add-finger an-aterm path #t))
(define (add-right-finger an-aterm path) (add-finger an-aterm path #f))

(define (add-finger an-aterm path left?)
  (match-define (aterm pict left-map right-map) an-aterm)
  (define map (if left? left-map right-map))
  (define subpict (hash-ref map path #f))
  (unless subpict (error 'add-left-side-finger "could not find path ~a" path))
  (define-values (x y) (if left? (lc-find pict subpict) (rc-find pict subpict)))
  (define move-finger-up-amount 6)
  (define np
    (if left?
        (pin-over
         pict
         (- x (pict-width left-finger))
         (- y (/ (pict-width left-finger) 2) move-finger-up-amount)
         left-finger)
        (pin-over
         pict
         x
         (- y (/ (pict-width right-finger) 2) move-finger-up-amount)
         right-finger)))
  (make-aterm np left-map right-map))

(define adjust-to-point-amount 100)
(define left-finger (scale (t "☞") 2))
(define right-finger (scale (t "☜") 2))


(define (aterm->pict an-aterm)
  (aterm-pict an-aterm))

(define-syntax (-aterm stx)
  (syntax-parse stx
    [(_ term)
     (define table (make-hash))
     (define line->pict-items (make-hash))
     (define line->start-column (make-hash))
     (define original-column (syntax-column #'term))
     (define original-line (syntax-line #'term))
     (define (add-thing line what path)
       (define k (- line original-line))
       (hash-set! line->pict-items k (cons (vector path what) (hash-ref line->pict-items k '()))))
     (define (start-line line column)
       (define k (- line original-line))
       (hash-set! line->start-column k (- column original-column)))
     (hash-set! line->start-column 0 0)
     (let loop ([term #'term]
                [path '()]
                [prev-line (syntax-line #'term)])
       (define this-line (syntax-line term))
       (unless (= this-line prev-line)
         (start-line this-line (syntax-column term)))
       (syntax-parse term
         [(x ...)
          (add-thing this-line 'open-paren path)
          (define last-line
            (for/fold ([this-line this-line])
                      ([x (syntax->list #'(x ...))]
                       [i (in-naturals)])
              (loop x (cons i path) this-line)))
          (add-thing last-line 'close-paren path)
          last-line]
         [_
          (add-thing this-line (format "~a" (syntax-e term)) path)
          this-line]))
     #`(build-basic-term
         #,(for/hash ([(k v) (in-hash line->pict-items)])
             (values k (reverse v)))
         #,line->start-column)]))

(define (build-basic-term line->pict-items line->start-column)
  (define left-path->pict (make-hash))
  (define right-path->pict (make-hash))
  (define (build-line i)
    (define indent (s->pict (make-string (max 0 (hash-ref line->start-column i 0)) #\space)))
    (define line-items
      (for/list ([item (in-list (hash-ref line->pict-items i))]
                 [prev-item (in-list (cons #f (hash-ref line->pict-items i)))])
        (define add-space?
          (and prev-item
               (or (and (string? (vector-ref prev-item 1))
                        (string? (vector-ref item 1)))
                   (and (string? (vector-ref prev-item 1))
                        (equal? (vector-ref item 1) 'open-paren)))))
        (define the-pict (item->pict item))
        (define the-path (vector-ref item 0))
        (match (vector-ref item 1)
          ['open-paren
           (hash-set! left-path->pict the-path the-pict)]
          ['close-paren
           (hash-set! right-path->pict the-path the-pict)]
          [_
           (hash-set! right-path->pict the-path the-pict)
           (hash-set! left-path->pict the-path the-pict)])
        (cond
          [add-space?
           (hbl-append (s->pict " ") the-pict)]
          [else the-pict])))
    (apply hbl-append indent line-items))
  
  (make-aterm (for/fold ([p (blank)])
                        ([i (in-range (+ 1 (apply max (hash-keys line->start-column))))])
                (vl-append p (build-line i)))
              left-path->pict
              right-path->pict))

(define (item->pict s)
  (define st
    (match (vector-ref s 1)
      [(? string? s) s]
      ['open-paren "("]
      ['close-paren ")"]))
  (define the-pict (s->pict st))
  the-pict)

(define (s->pict s)
  (cond
    [(member s '("par" "seq" "signal" "go" "present" "emit" "nothing" "pause"))
     (parameterize ([current-main-font (cons 'bold "Inconsolata")])
       (t s))]
    [(symbol? s)
     (define str
       (match s
         ['open-paren "("]
         ['close-paren ")"]))
     (parameterize ([current-main-font "Inconsolata"])
       (colorize (t str) "brown"))]
    [else
     (parameterize ([current-main-font "Inconsolata"])
       (t s))]))


