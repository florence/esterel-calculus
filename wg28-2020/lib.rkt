#lang racket
(require slideshow (for-syntax syntax/parse))

#;
(provide
 basic-term
 (contract-out
  [add-finger (-> aterm? (listof natural?) aterm?)]
  [aterm->pict (-> aterm? pict?)]))

(struct aterm ())
(define add-finger #f)
(define aterm->pict #f)

(define-syntax (basic-term stx)
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
          (add-thing last-line 'close-paren #f)
          last-line]
         [_
          (add-thing this-line (format "~a" (syntax-e term)) path)
          this-line]))
     #`(build-basic-term
         #,(for/hash ([(k v) (in-hash line->pict-items)])
             (values k (reverse v)))
         #,line->start-column)]))

(define (build-basic-term line->pict-items line->start-column)
  (define (build-line i)
    (define indent (s->pict (make-string (max 0 (hash-ref line->start-column i 0)) #\space)))
    (define line-items
      (for/list ([item (in-list (hash-ref line->pict-items i))]
                 [prev-item (in-list (cons #f (hash-ref line->pict-items i)))])
        (define add-space?
          (and (string? item)
               (string? prev-item)))
        (cond
          [add-space? (hbl-append (s->pict " ") (item->pict item))]
          [else (item->pict item)])))
    (apply hbl-append indent line-items))
  
  (for/fold ([p (blank)])
            ([i (in-range (+ 1 (apply max (hash-keys line->start-column))))])
    (vl-append p (build-line i))))

(define (item->pict s)
  (match s
    [(vector _ (? string? s)) (s->pict s)]
    [(vector _ 'open-paren) (s->pict "(")]
    [(vector _ close-paren) (s->pict ")")]))

(define (s->pict s) (tt s))

(colorize
 (basic-term (λ (x)
               x))
 "white")


          