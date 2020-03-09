#lang racket
(require slideshow (for-syntax syntax/parse))
(module+ test (require rackunit))

(provide
 (rename-out [-aterm aterm])
 add-arc ;(-> aterm? (listof natural?) procedure? (listof natural?) (or/c string? #f) aterm?)
  
 (contract-out
  [find-path (-> aterm? any/c natural? (listof natural?))]
  [add-left-finger (->* (aterm?) #:rest (listof (listof natural?)) aterm?)]
  [add-right-finger (->* (aterm?) #:rest (listof (listof natural?)) aterm?)]
  [aterm->pict (-> aterm? pict?)]))

(struct aterm (pict sexp left-map right-map) #:transparent
  #:constructor-name make-aterm)

(define (find-path an-aterm to-find nth)
  (match-define (aterm pict sexp left-map right-map) an-aterm)
  (find-path/sexp sexp to-find nth))

(define (find-path/sexp sexp to-find nth)
  (let/ec k
    (define how-many
      (let loop ([sexp sexp]
                 [path '()]
                 [nth nth])
        (cond
          [(equal? sexp to-find)
           (cond
             [(zero? nth)
              (k (reverse path))]
             [else 1])]
          [(list? sexp)
           (for/fold ([how-many-before 0])
                     ([ele (in-list sexp)]
                      [i (in-naturals)])
             (define how-many-here (loop ele (cons i path) (- nth how-many-before)))
             (+ how-many-before how-many-here))]
          [else 0])))
    (error 'find-path "didn't find ~s enough times, found it ~a times, but was looking for something at index ~a"
           to-find how-many
           nth)))

(module+ test
  (check-equal? (find-path/sexp 'x 'x 0) '())
  (check-equal? (find-path/sexp '(x) 'x 0) '(0))
  (check-equal? (find-path/sexp '(x x) 'x 0) '(0))
  (check-equal? (find-path/sexp '(x x) 'x 1) '(1))
  (check-equal? (find-path/sexp '(x (x)) 'x 1) '(1 0))
  (check-equal? (find-path/sexp '(x ((x))) 'x 1) '(1 0 0))
  (check-equal? (find-path/sexp '(x ((y q x))) 'x 1) '(1 0 2)))

(define (add-arc an-aterm
                 start-path find-start
                 end-path find-end
                 label-pos label
                 #:start-angle [start-angle #f]
                 #:end-angle [end-angle #f]
                 #:start-pull [start-pull #f]
                 #:end-pull [end-pull #f])
  (match-define (aterm pict sexp left-map right-map) an-aterm)
  (define start-sub-pict (hash-ref left-map start-path #f))
  (define end-sub-pict (hash-ref left-map end-path #f))
  (unless start-sub-pict
    (error 'add-arc "could not find path start ~a" start-path))
  (unless end-sub-pict
    (error 'add-arc "could not find path end ~a" end-path))
  (define with-arrow
    (pin-arrow-line 20
                    (ghost pict)
                    start-sub-pict
                    find-start
                    end-sub-pict
                    find-end
                    #:line-width 4
                    #:start-angle start-angle
                    #:end-angle end-angle
                    #:start-pull start-pull
                    #:end-pull end-pull))
  (define label-pict
    (case label
      [(⊥) (inset (s->pict (~a label)) 0 -10 0 0)]
      [(0 1) (s->pict (~a label))]
      [(#f) (blank)]
      [else (error 'add-arc "unknown label ~s" label)]))
  (define-values (label-x label-y)
    (let ()
      (define-values (sx sy) (cc-find pict start-sub-pict))
      (define-values (ex ey) (cc-find pict end-sub-pict))
      (values (/ (+ sx ex) 2) (/ (+ sy ey) 2))))
  (define with-label
    (pin-over with-arrow
              (+ label-x (car label-pos))
              (+ label-y (cdr label-pos))
              label-pict))
  (make-aterm (lc-superimpose pict
                              (colorize (launder with-label) "navy"))
              sexp left-map right-map))

(define (add-left-finger an-aterm . paths)
  (for/fold ([an-aterm an-aterm])
            ([path (in-list paths)])
    (add-one-left-finger an-aterm path)))
(define (add-right-finger an-aterm . paths)
  (for/fold ([an-aterm an-aterm])
            ([path (in-list paths)])
    (add-one-right-finger an-aterm path)))
(define (add-one-left-finger an-aterm path) (add-finger an-aterm path #t 'add-left-side-finger))
(define (add-one-right-finger an-aterm path) (add-finger an-aterm path #f 'add-right-side-finger))

(define (add-finger an-aterm path left? who)
  (match-define (aterm pict sexp left-map right-map) an-aterm)
  (define map (if left? left-map right-map))
  (define subpict (hash-ref map path #f))
  (unless subpict (error who "could not find path ~a" path))
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
  (make-aterm np sexp left-map right-map))

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
        'term
         '#,(for/hash ([(k v) (in-hash line->pict-items)])
             (values k (reverse v)))
         '#,line->start-column)]))

(define (build-basic-term sexp line->pict-items line->start-column)
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
        (define the-path (reverse (vector-ref item 0)))
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
    (define the-line
      (apply hbl-append indent line-items))
    (if (aterm-line-numbers?)
        (refocus (hbl-append (colorize (scale (s->pict (~a (+ i 1) ": ")) .8)
                                       "darkgray")
                             the-line)
                 the-line)
        the-line))
  
  (make-aterm (for/fold ([p (blank)])
                        ([i (in-range (+ 1 (apply max (hash-keys line->start-column))))])
                (vl-append p (build-line i)))
              sexp
              left-path->pict
              right-path->pict))

(define aterm-line-numbers? (make-parameter #f))

(define (item->pict s) (s->pict (vector-ref s 1)))

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