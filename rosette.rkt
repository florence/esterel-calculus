#lang rosette/safe

(provide define-circuit convert circuit define-wires
         wire-constraints defined)

(require
  rosette/query/debug
  (for-syntax syntax/parse racket/syntax syntax/id-set))
(module+ test (require rackunit))

(module+ name-manipulation
  (provide (for-syntax + -)))

(define-syntax defined
  (syntax-parser
    [(_ x)
     #'(or (convert+ x)
           (convert- x))]))
     

(define-syntax define-circuit
  (syntax-parser
    #:literals (=)
    [(df (n:id arg:id ...)
         (= a:id b:expr)
         ...)
     
     #:with (+var ...) (map + (syntax->list #'(arg ...)))
     #:with (-var ...) (map - (syntax->list #'(arg ...)))
     #'(begin
         (define/debug (f +var ... -var ...)
           (df c
               #:interface (arg ...)
               (= a b)
               ...)
           c)
         (define-syntax n
           (syntax-parser
             [(_ arg ...)
              #:with (+var ...) (list (+ #'arg) ...)
              #:with (-var ...) (list (- #'arg) ...)
              #'(f +var ... -var ...)])))] 
    [(_ n:id
        (~optional (~seq #:interface (o:id ...))
                   #:defaults ([(o 1) empty]))
        (= a:id b:expr)
        ...)
     #'(define/debug n
         (circuit
          #:interface (o ...)
          (= a b) ...))]))
(define-syntax circuit
  (syntax-parser
    #:literals (=)
    [(_ (~optional (~seq #:interface (o:id ...))
                   #:defaults ([(o 1) empty]))
        (= a:id b:expr)
        ...)
     #:when #t ;; TODO check a's are unique
     #`(let ()
         (define-vars safety
           #:omit (o ...)
           a ... b ...)
         (implies safety
                  (and (convert (<=> a b))
                       ...)))]))

(define-for-syntax (+ a)
  (format-id a "+~a" a
             #:source a
             #:props a))
(define-for-syntax (- a)
  (format-id a "-~a" a
             #:source a
             #:props a))

(define-syntax define-wires
  (syntax-parser
    [(_ #:constraints n:id
        w:id ...)
     #'(define-vars n
         #:omit ()
         w ...)]))
     

(define-syntax define-vars
  (syntax-parser
    [(_ n:id #:omit (o ...) a:expr ...)
     #:with (var ...)
     (for/fold ([s (immutable-bound-id-set)]
                #:result (set->list
                          (set-subtract
                           s
                           (immutable-bound-id-set (syntax->list #'(o ...))))))
               ([b (in-syntax #'(a ...))])
       (set-union (vars-of b) s))
     #:with (+var ...) (map + (syntax->list #'(var ...)))
     #:with (-var ...) (map - (syntax->list #'(var ...)))
     #`(begin
         (define-symbolic* +var boolean?) ...
         (define-symbolic* -var boolean?) ...
         (define n
           (wire-constraints var ...)))]))

(define-syntax wire-constraints
  (syntax-parser
    [(_ var:id ...)
     #:with (+var ...) (map + (syntax->list #'(var ...)))
     #:with (-var ...) (map - (syntax->list #'(var ...)))
     #'(and (not (and +var -var)) ...)]))

(define-syntax convert
  (syntax-parser
    [(_ a ...)
     #'(and
        (and (convert+ a) (convert- a))
        ...)]))

(define-syntax convert+
  (syntax-parser
    #:literals (and or not <=>)
    [(_ (<=> a b))
     #'(<=> (convert+ a) (convert+ b))]
    [(_ #f) #'#f]
    [(_ #t) #'#t]
    [(_ x:id) (+ #'x)]
    [(_ (and a ...))
     #'(and (convert+ a) ...)]
    [(_ (or a ...))
     #'(or (convert+ a) ...)]
    [(_ (not a))
     #'(convert- a)]))

(define-syntax convert-
  (syntax-parser
    #:literals (and or not <=>)
    [(_ (<=> a b))
     #'(<=> (convert- a) (convert- b))]
    [(_ #f) #'#t]
    [(_ #t) #'#f]
    [(_ x:id) (- #'x)]
    [(_ (and a ...))
     #'(or (convert- a) ...)]
    [(_ (or a ...))
     #'(and (convert- a) ...)]
    [(_ (not a))
     #'(convert+ a)]))


(define-for-syntax (vars-of x)
  (syntax-parse x
    #:literals (and or not)
    [x:id (immutable-bound-id-set (list #'x))]
    [y:boolean (immutable-bound-id-set)]
    [((~or and or) a ...)
     (apply set-union (map vars-of (syntax->list #'(a ...))))]
    [(not x) (vars-of #'x)]))
    
(module+ test
  (test-begin
   (define-wires
     #:constraints c2
     l0 GO)
   (define-circuit c
     #:interface (l0 GO)
     (= lem GO)
     (= rem GO)
     (= l0 GO)
     (= r0 GO)
     (= left (or lem l0))
     (= right (or rem r0))
     (= both (or l0 r0))
     (= k0 (and left right both)))
   (check-equal?
    (verify
     #:assume (assert (and c2 c))
     #:guarantee
     (assert
      (circuit
       #:interface (l0 GO)
       (= l0 GO))))
    (unsat)))
  (clear-asserts!)
  (test-begin
   (define-wires
     #:constraints c2
     k0/n+2 GO sel k1)
   (define-circuit c
     #:interface (k0/n+2 GO sel k1)
     (= sel #f)
     (= k0/n+2 GO)
     (= k1 (or #f res-o-S))
     (= res-o-S (and res-o S))
     (= res-o (and res sel)))
   (check-equal?
    (verify
     #:assume (assert (and c2 c))
     #:guarantee
     (assert
      (circuit
        
       #:interface (k0/n+2 GO sel k1)
       (= k0/n+2 GO)
       (= sel #f)
       (= k1 #f))))
    (unsat)))
  (clear-asserts!)
  (test-begin
   (define +GO #f)
   (define -GO #t)
   (define-wires
     #:constraints c2
     a)
   (define-circuit c #:interface (a GO)
     (= a GO))
   (check-equal?
    (verify
     #:assume (assert (and c c2))
     #:guarantee
     (assert
      (circuit
       #:interface (a)
       (= a #f))))
    (unsat))))