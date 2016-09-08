#lang debug racket
(provide esterel-machine
         define-esterel-form
         eval-top
         nothing&
         exit&
         emit&
         pause&
         present&
         suspend&
         seq&
         loop&
         par&
         trap&
         signal&
         loop-each&
         shared&
         await&
         abort&
         halt&
         sustain&
         every&
         if&
         cond&
         var&
         ?
         :=&
         get-var
         machine-prog
         data-ref
         (for-syntax msg call est local-expand-esterel))
(require "model.rkt"
         redex/reduction-semantics
         racket/stxparam
         (for-syntax racket/pretty syntax/parse racket/syntax
                     racket/function racket/dict
                     racket/sequence racket/format racket/promise
                     syntax/id-set redex/reduction-semantics
                     syntax/id-table racket/match
                     "model.rkt"))

(define-for-syntax core-esterel-forms
  (syntax->list
   (quote-syntax
    (nothing
     pause
     seq
     par
     loop
     suspend
     present
     trap
     exit
     emit
     var
     shared
     signal
     :=
     <=
     if))))

;; Machine Inputs -> Machine Inputs
;; where Inputs = (listof (U symbol (lst symbol any)))
(define (eval-top in-machine inputs)
  (match-define (machine in-prog replacements valid-ins outputs) in-machine)
  (check-inputs! valid-ins inputs)
  (define in-store*
    (filter
     values
     (for/list ([i (in-list inputs)])
       (match i
         [(list s v)
          (list 'shar (dict-ref replacements s) v 'new)]
         [else #f]))))
  (define E
    (filter
     values
     (for/list ([i (in-list valid-ins)])
       (match-define (or (list S _) S) i)
       (match inputs
         [(list _ ... (or (== S) (list (== S) _)) _ ...)
          (list 'sig S 'present)]
         [else #f #;(list 'sig S 'absent)
               ]))))

  (define n (term (instant ,in-prog ,(append in-store* E))))
  (unless n
    (error 'eval
           "failed to evaluate: ~a"
           (list 'instant in-prog (append in-store* E))))
  (match-define (list out-prog outed) n)
  (values (make-machine out-prog replacements valid-ins outputs)
          (get-data outputs
                    outed
                    replacements
                    out-prog)))

(define (check-inputs! vins inputs)
  (for ([i (in-list inputs)])
    (unless
        (match i
          [(list (? symbol? a) _)
           (for/or ([vin (in-list vins)])
             (match vin
               [(list (== a) _) #t]
               [_ #f]))]
          [(? symbol? a)
           (member a vins)])
      (error 'signals "not valid signal ~a" i))))

(define (data-ref machine name)
  (define data (get-data (list name)
                         (list name)
                         (machine-replacements machine)
                         (machine-prog machine)))
  (match data
    [`((,(== name) ,ev)) ev]))

(define (get-data outputs include replacements p)
  (match-define `(env (,env-vs ...) ,_) p)
  (filter
   values
   (for/list ([o (in-list outputs)])
     (match* (env-vs include)
       [((list* _ ...
                `(shar ,(== (dict-ref replacements o #f)) ,ev ,_)
                _)
         (list* _ ... (== o) _))
        (match-define (or `(rvalue ,ev*) ev*) ev)
        (list o ev*)]
       [(_ (list* _ ... (== o) _))
        o]
       [(_ _) #f]))))

(struct machine (prog replacements valid-ins outputs)
  #:reflection-name 'esterel-machine
  #:extra-constructor-name make-machine)
(define-syntax esterel-machine
  (syntax-parser
    [(_ #:inputs (in ...)
        #:outputs (out ...)
        machine)
     (define/with-syntax t
       (parameterize ([in-machine? #t])
         (define init-expr
           (local-expand-esterel #'machine))
         init-expr))
     (define/with-syntax ((outv/sym out/value) ...)
       (for/list ([o (in-syntax #'(out ...))]
                  #:when (syntax-parse o [(a b) #t] [_ #f]))
         ;; TODO i think this should be "old" but thats annoying and not needed yet
         ;; and requires comb functions
         (syntax-parse o [(n v) (list #'n #`(shar n v old))])))
     (define/with-syntax ((inv/sym in/value) ...)
       (for/list ([i (in-syntax #'(in ...))]
                  #:when (syntax-parse i [(a b) #t] [_ #f]))
         (syntax-parse i [(n v) (list #'n #`(shar n v new))])))
     (define/with-syntax (in/sym ...)
       (for/list ([x (in-syntax #'(in ...))])
         (syntax-parse x [(i _) #'i] [i #'i])))
     (define/with-syntax (out/sym ...)
       (for/list ([x (in-syntax #'(out ...))])
         (syntax-parse x [(i _) #'i] [i #'i])))
     (define/with-syntax ((in/out ...) (in/out-replacements ...))
       (list
        #'(inv/sym ... outv/sym ...)
        (generate-temporaries #'(inv/sym ... outv/sym ...))))
     (define/with-syntax (in/out*/value ...)
       (begin
         (syntax-parse #'(in/value ... out/value ...)
           [((shar n v new) ...)
            #'((shar in/out-replacements v new) ...)])))
     #'(let-values ([(raw-prog)
                     (set-sigs `(in/sym ... out/sym ...)
                      (update-vars (term t)
                                   '((in/out . in/out*/value) ...)))])
         ;(loop-safe! raw-prog) TODO
         (make-machine `(env ((sig in/sym unknown) ... (sig out/sym unknown) ... in/out*/value ...)
                             ,raw-prog)
                       '((in/out . in/out-replacements) ...)
                       '(in ...)
                       '(out/sym ...)))]))

(define (update-vars t vmap)
  (define (u t) (update-vars t vmap))
  (define (u/e e) (update-vars/e e vmap))
  (define (u/v v) (update-vars/v v vmap))
  (match t
    [`(var ,s := ,e ,p)
     `(var ,(u/v s) := ,(u/e e) ,(u p))]
    [`(shared ,s := ,e ,p)
     `(shared ,(u/e s) := ,(u/e e) ,(u p))]
    [`(<= ,s ,e) `(<= ,(u/v s) ,(u/e e))]
    [`(:= ,s ,e) `(:= ,(u/v s) ,(u/e e))]
    [`(if ,e ,p ,q) `(if ,(u/e e) ,(u p) ,(u q))]
    [(? list?) (map u t)]
    [else t]))
(module+ test
  (let ([f (const #t)])
    (check-equal? (update-vars `(if ((rfunc ,f) I) nothing nothing)
                               '((I . R)))
                  `(if ((rfunc ,f) R) nothing nothing))))

(define (update-vars/e e vmap)
  (cond
    [(list? e)
     (for/list ([e (in-list e)])
       (update-vars/e e vmap))]
    [(dict-ref vmap e #f) => values]
    [else e]))

(define (update-vars/v v vmap)
  (match (dict-ref vmap v #f)
    [`(shar ,vo ,_ ,_) vo]
    [#f v]))

(define (set-sigs s p)
  (for/fold ([p p])
            ([s (in-list s)])
    (term (substitute* ,p ,s (sig ,s unknown)))))

(define-syntax define-esterel-form
  (syntax-parser
    [(_ name:id val)
     #'(define-syntax name (make-esterel-form val))]))

(define-for-syntax in-machine? (make-parameter #f))

(begin-for-syntax
  (struct esterel-form (proc)
    #:property prop:procedure (struct-field-index proc)))
(begin-for-syntax (provide make-esterel-form))
(define-for-syntax (make-esterel-form f)
  (esterel-form
   (lambda (stx)
     (unless (in-machine?)
       (raise-syntax-error #f "use of a esterel form not in a esterel machine" stx))
     (f stx))))

(begin-for-syntax
  (define-extended-language e* esterel-eval))
(define-for-syntax (local-expand-esterel stx [ctx #f])
  (unless (in-machine?)
      (raise-syntax-error #f "use of a esterel form escaped esterel context" stx))
  (define n
    (syntax-parse stx
      [(n:id . body)
       #'n]
      [name:id #'name]))
  (unless (or (memf (lambda (x) (free-identifier=? n x)) core-esterel-forms)
              (esterel-form? (syntax-local-value n (lambda () #f) ctx)))
    (raise-syntax-error #f "use of non-esterel form in esterel context" stx))
  (define x
    (local-expand stx (if ctx (list ctx) 'expression) core-esterel-forms ctx))
  (define datum (syntax->datum x))
  (unless (redex-match? e* p datum)
    (raise-syntax-error #f (~a "got bad esterel code " (~a datum)) stx))
  x)


(define-syntax-parameter ENV (lambda (stx) (raise-syntax-error #f "no" stx)))
(define-for-syntax shared-vars-set (make-parameter #f))
(define-for-syntax normal-vars-set (make-parameter #f))
(define-for-syntax (delayed-call e)
  (delay
    (with-syntax ([env #'env])
      (parameterize ([shared-vars-set (mutable-free-id-set)]
                     [normal-vars-set (mutable-free-id-set)])
        (define/with-syntax f
          (local-expand
           #`(lambda (env)
               (syntax-parameterize ([ENV (make-rename-transformer #'env)])
                 #,e))
           'expression
           null))
        (define/with-syntax (var ...)
          (append (free-id-set->list (shared-vars-set))
                  (free-id-set->list (normal-vars-set))))
        #`((rfunc
            (unquote
             (lambda (var ...)
               (define env
                 (make-hasheq
                  (list (cons 'var (maybe-rvalue->value var)) ...)))
               (f env))))
           var ... )))))
(define (maybe-rvalue->value mrv)
  (match mrv
    [`(rvalue ,v) v]
    [v v]))

(begin-for-syntax
  (define-syntax-class msg
    (pattern _:id)
    (pattern (or _:id ...)))
  (define-syntax-class est
    (pattern a
             #:attr exp (delay (local-expand-esterel #'a))))
  (define-syntax-class call
    (pattern e
             #:attr func (delayed-call #'e))))

(define-esterel-form nothing& (syntax-parser [_:id #'nothing]))
(define-esterel-form pause& (syntax-parser [_:id #'pause]))
(define-esterel-form exit&
  (syntax-parser
    [(_ T:id) #`(exit #,(get-exit-code #'T))]))
(define-esterel-form emit&
  (syntax-parser
    [(_ S:id)
     #`(emit #,(get-signal-replacement #'S))]
    [(form S:id call:call)
     #`(seq& (form S)
             (<= #,(get-signal-var (get-signal-replacement #'S)) call.func))]))

(define-esterel-form present&
  (syntax-parser
    [(_ (~or (or S:id) S:id) th:est el:est)
     #`(present #,(get-signal-replacement #'S) th.exp el.exp)]
    [(p S:msg th:expr) #'(p S th nothing&)]
    ;; WARNING duplicates code
    [(p (or S1:id S2:id ...) th:expr el:expr)
     #'(p S1 th (p (or S2 ...) th el))]))

(define-esterel-form suspend&
  (syntax-parser
    #:datum-literals (or not)
    [(_ (not S:id) p:est)
     (define/with-syntax S_local (generate-temporary 'not-signal))
     (define/with-syntax T (generate-temporary 'not-trap))
     #'(trap&
        T
        (signal& S_local
                 (par&
                  (loop& (present& S nothing& (emit& S_local)) pause&)
                  (seq& (suspend& S_local p) (exit& T)))))]
    [(_ (~or (or S:id) S:id) p:est)
     #`(suspend p.exp #,(get-signal-replacement #'S))]
    [(s S p:expr ...)
     #`(s S (seq& p ...))]
    [(s (or S1 S2 ...) p:expr ...)
     #'(s S1 (s (or S2 ...) p ...))]))
(define-esterel-form seq&
  (syntax-parser
    [(_ p:expr) #'p]
    [(_ l:est r:est)
     #'(seq l.exp r.exp)]
    [(_ l:expr r:expr ...)
     #`(seq& l (seq& r ...))]))
(define-esterel-form loop&
  (syntax-parser
    [(_ p:est)
     #'(loop p.exp)]
    [(_ p:expr ...)
     #`(loop& (seq& p ...))]))
(define-esterel-form par&
  (syntax-parser
    [(_ l:expr) #'l]
    [(_ l:est r:est) #'(par l.exp r.exp)]
    [(_ l:expr r:expr ...) #`(par& l (par& r ...))]))
(define-esterel-form trap&
  (syntax-parser
    [(_ T p:est)
     (parameterize ([exit-stack (cons #'T (exit-stack))])
       #'(trap p.exp))]
    [(_ T:id p:expr ...)
     #`(trap& T (seq& p ...))]))
(define-esterel-form signal&
  (syntax-parser
    #:datum-literals (:=)
    [(form S:id := e:call p:est)
     (parameterize ([signal-var-map (extend-signal-var-map-for #'S)])
       #`(signal S
               (shared #,(get-signal-var #'S) := e.func p.exp)))]
    [(form S:id := e:call p:expr ...)
     #`(form S := e.func (seq& p ...))]
    [(s (S:id) p:expr ...)
     #'(s S p ...)]
    [(s (S_1:id S:id ...) p:expr ...)
     #'(s S_1 (s (S ...) p ...))]
    [(_ S:id p:est)
     #`(signal S p.exp)]
    [(form S:id p:expr ...)
     #`(form S (seq& p ...))]))


(define-syntax ?
  (syntax-parser
    [(? s:id)
     (define/with-syntax svar (get-signal-var (get-signal-replacement #'s)))
     (free-id-set-add! (shared-vars-set) #'svar)
     #'(hash-ref ENV 'svar)]))

(define-syntax get-var
  (syntax-parser
    [(? v:id)
     (free-id-set-add! (normal-vars-set) #'v)
     #`(hash-ref ENV 'v)]))
(define-syntax delay-var*
  (syntax-parser [(_ x:id) #'x]))

(define-esterel-form cond&
  (syntax-parser
    [(cond& [a b ...] body ...)
     #`(if& a
            (seq& b ...)
            (cond& body ...))]
    [(cond&) #'nothing&]))
(define-esterel-form if&
  (syntax-parser
    [(_ call:call p:est q:est)
     #'(if call.func p.exp q.exp)]))

(define-esterel-form loop-each&
  (syntax-parser
    [(_ S:msg p:expr ...)
     #'(loop&
        (abort& S
                (seq& (seq& p ...) halt&)))]))

(define-esterel-form weak-abort&
  (syntax-parser
    [(_ S:msg p:expr ...)
     (define/with-syntax T (generate-temporary (format-id #f "~a-abort-trap"
                                                          (~a (syntax->datum #'S)))))
     #'(trap& T
              (par& (seq& (seq& p ...) (exit& T))
                    (seq& (await& S) (exit& T))))]))

(define-esterel-form abort&
  (syntax-parser
    [(_ S:msg p:expr ...)
     (define/with-syntax T (generate-temporary (format-id #f "~a-abort-trap"
                                                          (~a (syntax->datum #'S)))))
     #'(trap& T
              (par& (seq& (suspend& S (seq& p ...)) (exit& T))
                    (seq& (await& S) (exit& T))))]))

(define-esterel-form halt&
  (syntax-parser
    [_:id #'(loop& pause&)]))

(define-esterel-form var&
  (syntax-parser
    #:datum-literals (:=)
    [(_ a:id := b:call c:est)
     #'(var a := b.func c.exp)]))

(define-esterel-form shared&
  (syntax-parser
    #:datum-literals (:=)
    [(_ a:id := b:call c:est)
     #'(shared a := b.func c.exp)]))

(define-esterel-form repeat&
  (syntax-parser
    [(_ n:call p)
     (define/with-syntax v (generate-temporary 'repeat-var))
     (define/with-syntax T (generate-temporary 'repeat-trap))
     #`(trap& T
              (var& v := n
                    (loop&
                     (if& (> (get-var v) 0)
                          (seq& (:=& v (- (get-var v) 1)) p)
                          (exit& T)))))]))

(define-esterel-form await&
  (syntax-parser
    ;; this is how its supposed to be compiled
    ;; but "suspend-not" is freaking slow
    #;
    [(a n:call S:msg)
     #'(suspend& (not S) (repeat& n pause&))]
    #;
    [(a S:msg) #'(a 1 S)]
    [(a n:call S:msg)
     #'(seq& (await& S) (repeat& (- n 1) (await& S)))]
    [(a S:msg)
     (define/with-syntax T (generate-temporary 'await-trap))
     #'(trap& T (loop& pause& (present& S (exit& T))))]))

(define-esterel-form :=&
  (syntax-parser
    [(_ v c:call)
     #'(:= v c.func)]))
(define-esterel-form sustain&
  (syntax-parser
    [(_ S:msg) #'(loop& (emit& S) pause&)]))

(define-esterel-form every&
  (syntax-parser
    [(_ S:msg p:expr ...)
     #'(seq& (await& S) (loop-each& S p ...))]))



(define-for-syntax exit-stack (make-parameter null))
(define-for-syntax (get-exit-code T)
  (for/sum ([k (exit-stack)]
            #:break (free-identifier=? T k))
    1))

(define-for-syntax signal-var-map (make-parameter (make-hash)))
(define-for-syntax (extend-signal-var-map-for s)
  (if (hash-has-key? (signal-var-map) (syntax-e s))
      (signal-var-map)
      (hash-set (signal-var-map) (syntax-e s) (generate-temporary s))))
(define-for-syntax (get-signal-var s)
  (hash-ref (signal-var-map) (syntax-e s) s))

(define-for-syntax signal-replace-map (make-parameter (make-hash)))
(define-for-syntax (extend-signal-replace-map-for s)
  (hash-set (signal-replace-map) (syntax-e s) (gensym)))
(define-for-syntax (get-signal-replacement s)
  (hash-ref (signal-replace-map) (syntax-e s) s))

(module+ test
  (require rackunit)
  (test-begin
    (define-values (M S...)
      (eval-top
       (esterel-machine
        #:inputs ((I 1))
        #:outputs ((O 0))
        (present& I
                  nothing&
                  (if& (= (? I) 1)
                       (emit& O 1)
                       nothing&)))
       '()))
    (check-equal? S... '((O 1)))))


(define (fix-i/o prog ins outs)
  ;(define-values (prog* in-map out-map) (needed+sub prog ins outs))
  (define-values (prog*o in-mapo out-mapo) (needed+sub prog ins outs))
  (define-values (prog* in-map out-map) (needed+sub prog ins outs in-mapo out-mapo))
  (define new/ins
    (for/fold ([p prog*])
              ([(old new) (in-hash in-map)])
      `(signal ,new
               (par
                ,p
                (loop
                 (seq
                  (present ,old (emit ,new) nothing)
                  pause))))))
  (define new/outs
    (for/fold ([p new/ins])
              ([(old new) (in-hash out-map)])
      `(signal ,new
               (par
                ,p
                (loop
                 (seq
                  (present ,new (emit ,old) nothing)
                  pause))))))
  new/outs)
(define (needed+sub prog ins outs [ins-hash (hash)] [outs-hash (hash)])
  (define (recur p #:ins [in* ins-hash] #:outs [out* outs-hash])
    (needed+sub p ins outs in* out*))
  (define do
    (term-match/single
     esterel-eval
     [nothing (values prog ins-hash outs-hash)]
     [pause (values prog ins-hash outs-hash)]
     [(seq p q)
      (let ()
        (define-values (l1 l2 l3) (recur `p))
        (define-values (r1 r2 r3) (recur `q #:ins l2 #:outs l3))
        (values `(seq ,l1 ,r1) r2 r3))]
     [(par p q)
      (let ()
         (define-values (l1 l2 l3) (recur `p))
         (define-values (r1 r2 r3) (recur `q #:ins l2 #:outs l3))
         (values `(par ,l1 ,r1) r2 r3))]
     [(loop p)
      (let ()
         (define-values (a b c) (recur `p))
         (values `(loop ,a) b c))]
     [(suspend p S)
      (let ()
         (cond [(hash-ref outs-hash `S #f) =>
                (lambda (nS)
                  (recur `(suspend p ,nS)))]
               [(member `S outs)
                (recur prog #:outs (hash-set outs-hash `S (gensym `S)))]
               [else
                (define-values (l1 l2 l3) (recur `p))
                (values `(suspend ,l1 S) l2 l3)]))]
     [(signal S p)
      (let ()
         (define-values (a b c) (recur `p))
         (values `(signal S ,a) b c))]
     [(emit S)
      (let ()
         (cond [(hash-ref ins-hash `S #f) =>
                (lambda (nS)
                  (values `(emit ,nS) ins-hash outs-hash))]
               [(member `S ins)
                (recur prog #:ins (hash-set ins-hash `S (gensym `S)))]
               [(hash-ref outs-hash `S #f) =>
                (lambda (nS)
                  (values `(emit ,nS) ins-hash outs-hash))]
               [else (values prog ins-hash outs-hash)]))]
     [(present S p q)
      (let ()
         (cond [(hash-ref outs-hash `S #f) =>
                (lambda (nS)
                  (recur `(present ,nS p q)))]
               [(member `S outs)
                (recur prog #:outs (hash-set outs-hash `S (gensym `S)))]
               [(hash-ref ins-hash `S #f) =>
                (lambda (nS)
                  (recur `(present ,nS p q)))]
               [else
                (define-values (l1 l2 l3) (recur `p))
                (define-values (r1 r2 r3) (recur `q #:ins l2 #:outs l3))
                (values `(present S ,l1 ,r1) r2 r3)]))]
     [(trap p)
      (let ()
         (define-values (a b c) (recur `p))
         (values `(trap ,a) b c))]
     [(exit _) (values prog ins-hash outs-hash)]
     [(var v := any p)
      (let ()
         (define-values (a b c) (recur `p))
         (values `(var v := any ,a) b c))]
     [(shared s := any p)
      (let ()
        (define-values (a b c) (recur `p))
        (values `(shared s := any ,a) b c))]
     [(:= v call) (values prog ins-hash outs-hash)]
     [(<= s call) (values prog ins-hash outs-hash)]
     [(if v p q)
      (let ()
         (define-values (l1 l2 l3) (recur `p))
         (define-values (r1 r2 r3) (recur `q #:ins l2 #:outs l3))
         (values `(if v ,l1 ,r1) r2 r3))]))
  ;; -- in --
  (let-values ([(a b c) (do prog)])
    (values a b c)))
