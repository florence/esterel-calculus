#lang racket
(provide esterel-machine
         define-esterel-machine
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
         await-immediate&
         abort&
         weak-abort&
         weak-abort-immediate&
         halt&
         repeat&
         sustain&
         every&
         every-immediate&
         if&
         cond&
         pcond&
         var&
         ?
         :=&
         run&
         suspend-immediate&
         get-var
         machine-prog
         data-ref
         debug&
         (for-syntax msg call est local-expand-esterel))
(require esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/reduction
         esterel-calculus/redex/model/instant
         redex/reduction-semantics
         racket/stxparam
         racket/syntax
         (for-syntax
          racket/pretty syntax/parse racket/syntax
          racket/function racket/dict
          racket/bool
          racket/sequence racket/format racket/promise
          syntax/id-set redex/reduction-semantics
          syntax/id-table racket/match
          esterel-calculus/redex/model/shared
          esterel-calculus/redex/model/reduction))
(module+ test
  (require rackunit))

(define-syntax define-core-forms
  (syntax-parser
    [(_ name forms ...)
     #`(begin
         (define-for-syntax name
           (syntax->list (syntax (forms ...))))
         (define-syntax forms (lambda (stx) (raise-syntax-error #f "not actually usable" stx)))
         ...)]))
(define-core-forms core-esterel-forms
  nothing
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
  if)

;; Machine Inputs #:check-standard-implies-calculus? [Boolean] -> Machine Inputs
;; where Inputs = (listof (U symbol (lst symbol any)))
;; if `check-standard-implies-calculus` is #t, this function makes sure
;;    that, each time it p standard reduces to q, that p reduces in
;;    calculus.rkt's reduction relation to q, too.
(define (eval-top in-machine inputs
                  #:check-standard-implies-calculus?
                  [check-standard-implies-calculus?
                   (current-check-standard-implies-calculus)])
  (match-define (machine in-prog replacements valid-ins outputs) in-machine)
  (check-inputs! valid-ins inputs)
  (define in-store*
    (filter
     values
     (for/list ([i (in-list inputs)])
       (match i
         [(list s v)
          (list 'shar (second (dict-ref replacements s)) `(rvalue ,v) 'new)]
         [else #f]))))
  (define E
    (filter
     values
     (for/list ([i (in-list valid-ins)])
       (match-define (or (list S _) S) i)
       (match inputs
         [(list _ ... (or (== S) (list (== S) _)) _ ...)
          (list 'sig (first (dict-ref replacements S)) 'present)]
         [else #f #;(list 'sig S 'absent)
               ]))))

  (define n (parameterize ([current-check-standard-implies-calculus check-standard-implies-calculus?])
              (term (instant ,in-prog ,(append in-store* E)))))
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

(define (θ->list θ)
  (let loop ([l θ])
    (match l
      ['· empty]
      [(list v r)
       (cons v (loop r))])))
(define (list->θ l)
  (let loop ([l l] [seen null])
    (match l
      [(list) '·]
      [(cons f r)
       (cond
         [(memq (second f) seen)
          (loop r seen)]
         [else (list f (loop r (cons (second f) seen)))])])))

(define (get-data outputs include replacements p)
  (match-define `(ρ ,θ ,_ ,_) p)
  (define env-vs (θ->list θ))
  (filter
   values
   (for/list ([o (in-list outputs)])
     (define g (dict-ref replacements o))
     (match* (env-vs include)
       [((list* _ ...
                `(shar ,(== (second g)) ,ev ,_)
                _)
         (list* _ ... (== (first g)) _))
        (match-define (or `(rvalue ,ev*) ev*) ev)
        (list o ev*)]
       [(_ (list* _ ... (== (first g)) _))
        o]
       [(_ _) #f]))))


;                                                                        
;                                                                        
;                                                                        
;                                                                        
;                                 ;;;          ;;;                       
;                                 ;;;          ;;;                       
;   ;;;   ;;;                     ;;;          ;;;                       
;   ;;;   ;;;                     ;;;                                    
;   ;;;; ;;;;  ;;;;         ;;;;  ;;; ;;;   ;;;;;;    ;;; ;;;      ;;;;  
;   ;;;; ;;;;  ;;;;;;     ;;;;;;  ;;;;;;;;  ;;;;;;    ;;;;;;;;    ;;;;;; 
;   ;;;; ;;;;     ;;;    ;;;      ;;;   ;;;    ;;;    ;;;   ;;;  ;;   ;; 
;   ;;;; ;;;;      ;;;  ;;;       ;;;   ;;;    ;;;    ;;;   ;;;  ;;   ;;;
;   ;;;; ;;;;    ;;;;;  ;;;       ;;;   ;;;    ;;;    ;;;   ;;; ;;;;;;;;;
;   ;;; ; ;;;  ;;;;;;;  ;;;       ;;;   ;;;    ;;;    ;;;   ;;; ;;;;;;;;;
;   ;;; ; ;;; ;;;  ;;;  ;;;       ;;;   ;;;    ;;;    ;;;   ;;; ;;;      
;   ;;;   ;;; ;;;  ;;;   ;;;      ;;;   ;;;    ;;;    ;;;   ;;;  ;;;     
;   ;;;   ;;; ;;;;;;;;    ;;;;;;  ;;;   ;;; ;;;;;;;;; ;;;   ;;;   ;;;;;; 
;   ;;;   ;;;  ;;; ;;;     ;;;;;  ;;;   ;;; ;;;;;;;;; ;;;   ;;;     ;;;; 
;                                                                        
;                                                                        
;                                                                        
;                                                                        
;                                                                        

(begin-for-syntax
  (struct compile-time-machine (generator renamer)
    #:property prop:procedure
    (struct-field-index renamer)
    #:extra-constructor-name make-compile-time-machine))
(struct machine (prog replacements valid-ins outputs)
  #:reflection-name 'esterel-machine
  #:extra-constructor-name make-machine)
(define-syntax define-esterel-machine
  (syntax-parser
    [(_ name:id
        #:inputs (in ...)
        #:outputs (out ...)
        (~optional (~seq #:input/outputs (ios ...))
                   #:defaults
                   ([(ios 1) null]))
        machine:expr)
     #:with runtime (generate-temporary #'name)
     #:with compile-time (generate-temporary #'name)
     #'(begin
         (define runtime
           (esterel-machine
            #:inputs (in ...)
            #:outputs (out ...)
            #:input/outputs (ios ...)
            machine))
         (define-esterel-form compile-time
           (syntax-parser
             [(_ src [outer:id -> inner:id] (... ...))
              (parameterize ([signal-replace-map
                              (extend-signal-replace-map-for-many
                               (syntax->list #'(inner (... ...)))
                               (map get-signal-replacement (syntax->list #'(outer (... ...)))))])
                (check-bound-signals! #'src (syntax->list #'(in ... out ... ios ...)))
                (local-expand-esterel #'machine))]))
         (define-syntax name
           (make-compile-time-machine
            #'compile-time
            (syntax-parser [_:id #'runtime]))))]))

(define-for-syntax (check-bound-signals! src needs)
  (define error-name
    (syntax-e (syntax-parse src [(a:id b ...) #'a] [a:id #'a])))
  (for* ([id?pair (in-list needs)]
         [id (in-value (syntax-parse id?pair [(~or (a:id _) a:id) #'a]))]
         [shared? (in-value (syntax-parse id?pair [(a:identifier _) #t] [_ #f]))])
    (unless (has-signal-replacement? id)
      (raise-syntax-error error-name
                          (format "Expected signal to either be supplied or bound")
                          src
                          id))
    (unless (implies shared? (has-signal-var? (get-signal-replacement id)))
      (raise-syntax-error error-name
                          (format "Expected supplied signal to be a value carrying signal")
                          src
                          id))))
(define-syntax esterel-machine
  (syntax-parser
    [(_ #:inputs (in ...)
        #:outputs (out ...)
        (~optional (~seq #:input/outputs (ios ...))
                   #:defaults
                   ([(ios 1) null]))
        machine)
     #:with (var/sym ...)
     (for/list ([o (in-syntax #'(in ... out ... ios ...))]
                #:when (syntax-parse o [(a b) #t] [_ #f]))
       (syntax-parse o [(n v) #'n]))
     #:with (in/sym ...)
     (for/list ([x (in-syntax #'(in ...))])
       (syntax-parse x [(i _) #'i] [i #'i]))
     #:with (out/sym ...)
     (for/list ([x (in-syntax #'(out ...))])
       (syntax-parse x [(i _) #'i] [i #'i]))
     #:with (both/sym ...)
     (for/list ([x (in-syntax #'(ios ...))])
       (syntax-parse x [(i _) #'i] [i #'i]))

     (define signals
       (make-signal-replace-map
        (syntax->list
         #'(in/sym ... out/sym ... both/sym ...))))
     (parameterize ([signal-replace-map signals])
       (define/with-syntax (in/sym/replacements ...)
         (map get-signal-replacement (syntax->list #'(in/sym ...))))
       (define/with-syntax (out/sym/replacements ...)
         (map get-signal-replacement (syntax->list #'(out/sym ...))))
       (define/with-syntax (both/sym/replacements ...)
         (map get-signal-replacement (syntax->list #'(both/sym ...))))
       (define/with-syntax (in/out/both/sym/replacements ...)
         #'(in/sym/replacements ... out/sym/replacements ... both/sym/replacements ...))
       (define vars
         (make-signal-var-map
          (map
           get-signal-replacement
           (syntax->list #'(var/sym ...)))))
       (parameterize ([signal-var-map vars])
         (define (get-sym/v stx)
           (for/list ([o (in-syntax stx)]
                      #:when (syntax-parse o [(a b) #t] [_ #f]))
             (syntax-parse o [(n* v)
                              #:with n (get-signal-var (get-signal-replacement #'n*))
                              (list #'n #`(shar n (rvalue v) old))])))
           
         (define/with-syntax ((outv/sym out/value) ...)
           (get-sym/v #'(out ...)))
         (define/with-syntax ((inv/sym in/value) ...)
           (get-sym/v #'(in ...)))
         (define/with-syntax ((bothv/sym both/value) ...)
           (get-sym/v #'(ios ...)))

         (define/with-syntax ((in/out/both ...) (in/out/both-replacements ...))
           (list
            #'(var/sym ...)
            #'(inv/sym ... outv/sym ... bothv/sym ...)))
         (define/with-syntax (in/out/both*/value ...)
           (begin
             (syntax-parse #'(in/value ... out/value ... both/value ...)
               [((shar n v new) ...)
                #'((shar in/out/both-replacements v new) ...)])))

         (define/with-syntax t
           (parameterize ([in-machine? #t])
             (local-expand-esterel #'machine)))
         (define/with-syntax (in+out+both ...)
           #'(in/sym ... out/sym ... both/sym ...))
         (define/with-syntax (reps ...)
           (for/list ([s (in-syntax #'(in+out+both ...))])
             (define/with-syntax S (get-signal-replacement s))
             #`(S #,(dict-ref (signal-var-map) #'S #f))))

         #'(let-values ([(raw-prog) (term t)])
             (make-machine `(ρ ,(list->θ
                                 `((sig in/sym/replacements unknown) ...
                                   (sig out/sym/replacements unknown) ...
                                   (sig both/sym/replacements unknown) ...
                                   in/out/both*/value ...))
                               GO
                               ,raw-prog)
                           '((in+out+both . reps) ...)
                           '(in ... ios ...)
                           '(out/sym ... both/sym ...)))))]))

(define (update-vars t vmap)
  (define (u t) (update-vars t vmap))
  (define (u/e e) (update-vars/e e vmap))
  (match t
    [`(var ,s := ,e ,p)
     `(var ,(u/e s) := ,(u/e e) ,(u p))]
    [`(shared ,s := ,e ,p)
     `(shared ,(u/e s) := ,(u/e e) ,(u p))]
    [`(<= ,s ,e) `(<= ,(u/e s) ,(u/e e))]
    [`(:= ,s ,e) `(:= ,(u/e s) ,(u/e e))]
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


;                                          
;                                          
;                                          
;                                          
;                                          
;                                          
;        ;;;                               
;      ;;;;;;                              
;     ;;;       ;;;;   ;;;;; ;;;  ;;; ;;;  
;    ;;;       ;;;;;;; ;;;;;;;;;; ;;;;;;;; 
;   ;;;       ;;;  ;;; ;;; ;; ;;; ;;;  ;;; 
;   ;;;      ;;;    ;;;;;; ;; ;;; ;;;   ;;;
;   ;;;      ;;;    ;;;;;; ;; ;;; ;;;   ;;;
;   ;;;      ;;;    ;;;;;; ;; ;;; ;;;   ;;;
;    ;;;     ;;;    ;;;;;; ;; ;;; ;;;   ;; 
;    ;;;;     ;;;  ;;; ;;; ;; ;;; ;;;  ;;; 
;     ;;;;;;; ;;;;;;;  ;;; ;; ;;; ;;;;;;;  
;       ;;;;;   ;;;;   ;;; ;; ;;; ;;;;;    
;                                 ;;;      
;                                 ;;;      
;                                 ;;;      
;                                          
;                                          


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
  (define-extended-language e* esterel-standard))
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
           var ...)))))
(define (maybe-rvalue->value mrv)
  (match mrv
    [`(rvalue ,v) v]
    [v v]))

(begin-for-syntax
  (define-syntax-class msg
    (pattern _:id)
    (pattern (or _:msg ...))
    (pattern (and _:msg ...))
    (pattern (not _:msg)))
  (define-syntax-class est
    (pattern a
             #:attr exp (delay (local-expand-esterel #'a))))
  (define-syntax-class call
    (pattern e
             #:attr func (delayed-call #'e))))


;                                                                                                              
;                                                                                                              
;                                                                                                              
;                                                                                                              
;                                                     ;;                                                       
;  ;;;;;;;;                                         ;;;;                                                       
;  ;;;;;;;;                                        ;;                                                          
;     ;;     ;;;; ;;   ;;;     ;; ;;;     ;;;;   ;;;;;;;    ;;;    ;;;; ;;  ;;; ;;     ;;;    ;;;; ;;    ;;;;  
;     ;;     ;;;;;;;   ;;;;;   ;;;;;;;   ;;;;;;  ;;;;;;;   ;;;;;   ;;;;;;;  ;;;;;;;   ;;;;;   ;;;;;;;   ;;;;;; 
;     ;;       ;;;         ;;  ;;   ;;  ;;         ;;     ;;   ;;    ;;;    ;;;; ;;   ;   ;;    ;;;    ;;      
;     ;;       ;;        ;;;;  ;;   ;;   ;;;       ;;     ;;   ;;    ;;     ;;;; ;;  ;;;;;;;    ;;      ;;;    
;     ;;       ;;      ;;;;;;  ;;   ;;     ;;;     ;;     ;;   ;;    ;;     ;;;; ;;  ;;;;;;;    ;;        ;;;  
;     ;;       ;;     ;;   ;;  ;;   ;;       ;;    ;;     ;;   ;;    ;;     ;;;; ;;  ;;         ;;          ;; 
;     ;;     ;;;;;;   ;;;;;;;  ;;   ;;  ;;;;;;   ;;;;;;;   ;;;;;   ;;;;;;   ;;;; ;;   ;;;;;;  ;;;;;;   ;;;;;;  
;     ;;     ;;;;;;    ;;; ;;  ;;   ;;  ;;;;;    ;;;;;;     ;;;    ;;;;;;   ;; ; ;;     ;;;;  ;;;;;;   ;;;;;   
;                                                                                                              
;                                                                                                              
;                                                                                                              
;                                                                                                              
;     

                                                                                                         


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
    #:datum-literals (and or not)
    [(_ S:id th:est el:est)
     #`(present #,(get-signal-replacement #'S) th.exp el.exp)]
    
    [(p (not S:msg) th:est el:est)
     #'(p S el th)]
    
    [(p (and S:msg ...) th:est el:est)
     #:with S_and (generate-signal 'present_and_signal)
     #`(signal& S_and
                (par&
                 #,(for/fold ([pp #'(emit S_and)])
                             ([S (in-syntax #'(S ...))])
                     #`(p #,S #,pp nothing&))
                 (p S_and th el)))]
    [(p (or S:msg ...) th:est el:est)
     #:with S_or (generate-signal 'present_or_signal)
     #'(signal& S_or
                (par&
                 (p S (emit& S_or) nothing&)
                 ...
                 (p S_or th el)))]
    
    [(p S:msg th:expr) #'(p S th nothing&)]))

(define-esterel-form suspend&
  (syntax-parser
    [(_ S:id p:est)
     #`(suspend p.exp #,(get-signal-replacement #'S))]
    [(s S:msg p:expr p2:expr p3:expr ...)
     #`(s S (seq& p p2 p3 ...))]
    [(s S:msg p:est)
     ;; we let present do all the heavy lifting for compiling
     ;; msgs
     (define/with-syntax S_local (generate-temporary 'suspend-local-signal))
     (define/with-syntax T_local (generate-temporary 'suspend-local-trap))
     #'(trap&
        T_local
        (signal& S_local
                 (par&
                  (loop& (present& S (emit& S_local)) pause&)
                  (seq& (s S_local p) (exit& T_local)))))]))

(define-esterel-form suspend-immediate&
  (syntax-parser
    [(s c:msg p:expr)
     #'(suspend& c (present& c pause&) p)]))
(define-esterel-form seq&
  (syntax-parser
    [(_) #'nothing&]
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
    [(_) #'nothing&]
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
    [(form (S:id := e:call) p:est ...)
     #'(form S := e p ...)]
    [(form S:id := e:call p:est)
     (parameterize ([signal-replace-map (extend-signal-replace-map-for #'S)]
                    [signal-var-map (extend-signal-var-map-for #'S)])
       #`(signal #,(get-signal-replacement #'S)
               (shared #,(get-signal-var #'S) := e.func p.exp)))]
    [(form S:id := e:call p:expr ...)
     #`(form S := e.func (seq& p ...))]
    [(s (S:id) p:expr ...)
     #'(s S p ...)]
    [(s (S_1 S ...) p:expr ...)
     #'(s S_1 (s (S ...) p ...))]
    [(_ S:id p:est)
     (parameterize ([signal-replace-map (extend-signal-replace-map-for #'S)])
         #`(signal #,(get-signal-replacement #'S) p.exp))]
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
     (define/with-syntax v* (get-var-replacement #'v))
     (free-id-set-add! (normal-vars-set) #'v*)
     #`(hash-ref ENV 'v*)]))

(define-syntax delay-var*
  (syntax-parser [(_ x:id) #'x]))

(define-esterel-form cond&
  (syntax-parser
    #:literals (else)
    [(cond& [else b ...]) #'(seq& b ...)]
    [(cond& [a b ...] body ...)
     #`(if& a
            (seq& b ...)
            (cond& body ...))]
    [(cond&) #'nothing&]))

(define-esterel-form pcond&
  (syntax-parser
    #:literals (else)
    [(pcond& [else b ...]) #'(seq& b ...)]
    [(pcond& [a b ...] body ...)
     #`(present& a
                 (seq& b ...)
                 (pcond& body ...))]
    [(pcond&) #'nothing&]))

(define-esterel-form if&
  (syntax-parser
    [(_ call:call p:est q:est)
     (define/with-syntax x (generate-seqvar #'if-temp))
     #'(var x := call.func (if x p.exp q.exp))]))

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
                    (seq& (await& S) (exit& T))))]
    [(_ S:msg #:immediate p:expr ...)
     (define/with-syntax T (generate-temporary (format-id #f "~a-abort-trap"
                                                          (~a (syntax->datum #'S)))))
     #'(trap& T
              (par& (seq& (seq& p ...) (exit& T))
                    (seq& (await-immediate& S) (exit& T))))]))


(define-esterel-form weak-abort-immediate&
  (syntax-parser
    [(_ S:msg p:expr ...)
     (define/with-syntax T (generate-temporary (format-id #f "~a-abort-trap"
                                                          (~a (syntax->datum #'S)))))
     #'(trap& T
              (par& (seq& (seq& p ...) (exit& T))
                    (seq& (await-immediate& S) (exit& T))))]))

(define-esterel-form abort&
  (syntax-parser
    [(_ (n:call S:msg) p:expr ...)
     (define/with-syntax T (generate-temporary (format-id #f "~a-abort-trap"
                                                          (~a (syntax->datum #'S)))))
     (define/with-syntax S_local (generate-temporary (format-id #f "~a-abort-message"
                                                                (~a (syntax->datum #'S)))))
     #'(trap& T
              (signal& S_local
                       (par& (seq& (suspend& S_local (seq& p ...)) (exit& T))
                             (seq& (await& n S) (emit& S_local) (exit& T)))))]
    [(s S:msg p:expr ...)
     (define/with-syntax T (generate-temporary (format-id #f "~a-abort-trap"
                                                          (~a (syntax->datum #'S)))))
     #'(trap& T
              (par&
               (seq& (suspend& S p ...) (exit& T))
               (seq& (await& S) (exit& T))))
     #;
     #'(s (1 S) p ...)]))

(define-esterel-form halt&
  (syntax-parser
    [_:id #'(loop& pause&)]))

(define-esterel-form var&
  (syntax-parser
    #:datum-literals (:=)
    [(_ a:id := b:call c:est)
     (define nm (extend-var-replace-map #'a))
     (parameterize ([var-replace-map nm])
       (define/with-syntax c*
         (local-expand-esterel #'c))
       #`(var #,(get-var-replacement #'a) := b.func c*))]))

(module+ test
  (define x
    (esterel-machine
     #:inputs ()
     #:outputs ()
     (var& x := 1 (:=& x x)))))

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
              (var& v := (- n 1)
                    (seq&
                     p
                     (loop&
                      (if& (> (get-var v) 0)
                           (seq& (:=& v (- (get-var v) 1)) p)
                           (exit& T))))))]))

(define-esterel-form await&
  (syntax-parser
    [(a n:call S:msg)
     #'(suspend& (not S) (repeat& n pause&))]
    [(a (n:call S:msg))
     #'(a n S)]
    [(a S:msg)
     (define/with-syntax T (generate-temporary 'await-trap))
     #'(trap& T (loop& pause& (present& S (exit& T))))]))

(define-esterel-form await-immediate&
  (syntax-parser
    [(_ S:msg)
     #'(present& S nothing& (await& S))]))

(define-esterel-form :=&
  (syntax-parser
    [(_ v c:call)
     #`(:= #,(get-var-replacement #'v) c.func)]))
(define-esterel-form sustain&
  (syntax-parser
    [(_ S:msg) #'(loop& (emit& S) pause&)]))

(define-esterel-form every&
  (syntax-parser
    [(_ (n:call S:msg) p:expr ...)
     (define/with-syntax T (generate-temporary 'every-n))
     #'(signal& T (par& (loop& (await& n S) (emit& T))
                        (every& T p ...)))]
    [(_ S:msg p:expr ...)
     #'(seq& (await& S) (loop-each& S p ...))]
    [(_ S:msg #:immediate p:expr ...)
     #'(seq& (await-immediate& S) (loop-each& S p ...))]))

(define-esterel-form every-immediate&
  (syntax-parser
    [(_ S:msg p:expr ...)
     #'(seq& (await-immediate& S) (loop-each& S p ...))]))

(define-esterel-form run&
  (syntax-parser
    #:datum-literals (->)
    [(_ n:id [outer:id -> inner:id] ...)
     #:with generator (compile-time-machine-generator (syntax-local-value #'n))
     (quasisyntax/loc this-syntax (generator #,this-syntax [outer -> inner] ...))]))

(module+ test
  (test-case "run& pure"
    (define-esterel-machine inner
      #:inputs (I)
      #:outputs (O)
      (loop&
       (present& I (emit& O))
       pause&))
    (define outer
      (esterel-machine
       #:inputs ()
       #:outputs (O)
       (signal&
        S
        (seq&
         (emit& S)
         (run& inner [S -> I] [O -> O])))))
    (define-values (M S...)
      (eval-top outer '()))
    (check-equal? S... '(O)))
  (test-case "run& impure"
    (define-esterel-machine inner
      #:inputs (I)
      #:outputs ((O 0))
      (loop&
       (present& I (emit& O 1))
       pause&))
    (define outer
      (esterel-machine
       #:inputs ()
       #:outputs ((O 2))
       (signal&
        S
        (seq&
         (emit& S)
         (run& inner [S -> I])))))
    (define-values (M S...)
      (eval-top outer '()))
    (check-equal? S... '((O 1)))))

(define-esterel-form debug&
  (syntax-parser
    [(_ e:call)
     #'(var x := (displayln e) nothing)]))


;                                                                                   
;                                                                                   
;                                                                                   
;                                                                                   
;                                 ;;             ;;        ;;;;                     
;  ;;     ;;                      ;;             ;;         ;;;                     
;  ;;;   ;;;                      ;;             ;;          ;;                     
;   ;;   ;;   ;;;     ;;;; ;;  ;;;;;     ;;;     ;; ;;;      ;;      ;;;       ;;;; 
;   ;;   ;;   ;;;;;   ;;;;;;;  ;;;;;     ;;;;;   ;;;;;;;     ;;     ;;;;;     ;;;;; 
;   ;;   ;;      ;;     ;;;       ;;        ;;   ;;   ;;;    ;;     ;;  ;;   ;;     
;    ;; ;;        ;;    ;;        ;;         ;;  ;;    ;;    ;;    ;;   ;;   ;;;    
;    ;; ;;      ;;;;    ;;        ;;       ;;;;  ;;    ;;    ;;    ;;;;;;;    ;;;;  
;    ;; ;;    ;;;;;;    ;;        ;;     ;;;;;;  ;;    ;;    ;;    ;;;;;;;      ;;; 
;    ;; ;;   ;;   ;;    ;;        ;;    ;;   ;;  ;;   ;;     ;;    ;;            ;; 
;     ;;;    ;;;;;;;  ;;;;;;;  ;;;;;;;; ;;;;;;;  ;;;;;;   ;;;;;;;;  ;;;;;;   ;;;;;  
;     ;;;     ;;; ;;  ;;;;;;   ;;;;;;;;  ;;; ;;  ;;;;;    ;;;;;;;     ;;;    ;;;;   
;                                                                                   
;                                                                                   
;                                                                                   
;                                                                                   
;                                                                                   


(define-for-syntax exit-stack (make-parameter null))
(define-for-syntax (get-exit-code T)
  (for/sum ([k (exit-stack)]
            #:break (free-identifier=? T k))
    1))

(define-for-syntax signal-var-map (make-parameter (make-immutable-free-id-table)))
(define-for-syntax (make-signal-var-map vars)
  (make-immutable-free-id-table
   (map
    (lambda (x) (cons x (generate-sharedvar x)))
    vars)))

(define-for-syntax (extend-signal-var-map-for s)
  (hash-set (signal-var-map) s (generate-sharedvar s)))
(define-for-syntax (get-signal-var s)
  (dict-ref (signal-var-map) s
            (lambda () (raise-syntax-error #f "no data assosiated with signal" s))))
(define-for-syntax (has-signal-var? s)
  (dict-ref (signal-var-map) s #t))


(define-for-syntax (make-signal-replace-map ss)
  (make-immutable-free-id-table
   (map (lambda (x) (cons x (generate-signal x))) ss)))
(define-for-syntax signal-replace-map (make-parameter (make-signal-replace-map (list))))
(define-for-syntax (extend-signal-replace-map-for s)
  (extend-signal-replace-map-for-many (list s) (list (generate-signal s))))
(define-for-syntax (extend-signal-replace-map-for-many current new)
  (for/fold ([d (signal-replace-map)])
            ([s (in-list current)]
             [t (in-list new)])
    (dict-set d s t)))
(define-for-syntax (has-signal-replacement? s)
  (dict-ref (signal-replace-map) s #f))
(define-for-syntax (get-signal-replacement s)
  (dict-ref (signal-replace-map)
            s
            (lambda ()
              (raise-syntax-error #f "unbound signal" s))))

(define-for-syntax var-replace-map (make-parameter (make-immutable-free-id-table)))

(define-for-syntax (extend-var-replace-map var)
  (dict-set (var-replace-map) var (generate-seqvar var)))
(define-for-syntax (get-var-replacement var)
  (dict-ref (var-replace-map) var
            (lambda () (raise-syntax-error #f "variable" var))))

(define (cut-sym s)
  (string->symbol (substring (symbol->string s) 1)))

(define-for-syntax (generate-seqvar x)
  (define id (generate-temporary x))
  (format-id id "x~a" id))
(define-for-syntax (generate-sharedvar x)
  (define id (generate-temporary x))
  (format-id id "s~a" id))
(define-for-syntax (generate-signal x)
  (define id (generate-temporary x))
  (format-id id "S~a" id))



(module+ test
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
    (check-equal? S... '((O 1))))
  (test-begin
    (define-values (M S...)
      (eval-top
       (esterel-machine
        #:inputs ((I 1))
        #:outputs ((O 0))
        (signal& K
                 (present& K
                           nothing&
                           (if& (= (? I) 1)
                                (emit& O 1)
                                nothing&))))
       '()))
    (check-equal? S... '((O 1)))))
