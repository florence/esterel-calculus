#lang racket
(provide deps flow/pict)
(require pict
         pict/code
         ppict/tag
         (for-syntax syntax/parse racket/sequence racket/syntax)
         racket/hash
         data/queue)


;                                                                                            
;                                                                                            
;                                                                                            
;   ;;;;;                                                ;;;;                   ;            
;   ;;   ;;                                            ;;   ;;                  ;            
;   ;;    ;                                            ;                        ;            
;   ;;    ;;   ;;  ;;    ;;;;;   ;;      ;            ;;          ;;;;      ;;; ;     ;;;;   
;   ;;    ;;    ; ; ;        ;    ;  ;;  ;            ;;         ;;  ;;    ;;  ;;    ;;  ;;  
;   ;;    ;;    ;;  ;        ;;   ;  ;;  ;            ;         ;;    ;   ;;    ;    ;    ;  
;   ;;    ;;    ;;        ;;;;;   ;  ;;  ;            ;         ;;    ;   ;;    ;   ;;    ;  
;   ;;    ;;    ;        ;   ;;   ; ; ; ;;            ;;        ;;    ;   ;;    ;   ;;;;;;;  
;   ;;    ;;    ;       ;;   ;;   ; ; ; ;             ;;        ;;    ;   ;;    ;   ;;       
;   ;;    ;     ;       ;;   ;;   ;;;  ;;              ;        ;;    ;   ;;    ;    ;       
;   ;;  ;;;     ;       ;;  ;;;    ;;  ;;              ;;   ;;   ;;  ;;    ;;  ;;    ;;   ;  
;   ;;;;;      ;;;;      ;;;; ;    ;;  ;;                ;;;;     ;;;;      ;;; ;     ;;;;   
;                                                                                            
;                                                                                            
;                                                                                            
;                                                                                            
;                                                                                            

(define prog/c
  (let ([e/c (recursive-contract prog/c #:flat)])
    (or/c
     (and/c symbol?
            (not/c symbol-interned?)
            (or/c (compose (curry string=? "pause") symbol->string)
                  (compose (curry string=? "nothing") symbol->string)))
     (list/c 'nothing)
     (list/c 'pause)
     (list/c 'present symbol? e/c e/c)
     (list/c 'signal symbol? e/c)
     (list/c 'seq e/c e/c)
     (list/c 'par e/c e/c)
     (list/c 'emit symbol?)
     (list/c 'exit natural?)
     (list/c 'trap e/c)
     (list/c 'loop e/c))))
     
   

(define-syntax taged-code
  (syntax-parser
    [(_ x)
     (define-values (pict term hash defs)
       (let loop ([x #'x]
                  [hash #'(hasheq)]
                  [defs null])
         (syntax-parse x
           #:datum-literals (present emit nothing pause)
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
           [(~and (~or pause nothing) x)
            #:with tag (generate-temporary)
            #:with term (generate-temporary)
            #:with E* (quasisyntax/loc #'x (#,#'unsyntax (tag-pict (code x) tag)))
            (values (quasisyntax/loc this-syntax E*)
                    #',term
                    #`(hash-set #,hash term tag)
                    (list*
                     #'(define tag (gensym))
                     #`(define term
                         (string->uninterned-symbol
                          #,(symbol->string (syntax-e #'x))))
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
            (values this-syntax this-syntax hash defs)])))
     #`(let ()
         #,@(reverse defs)
         (values (code #,pict)
                 `#,term
                 #,hash))]))

(define (draw-deps pict code map)
  (for*/fold ([p pict])
             ([(from* tos) (in-hash (hash-union/append (cfg code) (dfg code)))]
              [to* (in-list tos)]
              [to (in-value (hash-ref map (flow-term to*) #f))]
              [from (in-value (hash-ref map from* #f))]
              #:when (and from to))
    (pin-arrow-line
     10
     p
     (find-tag* p from)
     lc-find
     (find-tag* p to)
     lc-find)))

(define-syntax deps
  (syntax-parser
    [(_ code)
     #'(let-values ([(a b c) (taged-code code)])
         (draw-deps a b c))]))



;                                
;                                
;                                
;      ;;;;    ;;;;;;;    ;;;;   
;    ;;   ;;   ;;        ;;   ;  
;    ;         ;;       ;;       
;   ;;         ;;       ;;       
;   ;;         ;;       ;        
;   ;          ;;       ;        
;   ;          ;;;;;;   ;   ;;;; 
;   ;;         ;;       ;     ;; 
;   ;;         ;;       ;     ;; 
;    ;         ;;       ;;    ;; 
;    ;;   ;;   ;;        ;;   ;; 
;      ;;;;    ;;         ;;;;;  
;                                
;                                
;                                
;                                
;                                


(struct flow (term)
  #:transparent)
(struct true-flow flow ()
  #:transparent)
(struct false-flow flow ()
  #:transparent)
(struct K-flow flow (index)
  #:transparent)
(struct data-flow flow ()
  #:transparent)
(struct war-flow data-flow ()
  #:transparent)
(struct raw-flow data-flow ()
  #:transparent)

(define (K0-split l)
  (for/fold ([K0 empty]
             [r empty])
            ([l (in-list l)])
    (match l
      [(K-flow t 0)
       (values (cons t K0) r)]
      [_ (values K0 (cons l r))])))

(define (swap-term t l)
  (values
   (flow-term l)
   (match l
     [(K-flow _ n) (K-flow t n)]
     [(true-flow _) (true-flow t)]
     [(false-flow _) (false-flow t)])))

(define/contract (cfg term)
  (-> prog/c (and/c hash? hash-eq? immutable?))
  (define-values (head graph tails)
    (let loop ([term term])
      (match term
        [(? (lambda (x) (and (symbol? x)
                             (not (symbol-interned? x))
                             (or
                              (string=? (symbol->string x) "pause")
                              (string=? (symbol->string x) "nothing")))))
         (values term (hasheq) (list (K-flow term 0)))]
        [(or `(emit ,_) `(nothing))
         (values term (hasheq) (list (K-flow term 0)))]
        [`(pause)
         (values 'exit (hasheq) (list (K-flow 'start 0)))]
        [`(exit ,n)
         (values term (hasheq) (list (K-flow term (+ n 2))))]
        [`(present ,S ,p ,q)
         (define-values (p-head p-graph p-tails)
           (loop p))
         (define-values (q-head q-graph q-tails)
           (loop q))
         (values term
                 (hash-set
                  (hash-union/append p-graph q-graph)
                  term (list (true-flow p-head) (false-flow q-head)))
                 (append p-tails q-tails))]
        [`(seq ,p ,q)
         (define-values (p-head p-graph p-tails)
           (loop p))
         (define-values (q-head q-graph q-tails)
           (loop q))
         (define-values (pK0 p-tails*)
           (K0-split p-tails))
         (define inner
           (hash-union/append
            p-graph
            q-graph))
         (values
          p-head
          (for/fold ([inner inner])
                    ([pK0 (in-list pK0)])
            (hash-cons inner pK0 (K-flow q-head 0)))
          (append p-tails* q-tails))]
        [`(par ,p ...)
         (define-values (heads graph tails)
           (for/fold ([heads empty]
                      [graph (hasheq)]
                      [tails empty])
                     ([p (in-list p)])
             (define-values (ph pg pt) (loop p))
             (values (cons ph heads)
                     (hash-union/append graph pg)
                     (cons pt tails))))
         #|
We handle join by creating one join
 node for each possible set of return codes,
and passing *those* on. This encodes the control dependencies
between an par an its future children based on its return codes
|#
         (define j '(join))
         ;; Step 1, add the edges from the fork node
         (define graph+fork (hash-append graph term (map (lambda (x) (K-flow x 0)) heads)))
         ;; step 2, compute possible return codes
         ;; from a static approx of the equasion from Can, K = {max(k_i ...) | k_i ∈ Can_K(p_i) ... }
         (define kodes
           (for/fold ([current (map K-flow-index (first tails))])
                     ([a (in-list (rest tails))])
             (for*/list ([t1 (in-list a)]
                         [k2 (in-list current)])
               (max (K-flow-index t1) k2))))
         ;; step 3: map each flow to any kode it might help result in
         ;; (which are all kodes >= its kode).
         (define parents+flows
           (for*/fold ([mapping (apply hash (append-map (lambda (x) (list x empty)) kodes))])
                      ([ts (in-list tails)]
                       [t (in-list ts)]
                       [(k l) (in-hash mapping)]
                       #:when (>= k (K-flow-index t)))
             (hash-set mapping k (cons t l))))
         ;; step 4: build the actual nodes
         (define k-nodes
           (for/hash ([(k _) (in-hash parents+flows)])
             (values k `(join ,k))))
         ;; step 5: add the connections to the graph
         (define graph+fork+join
           (for*/fold ([g graph+fork])
                      ([(k ls) (in-hash parents+flows)]
                       [l (in-list ls)])
             (define-values (in out)
               (swap-term (hash-ref k-nodes k) l))
             (hash-cons g in out)))
         (values
          term
          graph+fork+join
          (for/list ([(K node) (in-hash k-nodes)])
            (K-flow node K)))]
        [`(trap ,p)
         (define-values (head graph tails)
           (loop p))
         (values head
                 graph
                 (for/list ([t (in-list tails)])
                   (match t
                     [(or (K-flow _ 0)
                          (K-flow _ 1))
                      t]
                     [(K-flow x 2)
                      (K-flow x 0)]
                     [(K-flow x n)
                      (K-flow x (sub1 n))])))]
        [`(signal ,S ,p)
         (loop p)]
        [`(loop ,p)
         (define-values (head graph tails)
           (loop p))
         (values head graph
                 (for/list ([t (in-list tails)]
                            #:when (match t [(K-flow _ 0) #f] [_ #t]))
                   t))])))
  (for/fold ([graph graph])
            ([l (in-list tails)])
    (define-values (n r) (swap-term 'exit l))
    (hash-append* graph
                  'start (list (K-flow head 0))
                  n (list r)
                  'entry (list (true-flow 'start)
                               (false-flow 'exit)))))


;                                
;                                
;                                
;   ;;;;;      ;;;;;;;    ;;;;   
;   ;;   ;;    ;;        ;;   ;  
;   ;;    ;    ;;       ;;       
;   ;;    ;;   ;;       ;;       
;   ;;    ;;   ;;       ;        
;   ;;    ;;   ;;       ;        
;   ;;    ;;   ;;;;;;   ;   ;;;; 
;   ;;    ;;   ;;       ;     ;; 
;   ;;    ;;   ;;       ;     ;; 
;   ;;    ;    ;;       ;;    ;; 
;   ;;  ;;;    ;;        ;;   ;; 
;   ;;;;;      ;;         ;;;;;  
;                                
;                                
;                                
;                                
;                            

;; This is a very dumb algorithm that doesn't account
;; for suface/depth breaks or pruning based on Can.
(define (dfg t)
  (define em (get-emits t))
  (define ps (get-presents t))
  (for*/fold ([h (hasheq)])
             ([(S es) (in-hash em)]
              [e (in-list es)]
              [p (in-list (hash-ref ps S empty))])
    (hash-cons h e (raw-flow p))))

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

;                                
;                                
;                                
;   ;;;;;     ;;;;;       ;;;;   
;   ;;   ;;   ;;   ;;    ;;   ;  
;   ;;    ;   ;;    ;   ;;       
;   ;;    ;;  ;;    ;;  ;;       
;   ;;    ;;  ;;    ;;  ;        
;   ;;    ;;  ;;    ;;  ;        
;   ;;    ;;  ;;    ;;  ;   ;;;; 
;   ;;    ;;  ;;    ;;  ;     ;; 
;   ;;    ;;  ;;    ;;  ;     ;; 
;   ;;    ;   ;;    ;   ;;    ;; 
;   ;;  ;;;   ;;  ;;;    ;;   ;; 
;   ;;;;;     ;;;;;       ;;;;;  
;                                
;                                
;                                
;                                
;                                
    

;; Data Dependence graphs here are just adding write-after-read
;; deps to the data-flow graph.
(define (ddg term)
  (ddg-from-dfg (dfg term)))

(define (ddg-from-dfg dfg)
  ;; TODO actually implement
  dfg)

;                                
;                                
;                                
;      ;;;;   ;;;;;       ;;;;   
;    ;;   ;;  ;;   ;;    ;;   ;  
;    ;        ;;    ;   ;;       
;   ;;        ;;    ;;  ;;       
;   ;;        ;;    ;;  ;        
;   ;         ;;    ;;  ;        
;   ;         ;;    ;;  ;   ;;;; 
;   ;;        ;;    ;;  ;     ;; 
;   ;;        ;;    ;;  ;     ;; 
;    ;        ;;    ;   ;;    ;; 
;    ;;   ;;  ;;  ;;;    ;;   ;; 
;      ;;;;   ;;;;;       ;;;;;  
;                                
;                                
;                                
;                                
;                                

(define (cdg term)
  (cdg-from-cfg
   (cfg term)))

(define (postdominator-tree-from-cfg cfg)
  (define rcfg (reverse-cfg cfg))
  (define idom (immediate-postdominators-from-rcfg-and-cfg cfg rcfg))
  (define-values (pdt pdtt) (postdominator-tree+traversal cfg idom))
  pdt)

(define (cdg-from-cfg cfg)
  (define rcfg (reverse-cfg cfg))
  (define idom (immediate-postdominators-from-rcfg-and-cfg cfg rcfg))
  (define-values (pdt pdtt) (postdominator-tree+traversal cfg idom))
  (define rdf (dominance-frontier-from-postdominator-tree-traversal rcfg pdt pdtt idom))
  (cdg-from-reverse-dominance-frontier rdf))

(define (cdg-from-reverse-dominance-frontier rdf)
  ;; See "Static Single Assignment Form and the Control Dependence Graph" page 477
  (for*/fold ([h (hasheq)])
             ([(y* x*s) (in-hash rdf)]
              [x* (in-list x*s)])
    (define-values (x y) (swap-term y* x*))
    (hash-cons h x y)))

(define (dominance-frontier-from-postdominator-tree-traversal rcfg pdt pdtt idom)
  ;; See "Static Single Assignment Form and the Control Dependence Graph" page 466, fig 10
  (for/fold ([df (hasheq)])
            ([x (in-list pdtt)])
    (define (not-idom-by-x? y)
      (not (eq? x (idom (flow-term y)))))
    (define df+x (hash-set df x empty))
    (define df+y
      (for/fold ([df df+x])
                ([y (in-list (hash-ref rcfg x empty))]
                 #:when (not-idom-by-x? y))
        (hash-cons df x y)))
    (define df+z
      (for*/fold ([df df+y])
                 ([z (hash-ref pdt x)]
                  [y (in-list (hash-ref df+y z))]
                  #:when (not-idom-by-x? y))
        (hash-cons df x y)))       
    df+z))
  
(define (immediate-postdominators-from-rcfg-and-cfg cfg rcfg)
  (define pd
    (postdominators-from-reverse-cfg-and-rcfg cfg rcfg))
  (define (immediate-dominator n)
    (define ds (hash-ref pd n))
    (define l
      (for/list ([d (in-set ds)]
                 #:when (not (eq? d n))
                 #:when
                 (for/and ([d2 (in-set ds)]
                           #:when (not (eq? d2 n)))
                   (set-member? (hash-ref pd d)
                                d2)))
        d))
    (unless (pair? l)
      (pretty-display pd)
      (pretty-display n)
      (error 'immediate-postdom "No immediate post-dominators!"))
    (unless (empty? (rest l))
      (pretty-display pd)
      (pretty-display (list n l))
      (error 'immediate-postdom "Multiple immediate post-dominators!"))
    (first l))
  immediate-dominator)

;; CFG -> (listof Node)
;; get the nodes of the CFG of post-domainator-tree in bottom-up traversal order
;; this is a fairly niave algorithm, don't care to make it fast
(define (postdominator-tree+traversal cfg idom)
  (define nodes (hash-keys cfg))
  (define start 'exit)
  (define q (make-queue))
  (enqueue! q start)
  (let loop ([res (list start)]
             [tree (hasheq)])
    (cond [(queue-empty? q) (values tree res)]
          [else
           (define h (dequeue! q))
           (define idoms
             (filter (lambda (x) (eq? h (idom x)))
                     nodes))
           (for ([x (in-list idoms)])
             (enqueue! q x))
           (loop (append idoms res)
                 (hash-set tree h idoms))])))
                
  

(define (strictify-dominators ds)
  (for/hasheq ([(d s) (in-hash ds)])
    (values d
            (set-remove s d))))

(define (postdominators-from-reverse-cfg-and-rcfg cfg rcfg)
  
  ;; Dominator dataflow equations:
  ;; out[B] = FB(in[B]), for all B
  ;; in[B] = ∩{out[B’] | B’∈pred(B)}, for all B
  ;; in[Bs] = {}
  ;; where FB(X) = X ⋃ {B}
  ;; and the top of the latice is all nodes

  ;; This simplifies to:
  ;;  dom(n0)= {n0}
  ;;  dom(n) = ∩{ dom(m) | m ∈ pred(n) } ∪ {n}
  ;; (see http://pages.cs.wisc.edu/~fischer/cs701.f08/lectures/Lecture19.4up.pdf)
  
  ;; We don't have cycles so we could do this
  ;; in a single pass with the right traversal order
  ;; but im lazy and the fixed point should only need a
  ;; constant number of passes so whatever

  (define start 'exit)
  (define nodes (set->list (list->seteq (append (hash-keys cfg) (hash-keys rcfg)))))
  (let loop ([todo nodes]
             [in (hasheq start empty)]
             [out (hasheq)])
    (cond
      [(empty? todo) out]
      [else
       (define B (first todo))
       (define preds (map flow-term (hash-ref cfg B empty)))
       (define succs (map flow-term (hash-ref rcfg B empty)))
       (define B-in
         (let ([all (for/list ([p (in-list preds)])
                      (list->seteq (hash-ref out p nodes)))])
           (if (empty? all)
               (seteq)
               (apply set-intersect all))))
       (define new-in
         (hash-set in B B-in))
       (define new-out
         (hash-set out B (set-union B-in (seteq B))))
       
       (loop
        (append
         (if (and (equal? in new-in)
                  (equal? out new-out))
             empty
             succs)
         (rest todo))
        new-in
        new-out)])))
         
(define (reverse-cfg cfg)
  (for*/fold ([r (hasheq)])
             ([(t* f*s) (in-hash cfg)]
              [f* (in-list f*s)])
    (define-values (f t) (swap-term t* f*))
    (hash-cons r f t)))
   


;                                                                        
;                                                                        
;                                                                        
;   ;;    ;                ;                                             
;   ;;    ;                ;                                             
;   ;;    ;                ;                                             
;   ;;    ;     ;;;;       ;       ; ;;;      ;;;;     ;;  ;;     ;;;;   
;   ;;    ;    ;;  ;;      ;       ;;  ;;    ;;  ;;     ; ; ;    ;    ;  
;   ;;;;;;;    ;    ;      ;       ;    ;    ;    ;     ;;  ;    ;       
;   ;;    ;   ;;    ;      ;       ;    ;   ;;    ;     ;;       ;;      
;   ;;    ;   ;;;;;;;      ;       ;    ;   ;;;;;;;     ;         ;;;;   
;   ;;    ;   ;;           ;       ;    ;   ;;          ;            ;;  
;   ;;    ;    ;           ;       ;    ;    ;          ;             ;  
;   ;;    ;    ;;   ;      ;       ;;  ;;    ;;   ;     ;       ;;   ;;  
;   ;;    ;     ;;;;        ;;;    ;;;;;      ;;;;     ;;;;      ;;;;;   
;                                  ;                                     
;                                  ;                                     
;                                  ;                                     
;                                                                        
;                                                                        


(define (↓k map)
  (for/fold ([m2 (hash)])
            ([(k v) (in-hash map)])
    (match k
      [0 (hash-append m2 0 v)]
      [1 (hash-set m2 1 v)]
      [2 (hash-append m2 0 v)]
      [n (hash-set m2 (sub1 n) v)])))

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
(define (hash-append* h . r)
  (let loop ([r r]
             [h h])
    (match r
      [(list) h]
      [(list* a b r)
       (loop
        r
        (hash-append h a b))])))

(define (hash-union/append h1 h2)
  (hash-union h1 h2 #:combine append))

(define (find-tag* p t)
  (define x (find-tag p t))
  (unless x (error 'find-tag "could not find tag ~a" t))
  x)

;                                          
;                                          
;                          ;;              
;     ;;;;                 ;;          
;    ;;   ;                               
;   ;;                                    
;   ;;         ;    ;    ;;;;              
;   ;          ;    ;       ;              
;   ;          ;    ;       ;              
;   ;   ;;;;   ;    ;       ;              
;   ;     ;;   ;    ;       ;              
;   ;     ;;   ;    ;       ;              
;   ;;    ;;   ;    ;       ;              
;    ;;   ;;   ;   ;;       ;              
;     ;;;;;    ;;;; ;    ;;;;;;            
;                                          
;                                          
;                                          
;                                          
;                                          
(require racket/gui mrlib/graph
         framework)

(define (flow->label l)
  (match l
    [(K-flow _ n) (~a n)]
    [(true-flow _) "T"]
    [(false-flow _) "F"]
    [(data-flow _) ""]))
(define (term->node-string c)
  (match c
    [`(emit ,S) (~a `(emit ,S))]
    [(or `(nothing) `(exit ,_) `(pause)
         (? (lambda (x) (and (symbol? x)
                             (not (symbol-interned? x))
                             (or
                              (string=? (symbol->string x) "pause")
                              (string=? (symbol->string x) "nothing"))))))
     ""]
    [`(present ,S ,p ,q) (~a `(? ,S))]
    ['(join) "join"]
    [`(par ,p ...) "par"]
    ['exit "exit"]
    [_ (~a c)]))

(define (graph-pastboard-from-map make-admin! control data
                                  #:position? [position? #t])
  (define terms
    (sort
     (set->list
      (for*/seteq ([(c fs) (in-hash (hash-union/append control data))]
                   [t (in-list (cons c (map flow-term fs)))])
        t))
     ;; there is still a slight non-deterministic
     ;; ordering here for when the same term
     ;; shows up twice. Could use a
     ;; program-traversal order instead
     ;; if this is ever annoying.
     string<?
     #:key ~a
     #:cache-keys? #t))
  (define-values (snips snips-ordering)
    (for/fold ([h (hasheq)]
               [ordering empty])
              
              ([c (in-list terms)])
      (define t (new text%))
      (send t insert
            (term->node-string c)
            0)
      (values
       (hash-set
        h
        c
        (new graph-editor-snip%
             [editor t]))
       (cons c ordering))))
  (define (add-links* map)
    (for* ([(c links) (in-hash map)]
           [l (in-list links)])
      (define color
        (if (data-flow? l)
            "red"
            "blue"))
      (add-links (hash-ref snips c)
                 (hash-ref snips (flow-term l))
                 (send the-pen-list find-or-create-pen color 0 'solid)
                 (send the-pen-list find-or-create-pen color 0 'solid)
                 (send the-brush-list find-or-create-brush color 'solid)
                 (send the-brush-list find-or-create-brush color 'solid)
                 (flow->label l))))
  (add-links* control)
  (define p (new (graph-pasteboard-mixin pasteboard%)))
  (make-admin! p)
  (send p begin-edit-sequence)
  (send p set-draw-arrow-heads? #t)
  (for ([k (in-list snips-ordering)])
    (define s (hash-ref snips k))
    (send p insert s)
    (send s set-margin 15 15 15 15))
  (when position? (dot-positioning p))
  (for ([(_ s) (in-hash snips)])
    (send s set-margin 5 5 5 5))
  (send p end-edit-sequence)
  (add-links* data)
  p)

(define (graph-gui-from-mapping! ac control data)
  (graph-pastboard-from-map
   (lambda (p)
     (new editor-canvas%
          [parent ac]
          [editor p]))
   control data)
  (void))

(define graph-editor-snip% (graph-snip-mixin editor-snip%))

(define (flow-graph c)
  (define f (new (frame:basic-mixin frame%)
                 [label ""]
                 [min-width 800]
                 [min-height 600]))
  (graph-gui-from-mapping! (send f get-area-container) (cfg c) (dfg c))
  (send f show #t))

(define (dependence-graph c)
  (dependence-graph-from-pfg (cfg c) (dfg c)))

(define (graph c)
  (define f (new (frame:basic-mixin frame%)
                 [label ""]
                 [min-width 800]
                 [min-height 600]))
  (define h (new horizontal-panel% [parent (send f get-area-container)]))
  (define t
    (new racket:text%))
  (send t insert
        (with-output-to-string
          (lambda ()
            (parameterize ([pretty-print-columns 40])
              (pretty-display c)))))
  (define ec
    (new editor-canvas%
         [parent h]
         [editor t]))
  (define c-cfg (cfg c))
  (graph-gui-from-mapping! h (hash-remove c-cfg 'entry) (dfg c))
  (graph-gui-from-mapping! h (cdg-from-cfg c-cfg) (ddg c))
  (queue-callback (lambda ()
                    (send t freeze-colorer)
                    (send t lock #t)
                    (send f show #t))
                  #f))

(define (graph-from-pfg cfg dfg)
  (define f (new (frame:basic-mixin frame%)
                 [label ""]
                 [min-width 800]
                 [min-height 600]))
  (define h (new horizontal-panel%
                 [parent (send f get-area-container)]))
  (graph-gui-from-mapping! h (hash-remove cfg 'entry) dfg)
  (graph-gui-from-mapping! h (cdg-from-cfg cfg) (ddg-from-dfg dfg))
  (send f show #t))

(define (flow-graph-from-pfg cfg dfg)
  (define f (new (frame:basic-mixin frame%)
                 [label ""]
                 [min-width 800]
                 [min-height 600]))
  (graph-gui-from-mapping! (send f get-area-container) cfg dfg)
  (send f show #t))

(define (dependence-graph-from-pfg cfg dfg)
  (define f (new (frame:basic-mixin frame%)
                 [label ""]
                 [min-width 800]
                 [min-height 600]))
  (graph-gui-from-mapping! (send f get-area-container) (cdg-from-cfg cfg) (ddg-from-dfg dfg))
  (send f show #t))


;                                                    
;                                                    
;                                                    
;                ;;                                  
;    ;;;;;       ;;                                  
;    ;    ;;                        ;;               
;    ;     ;                        ;;               
;    ;     ;   ;;;;        ;;;;   ;;;;;;;     ;;;;;  
;    ;     ;      ;       ;   ;;    ;;       ;;   ;  
;    ;     ;      ;      ;;         ;;       ;       
;    ;    ;;      ;      ;          ;;       ;;;     
;    ;;;;;;       ;      ;          ;;         ;;;   
;    ;            ;      ;          ;;            ;  
;    ;            ;      ;          ;;            ;; 
;    ;            ;      ;;   ;      ;  ;    ;   ;;  
;    ;         ;;;;;;;     ;;;;;      ;;;;  ;;;;;;   
;                                                    
;                                                    
;                                                    
;                                                    
;                                                    

(define (flow/pict code)
  (define code* (uniquify code))
  (pict-from-mapping (hash-remove (cfg code*) 'entry) (dfg code*)))

(define (uniquify code)
  (match code
    ['nothing (string->uninterned-symbol "nothing")]
    ['pause (string->uninterned-symbol "pause")]
    [(list x ...) (map uniquify x)]
    [atom atom]))

(require (only-in rackunit require/expose))

(require/expose
 mrlib/private/dot
 (snip-info run-dot))

(define (for-snips pb f)
  (let loop ([n #f])
    (match (send pb find-next-selected-snip n)
      [#f (void)]
      [p (f p) (loop p)])))
(define-syntax (or-2v stx)
  (syntax-case stx ()
    [(_ arg)
     (syntax arg)]
    [(_ arg args ...)
     (syntax
      (let-values ([(one two) arg])
        (if (and one two)
            (values one two)
            (or-2v args ...))))]))
(define (pict-from-mapping control data)
  (local-require pict ppict/tag)
  (define all (hash-union/append control data))
  (define terms
    (sort
     (set->list
      (for*/seteq ([(c fs) (in-hash all)]
                   [t (in-list (cons c (map flow-term fs)))])
        t))
     ;; there is still a slight non-deterministic
     ;; ordering here for when the same term
     ;; shows up twice. Could use a
     ;; program-traversal order instead
     ;; if this is ever annoying.
     string<?
     #:key ~a
     #:cache-keys? #t))
  (define-values (ids revids)
    (for/fold ([id 0]
               [h1 (hasheq)]
               [h2 (hasheq)]
               #:result (values h1 h2))
              ([t (in-list (reverse terms))])
      (values (add1 id)
              (hash-set h1 t id)
              (hash-set h2 id t))))
  (define info
    (for/hash ([t (in-list terms)])
      (define id (hash-ref ids t))
      (define p (frame
                 (inset
                  (text (term->node-string t))
                  5)))
      (define links (hash-ref all t empty))
      (values 
       id
       (list p
             (+ 30 (pict-width p))
             (+ 30 (pict-height p))
             (map (compose (lambda (x) (hash-ref ids x))
                           flow-term)
                  links)))))       
  (define max-width
    (for/fold ([m 0])
              ([(_ l) (in-hash info)])
      (match-define (list _ w _ _) l)
      (max m w)))
  (define-values (positions max-y) (run-dot (find-dot #f) info dot-label #f))
  (define max-x
    (for/fold ([m 0])
              ([l (in-list positions)])
      (match-define (list id x y) l)
      (max m (+ x max-width))))
  (define base (blank max-x max-y))
  (define tags
    (for/hash ([(id _) (in-hash info)])
      (values id (gensym))))
  (define with-images
    (for/fold ([p base])
              ([item (in-list positions)])
      (match-define (list id x y) item)
      (match-define (list p* _ _ _) (hash-ref info id))
      (define tag (hash-ref tags id))
      (pin-over
       p
       x (- max-y y)
       (tag-pict p* tag))))
  (define with-arrows
    (for*/fold ([p with-images])
               ([(id l) (in-hash info)]
                [child-id (in-list (list-ref l 3))]
                #:unless (= id child-id))
      (define f (hash-ref tags id))
      (define t (hash-ref tags child-id))
      (define pf (find-tag p f))
      (define pt (find-tag p t))
      (define-values (lf tf) (lt-find p pf))
      (define-values (lt tt) (lt-find p pt))
      (define-values (rf bf) (rb-find p pf))
      (define-values (rt bt) (rb-find p pt))
      (define-values (x1 y1) (cc-find p pf))
      (define-values (x2 y2) (cc-find p pt))
      (define-values (from-x from-y)
        (or-2v (find-intersection x1 y1 x2 y2 
                                  lf tf rf tf)
               (find-intersection x1 y1 x2 y2 
                                  lf bf rf bf)
               (find-intersection x1 y1 x2 y2 
                                  lf tf lf bf)
               (find-intersection x1 y1 x2 y2 
                                  rf tf rf bf)))
      (define-values (to-x to-y)
        (or-2v (find-intersection x1 y1 x2 y2 
                                  lt tt rt tt)
               (find-intersection x1 y1 x2 y2 
                                  lt bt rt bt)
               (find-intersection x1 y1 x2 y2 
                                  lt tt lt bt)
               (find-intersection x1 y1 x2 y2 
                                  rt tt rt bt)))
      (define term1 (hash-ref revids id))
      (define term2 (hash-ref revids child-id))
      (define flow
        (for/first ([x (in-list (hash-ref all term1))]
                    #:when (eq? term2 (flow-term x)))
          x))
      (define color
        (if (data-flow? flow)
            "red"
            "blue"))
      (if (not (and from-x from-y to-x to-y))
          p
          (pin-arrow-line
           5
           p
           pf
           (lambda (a b) (values from-x from-y))
           pt
           (lambda (a b) (values to-x to-y))
           #:start-angle (and (data-flow? flow) (degrees->radians 15))
           #:end-angle (and (data-flow? flow) (degrees->radians (- 180 15)))
           #:color color
           #:line-width 1
           #:under? #t
           #:label (text (flow->label flow))))))
  with-arrows)

;; find-intersection : number^8 -> (values (or/c #f number) (or/c #f number))
;; calculates the intersection between two line segments, 
;; described as pairs of points. Returns #f if they do not intersect
(define (find-intersection x1 y1 x2 y2 x3 y3 x4 y4)
  (let-values ([(m1 b1) (find-mb x1 y1 x2 y2)]
               [(m2 b2) (find-mb x3 y3 x4 y4)])
    (let-values ([(int-x int-y)
                  (cond
                    [(and m1 m2 b1 b2
                          (= m1 0)
                          (= m2 0))
                     (values #f #f)]
                    [(and m1 m2 b1 b2
                          (= m1 0))
                     (let* ([y y1]
                            [x (/ (- y b2) m2)])
                       (values x y))]
                    [(and m1 m2 b1 b2
                          (= m2 0))
                     (let* ([y y3]
                            [x (/ (- y b1) m1)])
                       (values x y))]
                    [(and m1 m2 b1 b2
                          (not (= m1 m2)))
                     (let* ([y (/ (- b2 b1) (- m1 m2))]
                            [x (/ (- y b1) m1)])
                       (values x y))]
                    [(and m1 b1)
                     (let* ([x x3]
                            [y (+ (* m1 x) b1)])
                       (values x y))]
                    [(and m2 b2)
                     (let* ([x x1]
                            [y (+ (* m2 x) b2)])
                       (values x y))]
                    [else 
                     (values #f #f)])])
        
      (if (and int-x
               int-y
               (<= (min x1 x2) int-x (max x1 x2))
               (<= (min y1 y2) int-y (max y1 y2))
               (<= (min x3 x4) int-x (max x3 x4))
               (<= (min y3 y4) int-y (max y3 y4)))
          (values int-x int-y)
          (values #f #f)))))
  ;; find-mb : number number number number -> (values (or/c #f number) (or/c #f number))
  ;; finds the "m" and "b" constants that describe the
  ;; lines from (x1, y1) to (x2, y2)
  (define (find-mb x1 y1 x2 y2)
    (if (= x1 x2)
        (values #f #f)
        (let-values ([(xl yl xr yr)
                      (if (x1 . <= . x2)
                          (values x1 y1 x2 y2)
                          (values x2 y2 x1 y1))])
          (let* ([m (/ (- yr yl) (- xr xl))]
                 [b (- y1 (* m x1))])
            (values m b)))))

#|
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
|#
#;
(scale
 (hc-append
  (deps 
   (signal SO
     (signal SB   
       (present S2
                (signal SE
                  (seq
                   (seq (emit SE)
                        (present SE (emit SB) (nothing)))
                   (present SB (nothing) (emit S2))))
                (nothing)))))
  (deps
   (signal SO
     (signal SB   
       (present S2
                (signal SE
                  (seq
                   (seq (emit SE)
                        (present SE (nothing) (emit SB)))
                   (present SB (emit S2) (nothing))))
                (nothing))))))
 2)
#;
(flow-graph
 '(signal SO
    (signal SB   
      (present S2
               (signal SE
                 (seq
                  (seq (emit SE)
                       (present SE (emit SB) (nothing)))
                  (present SB (nothing) (emit S2))))
               (nothing)))))
#;
(dependence-graph
 '(signal SO
    (signal SB   
      (present S2
               (signal SE
                 (seq
                  (seq (emit SE)
                       (present SE (emit SB) (nothing)))
                  (present SB (nothing) (emit S2))))
               (nothing)))))
#;
(graph
 '(signal SO
    (signal SB   
      (present S2
               (signal SE
                 (seq
                  (seq (emit SE)
                       (present SE (emit SB) (nothing)))
                  (present SB (nothing) (emit S2))))
               (nothing)))))

(define h
  (hasheq
   'entry (list (true-flow 'start) (false-flow 'exit))
   'start (list (K-flow 1 0))
   1 (list (true-flow 2) (false-flow 3))
   2 (list (true-flow 4) (false-flow 5))
   3 (list (true-flow 5) (false-flow 7))
   4 (list (K-flow 6 0))
   5 (list (K-flow 6 0))
   6 (list (K-flow 7 0))
   7 (list (K-flow 'exit 0))))

(define h2
  (hasheq
   'entry (list (true-flow 'start) (false-flow 'exit))
   'start (list (K-flow 1 0))
   1 (list (K-flow 2 0))
   2 (list (true-flow 3) (false-flow 4)
           (K-flow 1 0)
           (K-flow 7 0))
   3 (list (K-flow 5 0))
   4 (list (K-flow 5 0))
   5 (list (true-flow 4) (false-flow 6))
   6 (list (K-flow 2 0))
   7 (list (K-flow 'exit 0))))

(define h3
  (hasheq
   'entry (list (true-flow 'P) (false-flow 'exit))
   'P (list (true-flow 'X=T) (false-flow 'X=F))
   'X=T (list (K-flow 'A 0))
   'X=F (list (K-flow 'A 0))
   'A (list (K-flow 'B 0))
   'B (list (K-flow 'C 0))
   'C (list (K-flow 'X 0))
   'X (list (true-flow 'D) (false-flow 'E))
   'D (list (K-flow 'F 0))
   'E (list (K-flow 'F 0))
   'F (list (K-flow 'exit 0))))

(define h4
  (hasheq
   'entry (list (true-flow 'start)
                (false-flow 'exit))
   'start (list (K-flow 1 0))
   1 (list (K-flow 2 0))
   2 (list (true-flow 1) (false-flow 'exit))))

(define h5
  (hasheq
   'entry (list (true-flow 1) (false-flow 'exit))
   1 (list (true-flow 1) (false-flow 2))
   2 (list (K-flow 'exit 0))))

#;(graph-from-pfg h (hasheq))
#;(graph-from-pfg h2 (hasheq))
#;
(graph '(signal S1
          (present S1
                   (par
                    (signal S2
                      (seq (emit S2)
                           (present S2
                                    (nothing)
                                    (emit S1))))
                    (signal S3
                      (seq (emit S3)
                           (present S3
                                    (nothing)
                                    (emit S1)))))
                   (nothing))))
#;
(graph '(signal S1
          (present S1
                   (par
                    (signal S2
                      (seq (emit S2)
                           (present S2
                                    (nothing)
                                    (emit S1))))
                    (signal S3
                      (seq (pause)
                           (present S3
                                    (nothing)
                                    (emit S1)))))
                   (nothing))))
