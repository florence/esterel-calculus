#lang racket
(provide compile-esterel
         compile-esterel/get-registers
         run/circuit)
(require esterel-calculus/circuits
         esterel-calculus/circuits/rosette
         esterel-calculus/redex/model/shared
         redex/reduction-semantics
         "rosette/sem-sig.rkt"
         "rosette/interp-sig.rkt"
         "rosette/interp-unit.rkt"
         "rosette/three-valued-unit.rkt"
         (prefix-in r: racket/base))

(module+ test (require rackunit))
(module+ rename
  (provide rename*)
  (define-metafunction L+
    rename* : any [c:a any] ... -> any
    [(rename* c:a _ ... [c:a c:b] _ ...)
     c:b]
    [(rename* (c:a = any_e) _ ... [c:a any] _ ...)
     ,(error 'rename "~a cannot be renamed to ~a" (term (c:a = any_e)) (term any))
     (side-condition
      (not (redex-match? L+ c:a (term any))))]
    [(rename* c:a _ ... [c:a any] _ ...)
     any]
    [(rename* (any ...) [c:a any_2] ...)
     ((rename* any [c:a any_2] ...) ...)]
    [(rename* any _ ...) any]))


;                                              
;                                              
;                                              
;         ;;                                   
;         ;;                                   
;         ;;                 ;                 
;         ;;                 ;                 
;     ;;;;;;    ;;;;;     ;;;;;;;     ;;;;;    
;    ;;  ;;;    ;   ;;       ;        ;   ;;   
;    ;    ;;         ;;      ;             ;;  
;   ;;    ;;         ;;      ;             ;;  
;   ;;    ;;     ;;;;;;      ;         ;;;;;;  
;   ;;    ;;    ;;   ;;      ;        ;;   ;;  
;   ;;    ;;   ;;    ;;      ;       ;;    ;;  
;    ;    ;;   ;;    ;;      ;       ;;    ;;  
;    ;;  ;;;    ;;  ;;;      ;;  ;    ;;  ;;;  
;     ;;;  ;    ;;;;  ;       ;;;;    ;;;;  ;  
;                                              
;                                              
;                                              
;                                              
;                                              


(define-extended-language constructive+ constructive
  (a ::= .... (K n))
  (n k ::= natural)
  (entropy ::= any))

(define-extended-language esterel-eval+ esterel-eval
  (p ::= .... (nts variable natural)
     (loop* p)))

(define-union-language L+
  (e: esterel-eval+)
  (c: constructive+))

(define-metafunction L+
  compile-esterel/get-registers : e:p -> (c:P ((c:a c:a) ...))
  [(compile-esterel/get-registers e:p)
   (compile-esterel/get-registers/entropy e:p ())])

(define-metafunction L+
  compile-esterel/get-registers/entropy : e:p c:entropy -> (c:P ((c:a c:a) ...))
  [(compile-esterel/get-registers/entropy e:p c:entropy_extra)
   ((rename* c:P
             [(K c:n) c:a] ...)
    ((c:a_1 c:a_2) ...))
   (where/error (c:P _ (c:n ...) ((c:a_1 c:a_2) ...))
                (compile e:p (c:entropy_extra ,(flatten (term e:p)))))
   (where/error ((c:n c:a) ...)
                ,(for/list ([x (in-list (term (c:n ...)))])
                   (list x (string->symbol (~a "K" x)))))])

(define-metafunction L+
  compile-esterel : e:p -> c:P
  [(compile-esterel e:p)
   c:P
   (where/error (c:P _)
                (compile-esterel/get-registers e:p))])

(define-values/invoke-unit/infer
  (export (prefix three-valued: interp^)
          (prefix three-valued: sem^))
  (link interp@ three-valued@))
(define (run/circuit p ins outs inputs)
  (define extended-inputs
    (for/list ([i (in-list inputs)])
      (append
       (map (lambda (x) `(,x #t)) i)
       (for/list ([x (in-list ins)]
                  #:when (not (member x i)))
         `(,x #f)))))
  (define p++regs (term (compile-esterel/top ,p)))
  (define results
    (three-valued:eval/multi*
     extended-inputs
     (first p++regs)
     (second p++regs)))
  (define (get-outputs x)
    (for/set ([o (in-list outs)]
              #:when (eq? #t (second (assoc o x))))
      o))
  (let process ([r results])
    (match r
      [(list) empty]
      [(cons x r)
       (cond
         [(not (three-valued:constructive? x))
          (build-list (length (cons x r)) (const #f))]
         [else
          (cons (get-outputs x)
                (process r))])])))

(define-metafunction L+
  compile-esterel/top : e:p -> (c:P ((c:a c:a) ...))
  [(compile-esterel/top e:p)
   ((++/P
     c:P
     ((GO = (not c:a_reg-out))
      (c:a_reg-in = (not false))
      (RES = true)
      (SUSP = false)
      (KILL = false)))
    ((c:a_reg-in c:a_reg-out)
     (c:a c:b) ...))
    
   (where (c:P ((c:a c:b) ...))
          (compile-esterel/get-registers e:p))
   (where c:a_reg-out (afresh reg-out c:P))
   (where c:a_reg-in (afresh reg-out (c:a_reg-out . c:P)))])



;                                                                               
;                                                                               
;                                                                               
;                                                  ;;      ;;;;;                
;                                                  ;;;        ;;                
;                                                             ;;                
;                                                             ;;                
;      ;;;;      ;;;;     ; ;;  ;;    ; ;;;;     ;;;;;        ;;         ;;;;   
;     ;;  ;;    ;;   ;;   ;; ;;; ;;   ;;;  ;;       ;;        ;;       ;;   ;;  
;    ;;         ;    ;;   ;   ;  ;;   ;;   ;;       ;;        ;;       ;     ;  
;    ;         ;;     ;   ;   ;  ;;   ;     ;       ;;        ;;       ;     ;  
;    ;         ;;     ;   ;   ;  ;;   ;     ;       ;;        ;;      ;;;;;;;;  
;    ;         ;;     ;   ;   ;  ;;   ;     ;       ;;        ;;      ;;        
;    ;         ;;     ;   ;   ;  ;;   ;     ;       ;;        ;;       ;        
;    ;;         ;    ;;   ;   ;  ;;   ;    ;;       ;;        ;;       ;;       
;     ;;  ;;    ;;  ;;;   ;   ;  ;;   ;;   ;;       ;;        ;;  ;    ;;;  ;;  
;      ;;;;      ;;;;     ;   ;  ;;   ; ;;;;     ;;;;;;;       ;;;;      ;;;;   
;                                     ;                                         
;                                     ;                                         
;                                     ;                                         
;                                     ;                                         
;                                                                               


(define-metafunction L+
  compile : e:p c:entropy -> (c:P (e:S ...) (c:n ...)  ((c:a c:a) ...))
  [(compile (nts variable c:n) c:entropy)
   ((((synth variable -GO entropy) = GO)
     ((synth variable -SUSP entropy) = SUSP)
     ((synth variable -KILL entropy) = KILL)
     ((synth variable -RES entropy) = RES)
     (SEL = (synth variable -SEL entropy))
     ,@(for/list ([i (in-range 0 (add1 (term c:n)))])
         (term ((K ,i) = (synth variable K ,i entropy)))))
     
    ()
    ,(for/list ([i (in-range 0 (add1 (term c:n)))]) i)
    ())]
  [(compile nothing _)
   ((((K 0) = GO))
    ()
    (0)
    ())]
  [(compile (exit c:k) _)
   ((((K ,(+ 2 (term c:k))) = GO))
    ()
    (,(+ 2 (term c:k)))
    ())]
  [(compile (emit e:S) _)
   ((((K 0) = GO)
     (e:S = GO))
    (e:S)
    (0)
    ())]
  [(compile pause c:entropy)
   ((((K 1) = GO)
     ((K 0) = (and c:a_reg-out RES))
     (SEL = c:a_reg-out)
     (c:a_reg-in = (and (not KILL) c:a_do-sel))
     (c:a_do-sel = (or GO c:a_resel))
     (c:a_resel = (and SUSP SEL)))
    ()
    (0 1)
    ((c:a_reg-in c:a_reg-out)))
   (where/error c:a_resel (afresh resel c:entropy))
   (where/error c:a_do-sel (afresh do-sel c:entropy))
   (where/error c:a_reg-out (afresh reg-out c:entropy))
   (where/error c:a_reg-in (afresh reg-in c:entropy))]
  [(compile (present e:S e:p e:q) c:entropy)
   ((++/P ((c:a_then = (and GO e:S))
           (c:a_else = (and GO (not e:S)))
           (SEL = (or any_psel any_qsel)))
          (rename* c:P_p
                   [GO c:a_then]
                   [SEL any_psel])
          (rename* c:P_q
                   [GO c:a_else]
                   [SEL any_qsel]))
         
    (++/filter (e:S_p ...) (e:S_q ...))
    (++/filter/sort (c:n_p ...) (c:n_q ...))
    ((c:a_preg-in c:a_preg-out) ...
     (c:a_qreg-in c:a_qreg-out) ...))
   (where/error (c:P_p (e:S_p ...) (c:n_p ...) ((c:a_preg-in c:a_preg-out) ...))
                (compile e:p c:entropy))
   (where/error (c:P_q (e:S_q ...) (c:n_q ...) ((c:a_qreg-in c:a_qreg-out) ...))
                (compile e:q (c:P_p c:entropy)))
   (where/error c:entropy_r (c:P_p c:P_q c:entropy))
   (where/error ((c:k_rename c:a_prename c:a_qrename) ...)
                (get-overlap-n/rename (c:n_p ...) (c:n_q ...)
                                      c:entropy_r))
   (where/error c:entropy_r2
                (((c:k_rename c:a_prename c:a_qrename) ...)
                 .
                 c:entropy_r))
   (where/error c:a_then (afresh then c:entropy_r2))
   (where/error c:a_else (afresh else c:entropy_r2))
   (where/error any_psel (maybe-afresh c:P_p SEL pSEL-present c:entropy_r2))
   (where/error any_qsel (maybe-afresh c:P_q SEL qSEL-present c:entropy_r2))]
  [(compile (suspend e:p e:S) c:entropy)
   ((++/P ((c:a_susp-res = (and (not e:S) c:a_do-res))
           (c:a_do-res = (and any_susp-sel RES))
           (c:a_susp-susp = (or SUSP c:a_do-susp))
           (c:a_do-susp = (and e:S c:a_do-res))
           ((K 1) = (or c:a_do-susp any_k1rename)))
          (rename* c:P
                   [RES c:a_susp-res]
                   [SEL any_susp-sel]
                   [SUSP c:a_susp-susp]
                   [(K 1) any_k1rename]))
    (e:S_out ...)
    (++/filter/sort (1) (c:k_out ...))
    ((c:a_preg-in c:a_preg-out) ...))
   (where/error (c:P (e:S_out ...) (c:k_out ...) ((c:a_preg-in c:a_preg-out) ...))
                (compile e:p c:entropy))
   
   (where/error c:entropy_r (c:P . c:entropy))
   (where/error any_k1rename (maybe-rename-k 1 (c:k_out ...) c:entropy_r))
   (where/error c:a_susp-res (afresh susp-res c:entropy_r))
   (where/error c:a_do-res (afresh do-res c:entropy_r))
   (where/error any_susp-sel
                (maybe-afresh c:P SEL susp-sel c:entropy_r))
   (where/error c:a_susp-susp (afresh susp-susp c:entropy_r))
   (where/error c:a_do-susp (afresh do-susp c:entropy_r))]
  [(compile (seq e:p e:q) c:entropy)
   ((++/P (rename* c:P_p [(K 0) any_k0rename])
          (rename* c:P_q [GO any_k0rename]))
    (++/filter (e:S_p ...) (e:S_q ...))
    (++/filter/sort ,(r:remove 0 (term (c:n_p ...)))
                    (c:n_q ...))
    ((c:a_preg-in c:a_preg-out) ...
     (c:a_qreg-in c:a_qreg-out) ...))
   (where/error (c:P_p (e:S_p ...) (c:n_p ...) ((c:a_preg-in c:a_preg-out) ...))
                (compile e:p c:entropy))
   (where/error (c:P_q (e:S_q ...) (c:n_q ...) ((c:a_qreg-in c:a_qreg-out) ...))
                (compile e:q (c:P_p . c:entropy)))
   (where/error any_k0rename
                (maybe-rename-k 0 (c:n_p ...) (c:P_p c:P_q . c:entropy)))]
  [(compile (loop e:p) c:entropy)
   (compile (loop* (seq e:p e:p)) c:entropy)]
  [(compile (loop* e:p) c:entropy)
   ((++/P (((K 0) = false)
           (c:a_loop-go = (or GO any_k0rename)))
          (rename* c:P
                   [GO c:a_loop-go]
                   [(K 0) any_k0rename]))
    (e:S_out ...)
    (++/filter/sort (0) (c:k_out ...))
    ((c:a_preg-in c:a_preg-out) ...))
   (where/error (c:P (e:S_out ...) (c:k_out ...) ((c:a_preg-in c:a_preg-out) ...))
                (compile e:p c:entropy))
   (where/error c:entropy_r (c:P . c:entropy))
   (where/error any_k0rename
                (maybe-rename-k 0 (c:k_out ...) c:entropy_r))
   (where/error c:a_loop-go (afresh loop-go c:entropy_r))]
  [(compile (trap e:p) c:entropy)
   ((++/P ((c:a_trap-kill = (or KILL any_k2rename))
           ((K 0) = (or any_k0rename any_k2rename)))
          (rename* c:P
                   [KILL c:a_trap-kill]
                   [(K 0) any_k0rename]
                   [(K 2) any_k2rename]
                   [(K c:k_o) (K c:k_i)] ...))
    (e:S_out ...)
    (++/filter/sort
     (0)
     ,(map (λ (x) (match x [0 0] [1 1] [2 0] [x (- x 1)]))
           (term (c:k_out ...))))
    ((c:a_preg-in c:a_preg-out) ...))
   (where/error (c:P (e:S_out ...) (c:k_out ...) ((c:a_preg-in c:a_preg-out) ...))
                (compile e:p c:entropy))
   (where/error c:entropy_r (c:P . c:entropy))
   (where/error c:a_trap-kill (afresh trap-kill c:entropy_r))
   (where/error any_k0rename (maybe-rename-k 0 (c:k_out ...) c:entropy_r))
   (where/error any_k2rename (maybe-rename-k 2 (c:k_out ...) c:entropy_r))
   (where/error ((c:k_o c:k_i) ...) (lower-ks (c:k_out ...)))]
  [(compile (signal e:S e:p) c:entropy)
   ((rename* c:P [e:S any_srename])
    ,(filter (lambda (x) (not (eq? (term e:S) x))) (term (e:S_o ...)))
    (c:k ...)
    ((c:a_preg-in c:a_preg-out) ...))
   (where/error (c:P (e:S_o ...) (c:k ...) ((c:a_preg-in c:a_preg-out) ...))
                (compile e:p c:entropy))
   (where/error any_srename (maybe-afresh c:P e:S e:S (c:P. c:entropy)))]
  [(compile (par e:p e:q) c:entropy)
   ((++/P c:P_sync
          ((SEL = (or any_psel any_qsel)))
          (rename* c:P_p
                   [KILL c:a_outkill]
                   [SEL any_psel]
                   [(K c:n_p) c:a_prename] ...)
          (rename* c:P_q
                   [KILL c:a_outkill]
                   [SEL any_qsel]
                   [(K c:n_q) c:a_qrename] ...))
    (++/filter (e:S_p ...) (e:S_q ...))
    (++/filter/sort (c:n_p ...) (c:n_q ...))
    ((c:a_preg-in c:a_preg-out) ...
     (c:a_qreg-in c:a_qreg-out) ...))
   (where/error (c:P_p (e:S_p ...) (c:n_p ...) ((c:a_preg-in c:a_preg-out) ...))
                (compile e:p c:entropy))
   (where/error (c:P_q (e:S_q ...) (c:n_q ...) ((c:a_qreg-in c:a_qreg-out) ...))
                (compile e:q (c:P_p . c:entropy)))
   (where/error c:entropy_r (c:P_q c:P_p . c:entropy))
   (where/error any_psel (maybe-afresh c:P_p SEL psel c:entropy_r))
   (where/error any_qsel (maybe-afresh c:P_q SEL qsel c:entropy_r))
   (where/error (c:P_sync (c:a_prename ...)
                          (c:a_qrename ...)
                          c:a_outkill)
                (build-synchonizer (c:n_p ...)
                                   any_psel
                                   (c:n_q ...)
                                   any_qsel
                                   (c:a_psel c:a_qsel . c:entropy_r)))])


;                                   
;                                   
;                                   
;                                   
;                                   
;                                   
;                                   
;    ;;;;;      ;    ;;   ;;;   ;;  
;    ;   ;;     ;    ;;    ;;   ;   
;         ;;    ;    ;;     ;; ;;   
;         ;;    ;    ;;      ; ;    
;     ;;;;;;    ;    ;;      ;;     
;    ;;   ;;    ;    ;;      ;;;    
;   ;;    ;;    ;    ;;     ;; ;    
;   ;;    ;;    ;    ;;     ;  ;;   
;    ;;  ;;;    ;;  ;;;    ;;   ;;  
;    ;;;;  ;     ;;;  ;   ;;     ;; 
;                                   
;                                   
;                                   
;                                   
;                                   


(define-metafunction L+
  lower-ks : (c:k ...) -> ((c:k c:k) ...)
  [(lower-ks ()) ()]
  [(lower-ks (0 c:k ...))
   (lower-ks (c:k ...))]
  [(lower-ks (1 c:k ...))
   (lower-ks (c:k ...))]
  [(lower-ks (2 c:k ...))
   (lower-ks (c:k ...))]
  [(lower-ks (c:k_head c:k ...))
   (++ ((c:k_head ,(- (term c:k_head) 1)))
       (lower-ks (c:k ...)))])

(define-metafunction L+
  maybe-rename-k : c:k (c:k ...) c:entropy -> c:a or false
  [(maybe-rename-k c:k (c:k_out ...) c:entropy)
   ,(if (member (term c:k) (term (c:k_out ...)))
        (term (afresh ,(string->symbol (~a "K" (term c:k) "-internal")) c:entropy))
        (term false))])



(define-metafunction L+
  get-overlap-n/rename : (c:n ...) (c:n ...) c:entropy -> ((c:n c:a c:a) ...)
  [(get-overlap-n/rename () _ _) ()]
  [(get-overlap-n/rename (c:n c:k ...)
                         (c:k_1 ... c:n c:k_2 ...)
                         c:entropy)
   (++ (any)
       (get-overlap-n/rename
        (c:k ...)
        (c:k_1 ... c:n c:k_2 ...)
        (any . c:entropy)))
   (where/error any (c:n (afresh left c:entropy) (afresh right c:entropy)))]
  [(get-overlap-n/rename (c:n c:k ...)
                         (c:k_1 ...)
                         c:entropy)
   (get-overlap-n/rename
    (c:k ...)
    (c:k_1 ...)
    c:entropy)
   (where/error any (c:n (afresh left c:entropy) (afresh right c:entropy)))])

(define-metafunction L+
  synth : any ... entropy -> c:a
  [(synth any ... c:entropy)
   (afresh ,(string->symbol (apply ~a (term (any ...)))) c:entropy)])

(define-metafunction L+
  maybe-afresh : c:P variable variable c:entropy -> c:a or false
  [(maybe-afresh (_ ... [variable = _] _ ...) variable variable_1 c:entropy)
   (afresh variable_1 c:entropy)]
  [(maybe-afresh _ _ _ _)
   false])
   
(define-metafunction L+
  afresh : variable c:entropy -> c:a
  [(afresh variable c:entropy)
   ,(variable-not-in (term c:entropy) (term variable))])

(define-metafunction L+
  ++/P : c:P ... -> c:P
  [(++/P (c:e ...) ...)
   (or-duplicates (++ (c:e ...) ...))])

(define-metafunction L+
  ++/filter/sort : (c:n ...) ... -> (c:n ...)
  [(++/filter/sort (c:n ...) ...)
   ,(sort (term (++/filter (c:n ...) ...)) <)])

(define-metafunction L+
  ++/filter : (any ...) ... -> (any ...)
  [(++/filter (any ...) ...)
   ,(remove-duplicates (term (++ (any ...) ...)))])

(define-metafunction L+
  ++ : (any ...) ... -> (any ...)
  [(++ (any ...) ...)
   (any ... ...)])

(define-metafunction L+
  or-duplicates : c:P -> c:P
  [(or-duplicates ()) ()]
  [(or-duplicates ((c:a = c:p_1)
                   c:e_1 ...
                   (c:a = c:p_2)
                   c:e_2 ...))
   (or-duplicates ((c:a = (or c:p_1 c:p_2))
                   c:e_1 ...
                   c:e_2 ...))]
  [(or-duplicates ((c:a = c:p_1)
                   c:e ...))
   (++
    ((c:a = c:p_1))
    (or-duplicates (c:e ...)))])

(define-metafunction L+
  build-synchonizer : (c:n ...) any (c:n ...) any c:entropy
  -> (c:P (c:a ...) (c:a ...) c:a)
  
  [(build-synchonizer (c:n_p ...) any_psel (c:n_q ...) any_qsel c:entropy)
   ,(let ()
      (define lem (variable-not-in (term c:entropy) 'lem))
      (define rem (variable-not-in (term c:entropy) 'rem))
      (for/fold ([P (term ((,lem = (and SEL (and RES (not any_psel))))
                           (,rem = (and SEL (and RES (not any_qsel))))))]
                 [lem lem]
                 [rem rem]
                 [kill (term KILL)]
                 [left (term ())]
                 [right (term ())]
                 #:result
                 (let ([nxt
                        (variable-not-in (list P kill left right (term c:entropy))
                                         'killout)])
                   (list (cons `(,nxt = ,kill) P)
                         (reverse left)
                         (reverse right)
                         nxt)))
                ([i (in-range 0 (add1 (apply max (term (++ (c:n_p ...) (c:n_q ...))))))])
        (define ent (list P kill left right (term c:entropy)))
        (define has-left? (member i (term (c:n_p ...))))
        (define has-right? (member i (term (c:n_q ...))))
        (define lname (if has-left?
                          (variable-not-in ent 'lname)
                          'false))
        (define rname (if has-right?
                          (variable-not-in ent 'rname)
                          'false))
        (define newlem (variable-not-in ent 'lem))
        (define newrem (variable-not-in ent 'rem))
        (define newboth (variable-not-in ent 'both))
        (cond
          [(not (or has-left? has-right?))
           (values P lem rem kill left right)]
          [else
           (values
            (list*
             (term (,newlem = (or ,lem ,lname)))
             (term (,newrem = (or ,rem ,rname)))
             (term (,newboth = (or ,lname ,rname)))
             (term ((K ,i) = (and ,newlem (and ,newrem ,newboth))))
             P)
            newlem
            newrem
            (if (< i 2) kill (term (or ,kill (K ,i))))
            (if has-left? (cons lname left) left)
            (if has-right? (cons rname right) right))])))])

(define-metafunction L+
  rename* : any [c:a any] ... -> any
  [(rename* c:a _ ... [c:a c:b] _ ...)
   c:b]
  [(rename* (c:a = any_e) _ ... [c:a any] _ ...)
   ,(error 'rename "~a cannot be renamed to ~a" (term (c:a = any_e)) (term any))
   (side-condition
    (not (redex-match? L+ c:a (term any))))]
  [(rename* c:a _ ... [c:a any] _ ...)
   any]
  [(rename* (any ...) [c:a any_2] ...)
   ((rename* any [c:a any_2] ...) ...)]
  [(rename* any _ ...) any])


;                                                         
;                                                         
;                                                         
;                                                         
;   ;;;;;;;;;                                             
;       ;                               ;                 
;       ;                               ;                 
;       ;         ;;;;      ;;;;;    ;;;;;;;      ;;;;;   
;       ;       ;;   ;;    ;;   ;;      ;        ;;   ;;  
;       ;       ;     ;    ;            ;        ;        
;       ;       ;     ;    ;;           ;        ;;       
;       ;      ;;;;;;;;     ;;;;        ;         ;;;;    
;       ;      ;;             ;;;       ;           ;;;   
;       ;       ;               ;;      ;             ;;  
;       ;       ;;              ;;      ;             ;;  
;       ;       ;;;  ;;    ;;  ;;;      ;;  ;    ;;  ;;;  
;       ;         ;;;;    ; ;;;;         ;;;;   ; ;;;;    
;                                                         
;                                                         
;                                                         
;                                                         
;                                                         


(module+ test
  (test-case "renaming"
    (check-equal?
     (term
      (rename*
       ((p-GO = GO))
       [GO false]))
     (term ((p-GO = false)))))
  (test-case "direct tests"
    (check-equal?
     (term (compile-esterel nothing))
     (term ((K0 = GO))))
    (check-equal?
     (term (compile-esterel (exit 0)))
     (term ((K2 = GO))))
    (check-equal?
     (term (compile-esterel (emit Ss)))
     (term ((K0 = GO)
            (Ss = GO))))
    (check-equal?
     (term (compile-esterel (seq nothing nothing)))
     (term ((K0-internal = GO)
            (K0 = K0-internal))))
    (check-equal?
     (term (compile-esterel pause))
     (term ((K1 = GO)
            (K0 = (and reg-out RES))
            (SEL = reg-out)
            (reg-in = (and (not KILL) do-sel))
            (do-sel = (or GO resel))
            (resel = (and SUSP SEL)))))
    (check-equal?
     (term (compile-esterel (suspend nothing S)))
     (term ((susp-res = (and (not S) do-res))
            (do-res = (and false RES))
            (susp-susp = (or SUSP do-susp))
            (do-susp = (and S do-res))
            (K1 = (or do-susp false))
            (K0 = GO))))
    (check-equal?
     (term (compile-esterel (seq (exit 3) (nts q 6))))
     (term
      ((K5 = (or GO qK5))
       (q-GO = false)
       (q-SUSP = SUSP)
       (q-KILL = KILL)
       (q-RES = RES)
       (SEL = q-SEL)
       (K0 = qK0)
       (K1 = qK1)
       (K2 = qK2)
       (K3 = qK3)
       (K4 = qK4)
       (K6 = qK6))))
    (check-equal?
     (term (compile-esterel (par nothing nothing)))
     (term
      ((killout = KILL)
       (lem1 = (or lem lname))
       (rem1 = (or rem rname))
       (both = (or lname rname))
       (K0 = (and lem1 (and rem1 both)))
       (lem = (and SEL (and RES (not false))))
       (rem = (and SEL (and RES (not false))))
       (SEL = (or false false))
       (lname = GO)
       (rname = GO)))))
  (test-case "testing via verification"
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (par nothing nothing)))
      (term (compile-esterel nothing))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (par (exit 2) nothing)))
      (term (compile-esterel (exit 2)))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (par (exit 2) (exit 4))))
      (term (compile-esterel (exit 4)))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (signal Ss (present Ss (emit S1) (emit S2)))))
      (term (compile-esterel (emit S2)))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (suspend nothing Ss)))
      (term (compile-esterel nothing))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (suspend (exit 2) Ss)))
      (term (compile-esterel (exit 2)))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (trap nothing)))
      (term (compile-esterel nothing))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (trap (exit 0))))
      (term (compile-esterel nothing))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (trap (exit 4))))
      (term (compile-esterel (exit 3)))))
    (check-pred
     unsat?
     (verify-same
      #:outputs '(K0 SEL p-GO p-SUSP p-KILL p-RES q-GO q-SUSP q-KILL q-RES)
      (term (compile-esterel (par (nts p 1) (nts q 1))))
      (term (compile-esterel (par (nts q 1) (nts p 1))))))
    (check-pred
     unsat?
     (verify-same
      #:outputs '(K0 K1 K2 K3 K4 K5 SEL
                     p-GO p-SUSP p-KILL p-RES q-GO q-SUSP q-KILL q-RES)
      (term (compile-esterel (par (nts p 5) (nts q 5))))
      (term (compile-esterel (par (nts q 5) (nts p 5))))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (suspend nothing S)))
      (term (compile-esterel nothing))))
    (check-pred
     unsat?
     (verify-same
      (term (compile-esterel (suspend (par pause (exit 0)) S)))
      (term (compile-esterel (exit 0)))))
    (check-pred
     list?
     (verify-same #:outputs '(K0 K4)
                  (term (compile-esterel (suspend nothing S)))
                  (term (compile-esterel (exit 2)))))
    (check-pred
     list?
     (verify-same 
      (term (compile-esterel (signal S (present S (emit S) (emit S)))))
      (term (compile-esterel nothing))))
    (check-pred
     list?
     (verify-same
      #:outputs '(K0 K4 SEL)
      (term (compile-esterel
             (signal S
               (seq (emit S)
                    (present S (exit 2) nothing)))))
      (term (compile-esterel (exit 2)))))
    (check-pred
     list?
     (verify-same
      #:outputs '(K0 K4 SEL)
      (term (++/P
             ((GO = ⊥))
             (compile-esterel
              (signal S
                (seq (emit S)
                     (present S (exit 2) nothing))))))
      (term (++/P ((GO = ⊥)) (compile-esterel (exit 2))))))
    (check-pred
     unsat?
     (verify-same
      #:outputs '(K0 K4 SEL)
      (term (++/P
             ((GO = false))
             (compile-esterel
              (signal S
                (seq (emit S)
                     (present S (exit 2) nothing))))))
      (term (++/P ((GO = false)) (compile-esterel (exit 2))))))
    (check-pred
     unsat?
     (verify-same
      #:outputs '(K0 K4 SEL)
      (term (++/P
             ((GO = true))
             (compile-esterel
              (signal S
                (seq (emit S)
                     (present S (exit 2) nothing))))))
      (term (++/P ((GO = true)) (compile-esterel (exit 2))))))
    (check-pred
     unsat?
     (verify-same
      #:outputs '(K0 K1 K2 K3 K4)
      (term (compile-esterel (exit 2)))
      (term
       (compile-esterel
        (par (par nothing (exit 1))
             (par (exit 0)
                  (par (exit 1)
                       (exit 2))))))))
    (test-case "state and Can"
      (define p++regs
        (term
         (compile-esterel/get-registers
          (signal S2
            (seq
             (present S2 (emit S1) nothing)
             (seq pause
                  (emit S2)))))))
      (define q++regs
        (term
         (compile-esterel/get-registers/entropy
          (signal S2
            (seq
             nothing
             (seq pause
                  (emit S2))))
          ,p++regs)))
      (check-pred
       list?
       (verify-same
        #:register-pairs1 (second p++regs)
        #:register-pairs2 (second q++regs)
        #:outputs '(K0 K1 K2 S1)
        (first p++regs)
        (first q++regs)))
      (check-pred
       unsat?
       (verify-same
        #:register-pairs1 (second p++regs)
        #:register-pairs2 (second q++regs)
        #:constraints (term (implies SEL (not GO)))
        #:outputs '(K0 K1 K2 S1)
        (first p++regs)
        (first q++regs)))))

  (test-case "testing eval"
    (check-equal?
     (run/circuit
      'nothing
      '()
      '()
      '())
     '())
    (check-equal?
      (run/circuit
       'nothing
       '()
       '()
       '(()))
      (list (set)))
     (check-equal?
      (run/circuit
       'nothing
       '()
       '()
       '(() ()))
      (list (set) (set)))
     (check-equal?
      (run/circuit
       'pause
       '()
       '()
       '(() ()))
      (list (set) (set)))
     (check-equal?
      (run/circuit
       'pause
       '()
       '()
       '(() () ()))
      (list (set) (set) (set)))
     (check-equal?
      (run/circuit
       '(emit S)
       '()
       '(S)
       '(() ()))
      (list (set 'S) (set)))
     (check-equal?
      (run/circuit
       '(seq (emit S)
             (seq pause (emit S)))
       '()
       '(S)
       '(() ()))
      (list (set 'S) (set 'S)))
     (check-equal?
      (run/circuit
       '(seq (emit S)
             (seq pause (emit S)))
       '()
       '(S)
       '(() () ()))
      (list (set 'S) (set 'S) (set)))
     (check-equal?
      (run/circuit
       '(present S (emit S1) nothing)
       '(S)
       '(S1)
       '(() ()))
      (list (set) (set)))
     (check-equal?
      (run/circuit
       '(present S (emit S1) nothing)
       '(S)
       '(S1)
       '((S) ()))
      (list (set 'S1) (set)))
    (check-equal?
     (run/circuit
      (term (seq nothing (exit 0)))
      '()
      '()
      '(()))
     (list (set)))
    (test-case "internal eval issues"
      (define p++regs
        (term (compile-esterel/top (trap (seq nothing (exit 0))))))
      (check-equal?
       (length
        (three-valued:eval/multi*
         '(() () () ())
         (first p++regs)
         (second p++regs)))
       4))
    (check-equal?
     (run/circuit
      (term (trap (seq nothing (exit 0))))
      '()
      '()
      '(() () () ()))
     (list (set) (set) (set) (set)))
    (check-equal?
     (run/circuit
      (term (trap (seq (emit S) (exit 0))))
      '()
      '(S)
      '(() () () ()))
     (list (set 'S) (set) (set) (set)))
    (check-equal?
     (run/circuit
      (term (loop (seq pause (emit S))))
      '()
      '(S)
      '(() () () ()))
     (list (set) (set 'S) (set 'S) (set 'S)))
    (check-equal?
     (run/circuit
      (term (seq (trap (seq pause (seq (emit S) (exit 0))))
                 (trap (seq pause (seq (emit S) (exit 0))))))
      '()
      '(S)
      '(() () () ()))
     (list (set) (set 'S) (set 'S) (set)))
    (check-equal?
     (run/circuit
      (term (loop (trap (seq pause (seq (emit S) (exit 0))))))
      '()
      '(S)
      '(() () () ()))
     (list (set) (set 'S) (set 'S) (set 'S)))
    (check-equal?
     (run/circuit
      (term (signal S (seq (loop (present S nothing nothing)) (emit S))))
      '()
      '()
      '(()))
     (list #f))
    (check-equal?
     (run/circuit
      (term (signal S (seq (loop (present S nothing pause)) (emit S))))
      '()
      '()
      '(()))
     (list #f))))