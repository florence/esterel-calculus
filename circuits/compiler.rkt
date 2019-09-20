#lang racket
(require esterel-calculus/circuits
         esterel-calculus/circuits/rosette
         esterel-calculus/redex/model/shared
         redex/reduction-semantics)

(module+ test (require rackunit))

(define-extended-language constructive+ constructive
  (a ::= .... (K n))
  (n k ::= natural)
  (entropy ::= any))

(define-extended-language esterel-eval+ esterel-eval
  (p ::= .... (nts variable natural)))

(define-union-language L+
  (e: esterel-eval+)
  (c: constructive+))

(define-metafunction L+
  compile-esterel : e:p -> c:P
  [(compile-esterel e:p)
   (rename* c:P
            [(K c:n) c:a] ...)         
   (where/error (c:P _ (c:n ...))
                (compile e:p ,(flatten (term e:p))))
   (where/error ((c:n c:a) ...)
                ,(for/list ([x (in-list (term (c:n ...)))])
                   (list x (string->symbol (~a "K" x)))))])

(define-metafunction L+
  synth : any ... entropy -> c:a
  [(synth any ... c:entropy)
   (afresh ,(string->symbol (apply ~a (term (any ...)))) c:entropy)])

(define-metafunction L+
  compile : e:p c:entropy -> (c:P (e:S ...) (c:n ...))
  [(compile (nts variable c:n) c:entropy)
   ((((synth variable -GO entropy) = GO)
     ((synth variable -SUSP entropy) = SUSP)
     ((synth variable -KILL entropy) = KILL)
     ((synth variable -RES entropy) = RES)
     (SEL = (synth variable -SEL entropy))
     ,@(for/list ([i (in-range 0 (add1 (term c:n)))])
         (term ((K ,i) = (synth variable K ,i entropy)))))
     
    ()
    ,(for/list ([i (in-range 0 (add1 (term c:n)))]) i))]
  [(compile nothing _)
   ((((K 0) = GO))
    ()
    (0))]
  [(compile (exit c:k) _)
   ((((K ,(+ 2 (term c:k))) = GO))
    ()
    (,(+ 2 (term c:k))))]
  [(compile (emit e:S) _)
   ((((K 0) = GO)
     (e:S = GO))
    (e:S)
    (0))]
  [(compile pause c:entropy)
   ((((K 1) = GO)
     ((K 0) = (and c:a_reg-out RES))
     (SEL = c:a_reg-out)
     (c:a_reg-in = (and (not KILL) c:a_do-sel))
     (c:a_do-sel = (or GO c:a_resel))
     (c:a_resel = (and susp SEL)))
    ()
    (0 1))
   (where/error c:a_resel (afresh resel c:entropy))
   (where/error c:a_do-sel (afresh do-sel c:entropy))
   (where/error c:a_reg-out (afresh reg-out c:entropy))
   (where/error c:a_reg-in (afresh reg-in c:entropy))]
  [(compile (present e:S e:p e:q) c:entropy)
   ((++/P ((c:a_then = (and GO e:S))
           (c:a_else = (and GO (not e:S)))
           (SEL = (or c:p_sel c:q_sel)))
          (rename* c:P_p
                   [GO c:a_then]
                   [SEL c:p_sel]
                   [(K c:k_rename) c:a_prename] ...)
          (rename* c:P_p
                   [GO c:a_else]
                   [SEL c:q_sel]
                   [(K c:k_rename) c:a_prename] ...))
         
    (++/filter (e:S_p ...) (e:S_q ...))
    (++/filter/sort (c:n_p ...) (c:n_q ...)))
   (where/error (c:P_p (e:S_p ...) (c:n_p ...))
                (compile e:p c:entropy))
   (where/error (c:P_q (e:S_q ...) (c:n_q ...))
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
   (where/error c:a_else (afresh else c:entropy_r2))]
  [(compile (suspend e:p e:S) c:entropy)
   ((++/P ((c:a_susp-res = (and (not e:S) c:a_do-res))
           (c:a_do-res = (and c:a_susp-sel RES))
           (c:a_susp-susp = (or SUSP c:a_do-susp))
           (c:a_do-susp = (and e:S c:a_do-res))
           ((K 1) = (or c:a_do-susp any_k1rename)))
          (rename* c:P
                   [RES c:a_susp-res]
                   [SEL c:a_susp-sel]
                   [SUSP c:a_susp-susp]
                   [(K 1) any_k1rename]))
    (e:S_out ...)
    (c:k_out ...))
   (where/error (c:P (e:S_out ...) (c:k_out ...))
                (compile e:p c:entropy))
   
   (where/error c:entropy_r (c:P . c:entropy))
   (where/error any_k1rename (maybe-rename-k 1 (c:k_out ...) c:entropy_r))
   (where/error c:a_susp-res (afresh susp-res c:entropy_r))
   (where/error c:a_do-res (afresh do-res c:entropy_r))
   (where/error c:a_susp-sel (afresh susp-sel c:entropy_r))
   (where/error c:a_susp-susp (afresh susp-susp c:entropy_r))
   (where/error c:a_do-susp (afresh do-susp c:entropy_r))]
  [(compile (seq e:p e:q) c:entropy)
   ((++/P (rename* c:P_p [(K 0) any_k0rename])
          (rename* c:P_q [GO any_k0rename]))
    (++/filter (e:S_p ...) (e:S_q ...))
    (++/filter/sort (c:n_q ...) (c:n_q ...)))
   (where/error (c:P_p (e:S_p ...) (c:n_p ...))
                (compile e:p c:entropy))
   (where/error (c:P_q (e:S_q ...) (c:n_q ...))
                (compile e:q (c:P_p . c:entropy)))
   (where/error any_k0rename (maybe-rename-k 0 (c:n_p ...) (c:P_p c:P_q . c:entropy)))]
  [(compile (loop e:p) c:entopy)
   ((++/P (((K 0) = false)
           (c:a_loop-go = (or GO any_k0rename)))
          (rename* c:P
                   [GO c:a_loop-go]
                   [(K 0) any_k0rename]))
    (e:S_out ...)
    (++/filter (0) (c:k_out ...)))
   (where/error (c:P (e:S_out ...) (c:k_out ...))
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
    ,(map (λ (x) (match x [0 0] [1 1] [2 0] [x (- x 1)]))
          (term (c:k_out ...))))
   (where/error (c:P (e:S_out ...) (c:k_out ...))
                (compile e:p c:entropy))
   (where/error c:entropy_r (c:P . c:entropy))
   (where/error c:a_trap-kill (afresh trap-kill c:entropy_r))
   (where/error any_k0rename (maybe-rename-k 0 (c:k_out ...) c:entropy_r))
   (where/error any_k2rename (maybe-rename-k 2 (c:k_out ...) c:entropy_r))
   (where/error ((c:k_o c:k_i) ...) (lower-ks (c:k_out ...)))]
  [(compile (signal e:S e:p) c:entropy)
   ;; assuming names are unique
   (compile e:p c:entropy)]
  [(compile (par e:p e:q) c:entropy)
   ((++/P c:P_sync
          (rename* c:P_p
                   [KILL c:a_outkill]
                   [SEL c:a_psel]
                   [(K c:n_p) c:a_prename] ...)
          (rename* c:P_q
                   [KILL c:a_outkill]
                   [SEL c:a_qsel]
                   [(K c:n_q) c:a_qrename] ...))
    (++/filter (e:S_p ...) (e:S_q ...))
    (++/filter/sort (c:n_p ...) (c:n_q ...)))
   (where/error (c:P_p (e:S_p ...) (c:n_p ...))
                (compile e:p c:entropy))
   (where/error (c:P_q (e:S_q ...) (c:n_q ...))
                (compile e:q (c:P_p . c:entropy)))
   (where/error c:entropy_r (c:P_q c:P_p . c:entropy))
   (where/error c:a_psel (afresh psel c:entropy_r))
   (where/error c:a_qsel (afresh qsel c:entropy_r))
   (where/error (c:P_sync (c:a_prename ...)
                          (c:a_qrename ...)
                          c:a_outkill)
                (build-synchonizer (c:n_p ...)
                                   c:a_psel
                                   (c:n_q ...)
                                   c:a_qsel
                                   (c:a_psel c:a_qsel . c:entropy_r)))])

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
  ++/filter : (any ...) ... -> (any ...)
  [(++/filter (any ...) ...)
   ,(remove-duplicates (term (++ (any ...) ...)))])

(define-metafunction L+
  ++/filter/sort : (c:n ...) ... -> (c:n ...)
  [(++/filter/sort (c:n ...) ...)
   ,(sort (term (++/filter (c:n ...) ...)) <)])

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
  afresh : variable c:entropy -> c:a
  [(afresh variable c:entropy)
   ,(variable-not-in (term c:entropy) (term variable))])
(define-metafunction L+
  ++ : (any ...) ... -> (any ...)
  [(++ (any ...) ...)
   (any ... ...)])

(define-metafunction L+
  ++/P : c:P ... -> c:P
  [(++/P (c:e ...) ...)
   (or-duplicates (++ (c:e ...) ...))])
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
  build-synchonizer : (c:n ...) c:a (c:n ...) c:a c:entropy
  -> (c:P (c:a ...) (c:a ...) c:a)
  
  [(build-synchonizer (c:n_p ...) c:a_psel (c:n_q ...) c:a_qsel c:entropy)
   ,(let ()
      (define lem (variable-not-in (term c:entropy) 'lem))
      (define rem (variable-not-in (term c:entropy) 'rem))
      (for/fold ([P (term ((,lem = (and SEL (and RES (not c:a_psel))))
                           (,rem = (and SEL (and RES (not c:a_qsel))))))]
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
  [(rename* c:a _ ... [c:a any] _ ...)
   ,(error "dont get here")]
  [(rename* (any ...) [c:a any_2] ...)
   ((rename* any [c:a any_2] ...) ...)]
  [(rename* any _ ...) any])
              
(module+ test
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
          (resel = (and susp SEL)))))
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
    (term (compile-esterel (par (nts q 5) (nts p 5)))))))