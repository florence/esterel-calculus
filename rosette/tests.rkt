#lang rosette/safe
(require
  "sem-sig.rkt"
  "interp-sig.rkt"
  "interp-unit.rkt"
  "three-valued-unit.rkt"
  "pos-neg-unit.rkt"
  "shared.rkt"
  (only-in "../main.rkt" convert-P)
  racket/unit
  rackunit
  (only-in redex/reduction-semantics
           term))

(test-case "three valued"
  (define-values/invoke-unit/infer
    (export interp^ sem^)
    (link three-valued@ interp@))
  (test-case "basic verify equality"
    (define-symbolic I1* boolean?)
    (define-symbolic I2* boolean?)
    (define I (if I1* '⊥ I2*))
    (check-true
     (unsat?
      (verify
       (assert
        (result=? (eval `((O ,'⊥) (L ,'⊥) (I ,I))
                        `((O ,(lambda (x) (deref x 'L)))
                          (L ,(lambda (x) (deref x 'I)))))
                  (eval `((O ,'⊥) (I ,I))
                        `((O ,(lambda (x) (deref x 'I)))))))))))
  (check-equal?
   (eval `((O ,'⊥) (L ,'⊥) (I ,#t))
         `((O ,(lambda (x) (deref x 'L)))
           (L ,(lambda (x) (deref x 'I)))))
   `((O ,#t) (L ,#t) (I ,#t)))
  (check-equal?
   (eval `((O ,'⊥) (L ,'⊥) (I ,#f))
         `((O ,(lambda (x) (deref x 'L)))
           (L ,(lambda (x) (deref x 'I)))))
   `((O ,#f) (L ,#f) (I ,#f)))
  (check-equal?
   (eval `((O ,'⊥) (L ,'⊥) (I ,'⊥))
         `((O ,(lambda (x) (deref x 'L)))
           (L ,(lambda (x) (deref x 'I)))))
   `((O ,'⊥) (L ,'⊥) (I ,'⊥)))
  
  (check-true
   (result=?
    (eval `((O ,'⊥) (L ,'⊥) (I ,#t))
          `((O ,(lambda (x) (deref x 'L)))
            (L ,(lambda (x) (deref x 'I)))))
    `((O ,#t) (L ,#t) (I ,#t))))
  (check-true
   (result=?
    (eval `((O ,'⊥) (L ,'⊥) (I ,#f))
          `((O ,(lambda (x) (deref x 'L)))
            (L ,(lambda (x) (deref x 'I)))))
    `((O ,#f) (L ,#f) (I ,#f))))
  (check-true
   (result=?
    (eval `((O ,'⊥) (L ,'⊥) (I ,'⊥))
          `((O ,(lambda (x) (deref x 'L)))
            (L ,(lambda (x) (deref x 'I)))))
    `((O ,'⊥) (L ,'⊥) (I ,'⊥))))
  (test-case "formula building"
    (define f (build-formula `((O = L) (L = I))))
    (check-equal?
     (eval `((O ,'⊥) (L ,'⊥) (I ,#t))
           f)
     `((O ,#t) (L ,#t) (I ,#t)))
    (check-equal?
     (eval `((O ,'⊥) (L ,'⊥) (I ,#f))
           f)
     `((O ,#f) (L ,#f) (I ,#f)))
    (check-equal?
     (eval `((O ,'⊥) (L ,'⊥) (I ,'⊥))
           f)
     `((O ,'⊥) (L ,'⊥) (I ,'⊥)))
    (check-true
     (result=?
      (eval `((O ,'⊥) (L ,'⊥) (I ,#t))
            f)
      `((O ,#t) (L ,#t) (I ,#t))))
    (check-true
     (result=?
      (eval `((O ,'⊥) (L ,'⊥) (I ,#f))
            f)
      `((O ,#f) (L ,#f) (I ,#f))))
    (check-true
     (result=?
      (eval `((O ,'⊥) (L ,'⊥) (I ,'⊥))
            f)
      `((O ,'⊥) (L ,'⊥) (I ,'⊥)))))
  (check-true
   (outputs=?
    (eval `((a ⊥)) (build-formula `((a = (or true true)))))
    (eval `((a ⊥)) (build-formula `((a = (or true true)))))))
  (check-false
   (outputs=?
    (eval (build-state `((O = (not L)) (L = I)) `((I ,#f)))
          (build-formula `((O = (not L)) (L = I))))
    (eval (build-state `((O = I)) `((I ,#f)))
          (build-formula `((O = I))))))
  (check-false
   (result=?
    (eval (build-state `((O = (not L)) (L = I)) `((I ,#f)))
          (build-formula `((O = (not L)) (L = I))))
    (eval (build-state `((O = I)) `((I ,#f)))
          (build-formula `((O = I))))))
  (check-false
   (result=?
    (eval (build-state `((O = (not L)) (L = I)) `((I ,#t)))
          (build-formula `((O = (not L)) (L = I))))
    (eval (build-state `((O = I)) `((I ,#t)))
          (build-formula `((O = I))))))
  (check-true
   (result=?
    (eval (build-state `((O = (not L)) (L = I)) `((I ⊥)))
          (build-formula `((O = (not L)) (L = I))))
    (eval (build-state `((O = I)) `((I ⊥)))
          (build-formula `((O = I))))))
     
  (test-case "verification"
    (let ()
      (define s (build-state `((O = L) (L = I))
                             (symbolic-inputs `((O = L) (L = I)))))
      (define f (build-formula `((O = L) (L = I))))
      (check-true
       (unsat?
        (verify
         (assert
          (equal?
           (deref
            (eval s f)
            'O)
           (deref s 'I))))))
      (check-true
       (unsat?
        (verify
         #:assume (assert (equal? (deref s 'I) '⊥))
         #:guarantee
         (assert (not (constructive? (eval s f))))))))
    (let ()
      (define s (build-state `((O = I))
                             (symbolic-inputs `((O = I)))))
      (define f (build-formula `((O = I))))
      (check-true
       (unsat?
        (verify
         (assert
          (equal?
           (deref
            (eval s f)
            'O)
           (deref s 'I))))))
      (check-true
       (unsat?
        (verify
         #:assume (assert (equal? (deref s 'I) '⊥))
         #:guarantee
         (assert (not (constructive? (eval s f))))))))
    
    (check-true
     (unsat?
      (verify-same
       `((O = L) (L = I))
       `((O = I)))))

    (check-true
     (sat?
      (verify-same
       `((O = (not L)) (L = I))
       `((O = I)))))
    (test-case "pinning tests"
      (define p1
        '(
          ;; these come from then nothing
          (l0 = GO)
          (lsel = false)
          ;; SEL
          (SEL = (or lsel rsel))
          ;; the synchonizer
          (K0 = (and left0 (and right0 both0)))
          (left0 = (or l0 lem))
          (right0 = (or r0 rem))
          (lem = (and SEL (and RES (not lsel))))
          (rem = (and SEL (and RES (not rsel))))
          (both0 = (or l0 r0))))
      (define p2 '((K0 = r0) (SEL = rsel)))
      (check-true
       (sat?
        (verify-same p1 p2))))))


;                                                                               
;                                                                               
;                                                                               
;                                                                               
;    ;;;;;;                                     ;;;    ;                        
;    ;;   ;;                                    ;;;    ;                        
;    ;;    ;;                                   ;;;;   ;                      ; 
;    ;;    ;;    ;;;;       ;;;;;               ;;;;   ;      ;;;;      ;;;;;;; 
;    ;;    ;;   ;;   ;;    ;;   ;;              ;; ;   ;    ;;   ;;    ;;  ;;   
;    ;;    ;;   ;    ;;    ;                    ;; ;;  ;    ;     ;    ;    ;;  
;    ;;   ;;   ;;     ;    ;;                   ;; ;;  ;    ;     ;   ;;    ;;  
;    ;;;;;;    ;;     ;     ;;;;      ;;;;;;;   ;;  ;; ;   ;;;;;;;;    ;    ;;  
;    ;;        ;;     ;       ;;;               ;;  ;; ;   ;;          ;;   ;   
;    ;;        ;;     ;         ;;              ;;   ; ;    ;           ;;;;;   
;    ;;         ;    ;;         ;;              ;;   ;;;    ;;         ;        
;    ;;         ;;  ;;;    ;;  ;;;              ;;    ;;    ;;;  ;;    ;;       
;    ;;          ;;;;     ; ;;;;                ;;    ;;      ;;;;      ;;;;;;  
;                                                                            ;; 
;                                                                     ;;     ;; 
;                                                                     ;;    ;;  
;                                                                      ;;;;;;   
;                                                                               


(test-case "Pos Neg"
  (define-values/invoke-unit/infer
    (export interp^ sem^)
    (link pos-neg@ interp@))
  (test-case "basic verify equality"
    (define-symbolic \+I boolean?)
    (define-symbolic \-I boolean?)
    
    (check-true
     (unsat?
      (verify
       (assert
        (result=? (eval `(((+ O) ,#f)
                          ((- O) ,#f)
                          ((+ L) ,#f)
                          ((- L) ,#f)
                          ((+ I) ,\+I)
                          ((- I) ,\-I))
                        `(((+ O) ,(lambda (x) (deref x '(+ L))))
                          ((- O) ,(lambda (x) (deref x '(- L))))
                          ((+ L) ,(lambda (x) (deref x '(+ I))))
                          ((- L) ,(lambda (x) (deref x '(- I))))))
                  (eval `(((+ O) ,#f)
                          ((- O) ,#f)
                          ((+ I) ,\+I)
                          ((- I) ,\-I))
                        `(((+ O) ,(lambda (x) (deref x '(+ I))))
                          ((- O) ,(lambda (x) (deref x '(- I))))))))))))
  (check-equal?
   (eval `(((+ O) ,#f)
           ((- O) ,#f)
           ((+ L) ,#f)
           ((- L) ,#f)
           ((+ I) ,#t)
           ((- I) ,#f))
         `(((+ O) ,(lambda (x) (deref x '(+ L))))
           ((- O) ,(lambda (x) (deref x '(- L))))
           ((+ L) ,(lambda (x) (deref x '(+ I))))
           ((- L) ,(lambda (x) (deref x '(- I))))))
   `(((+ O) ,#t)
     ((- O) ,#f)
     ((+ L) ,#t)
     ((- L) ,#f)
     ((+ I) ,#t)
     ((- I) ,#f)))
  (check-equal?
   (eval `(((+ O) ,#f)
           ((- O) ,#f)
           ((+ L) ,#f)
           ((- L) ,#f)
           ((+ I) ,#f)
           ((- I) ,#t))
         `(((+ O) ,(lambda (x) (deref x '(+ L))))
           ((- O) ,(lambda (x) (deref x '(- L))))
           ((+ L) ,(lambda (x) (deref x '(+ I))))
           ((- L) ,(lambda (x) (deref x '(- I))))))
   `(((+ O) ,#f)
     ((- O) ,#t)
     ((+ L) ,#f)
     ((- L) ,#t)
     ((+ I) ,#f)
     ((- I) ,#t)))
  (check-equal?
   (eval `(((+ O) ,#f)
           ((- O) ,#f)
           ((+ L) ,#f)
           ((- L) ,#f)
           ((+ I) ,#f)
           ((- I) ,#f))
         `(((+ O) ,(lambda (x) (deref x '(+ L))))
           ((- O) ,(lambda (x) (deref x '(- L))))
           ((+ L) ,(lambda (x) (deref x '(+ I))))
           ((- L) ,(lambda (x) (deref x '(- I))))))
   `(((+ O) ,#f)
     ((- O) ,#f)
     ((+ L) ,#f)
     ((- L) ,#f)
     ((+ I) ,#f)
     ((- I) ,#f)))
  
  (check-true
   (result=?
    (eval `(((+ O) ,#f)
            ((- O) ,#f)
            ((+ L) ,#f)
            ((- L) ,#f)
            ((+ I) ,#t)
            ((- I) ,#f))
          `(((+ O) ,(lambda (x) (deref x '(+ L))))
            ((- O) ,(lambda (x) (deref x '(- L))))
            ((+ L) ,(lambda (x) (deref x '(+ I))))
            ((- L) ,(lambda (x) (deref x '(- I))))))
    `(((+ O) ,#t)
      ((- O) ,#f)
      ((+ L) ,#t)
      ((- L) ,#f)
      ((+ I) ,#t)
      ((- I) ,#f))))
  (check-true
   (result=?
    (eval `(((+ O) ,#f)
            ((- O) ,#f)
            ((+ L) ,#f)
            ((- L) ,#f)
            ((+ I) ,#f)
            ((- I) ,#t))
          `(((+ O) ,(lambda (x) (deref x '(+ L))))
            ((- O) ,(lambda (x) (deref x '(- L))))
            ((+ L) ,(lambda (x) (deref x '(+ I))))
            ((- L) ,(lambda (x) (deref x '(- I))))))
    `(((+ O) ,#f)
      ((- O) ,#t)
      ((+ L) ,#f)
      ((- L) ,#t)
      ((+ I) ,#f)
      ((- I) ,#t))))
  (check-true
   (result=?
    (eval `(((+ O) ,#f)
            ((- O) ,#f)
            ((+ L) ,#f)
            ((- L) ,#f)
            ((+ I) ,#f)
            ((- I) ,#f))
          `(((+ O) ,(lambda (x) (deref x '(+ L))))
            ((- O) ,(lambda (x) (deref x '(- L))))
            ((+ L) ,(lambda (x) (deref x '(+ I))))
            ((- L) ,(lambda (x) (deref x '(- I))))))
    `(((+ O) ,#f)
      ((- O) ,#f)
      ((+ L) ,#f)
      ((- L) ,#f)
      ((+ I) ,#f)
      ((- I) ,#f))))
  (test-case "formula building"
    (define f (build-formula (term (convert-P ((O = L) (L = I))))))
    (check-equal?
     (eval `(((+ O) ,#f)
             ((- O) ,#f)
             ((+ L) ,#f)
             ((- L) ,#f)
             ((+ I) ,#t)
             ((- I) ,#f))
           f)
     `(((+ O) ,#t)
       ((- O) ,#f)
       ((+ L) ,#t)
       ((- L) ,#f)
       ((+ I) ,#t)
       ((- I) ,#f)))
    (check-equal?
     (eval `(((+ O) ,#f)
             ((- O) ,#f)
             ((+ L) ,#f)
             ((- L) ,#f)
             ((+ I) ,#f)
             ((- I) ,#t))
           f)
     `(((+ O) ,#f)
       ((- O) ,#t)
       ((+ L) ,#f)
       ((- L) ,#t)
       ((+ I) ,#f)
       ((- I) ,#t)))
    (check-equal?
     (eval `(((+ O) ,#f)
             ((- O) ,#f)
             ((+ L) ,#f)
             ((- L) ,#f)
             ((+ I) ,#f)
             ((- I) ,#f))
           f)
     `(((+ O) ,#f)
       ((- O) ,#f)
       ((+ L) ,#f)
       ((- L) ,#f)
       ((+ I) ,#f)
       ((- I) ,#f)))
    (check-true
     (result=?
      (eval `(((+ O) ,#f)
              ((- O) ,#f)
              ((+ L) ,#f)
              ((- L) ,#f)
              ((+ I) ,#t)
              ((- I) ,#f))
            f)
      `(((+ O) ,#t)
        ((- O) ,#f)
        ((+ L) ,#t)
        ((- L) ,#f)
        ((+ I) ,#t)
        ((- I) ,#f))))
    (check-true
     (result=?
      (eval `(((+ O) ,#f)
              ((- O) ,#f)
              ((+ L) ,#f)
              ((- L) ,#f)
              ((+ I) ,#f)
              ((- I) ,#t))
            f)
      `(((+ O) ,#f)
        ((- O) ,#t)
        ((+ L) ,#f)
        ((- L) ,#t)
        ((+ I) ,#f)
        ((- I) ,#t))))
    (check-true
     (result=?
      (eval `(((+ O) ,#f)
              ((- O) ,#f)
              ((+ L) ,#f)
              ((- L) ,#f)
              ((+ I) ,#f)
              ((- I) ,#f))
            f)
      `(((+ O) ,#f)
        ((- O) ,#f)
        ((+ L) ,#f)
        ((- L) ,#f)
        ((+ I) ,#f)
        ((- I) ,#f)))))
  (check-true
   (outputs=?
    (eval `(((+ a) #f) ((- a) #f))
          (build-formula (term (convert-P ((a = (or true true)))))))
    (eval `(((+ a) #f) ((- a) #f))
          (build-formula (term (convert-P ((a = (or true true)))))))))
  (check-false
   (outputs=?
    (eval (build-state (term (convert-P ((O = (not L)) (L = I))))
                       `(((+ I) #f)
                         ((- I) #t)))
          (build-formula `((O = (not L)) (L = I))))
    (eval (build-state (term (convert-P ((O = I))))
                       `(((+ I) #f)
                         ((- I) #t)))
          (build-formula (term (convert-P ((O = I))))))))
  (check-false
   (result=?
    (eval (build-state (term (convert-P ((O = (not L)) (L = I))))
                       `(((+ I) #f)
                         ((- I) #t)))
          (build-formula (term (convert-P ((O = (not L)) (L = I))))))
    (eval (build-state (term (convert-P ((O = I))))
                       `(((+ I) #f)
                         ((- I) #t)))
          (build-formula (term (convert-P ((O = I))))))))
  (check-false
   (result=?
    (eval (build-state (term (convert-P ((O = (not L)) (L = I))))
                       `(((+ I) #t)
                         ((- I) #f)))
          (build-formula (term (convert-P ((O = (not L)) (L = I))))))
    (eval (build-state (term (convert-P ((O = I))))
                       `(((+ I) #t)
                         ((- I) #f)))
          (build-formula (term (convert-P ((O = I))))))))
  (check-true
   (result=?
    (eval (build-state (term (convert-P ((O = (not L)) (L = I))))
                       `(((+ I) #f)
                         ((- I) #f)))
          (build-formula (term (convert-P ((O = (not L)) (L = I))))))
    (eval (build-state (term (convert-P ((O = I))))
                       `(((+ I) #f)
                         ((- I) #f)))
          (build-formula (term (convert-P ((O = I))))))))
     
  (test-case "verification"
    (let ()
      (define m (term (convert-P ((O = L) (L = I)))))
      (define s (build-state m (symbolic-inputs m)))
      (define f (build-formula m))
      (check-true
       (unsat?
        (verify
         (assert
          (equal?
           (deref
            (eval s f)
            '(+ O))
           (deref s '(+ I)))))))
      (check-true
       (unsat?
        (verify
         (assert
          (equal?
           (deref
            (eval s f)
            '(- O))
           (deref s '(- I)))))))
      (check-true
       (unsat?
        (verify
         #:assume (assert
                   (and (equal? (deref s '(+ I)) #f)
                        (equal? (deref s '(- I)) #f)))
         #:guarantee
         (assert (not (constructive? (eval s f))))))))
    (let ()
      (define m (term (convert-P ((O = I)))))
      (define s (build-state m (symbolic-inputs m)))
      (define f (build-formula m))
      (check-true
       (unsat?
        (verify
         (assert
          (equal?
           (deref
            (eval s f)
            '(+ O))
           (deref s '(+ I)))))))
        (check-true
         (unsat?
          (verify
           (assert
            (equal?
             (deref
              (eval s f)
              '(- O))
             (deref s '(- I)))))))
        (check-true
         (unsat?
          (verify
           #:assume (assert
                     (and (equal? (deref s '(+ I)) #f)
                          (equal? (deref s '(- I)) #f)))
           #:guarantee
           (assert (not (constructive? (eval s f))))))))
    
    (check-true
     (unsat?
      (verify-same
       (term (convert-P ((O = L) (L = I))))
       (term (convert-P ((O = I)))))))
    (check-true
     (sat?
      (verify-same
       (term (convert-P ((O = (not L)) (L = I))))
       (term (convert-P ((O = I)))))))))