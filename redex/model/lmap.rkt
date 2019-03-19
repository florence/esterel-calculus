#lang racket
(require esterel-calculus/redex/model/shared
         esterel-calculus/redex/model/lset
         redex/reduction-semantics)
(provide
 M<-
 M<-*
 M0
 M1
 M1*
 Mderef
 Mrestrict-range
 Mrestrict-domain
 Mrestrict-domain*
 MU
 M---κ↓
 Mdom
 Mrestrict-range-to
 Mmax*)
(module+ test (require rackunit
                       esterel-calculus/redex/rackunit-adaptor))



(define-metafunction esterel-eval
  M<- : M variable any -> M
  [(M<- () any_1 any_2)
   (M1 any_1 any_2)]
  [(M<- ((any_1 L) M) any_1 any_2)
   ((any_1 (LU L (L1set any_2))) M)]
  [(M<- ((any_3 L) M) any_1 any_2)
   ((any_3 L) (M<- M any_1 any_2))])

(define-metafunction esterel-eval
  M<-* : M variable L -> M
  [(M<-* () any_1 L)
   (M1* any_1 L)]
  [(M<-* ((any_1 L) M) any_1 L_i)
   ((any_1 (LU L L_i)) M)]
  [(M<-* ((any_3 L) M) any_1 L_i)
   ((any_3 L) (M<-* M any_1 L_i))])

(module+ test
  (test-term-equal
   (M<-* (M0)
         S1
         (L1set nothin))
   (M1 S1 nothin))
  (test-term-equal
   (M<-* (M1 S1 nothin)
         S1
         (L2set nothin nothin))
   (M<- (M2 S1 nothin nothin) S1 nothin))
  (test-term-equal
   (M<-*
    (M<-* (M1 S1 nothin)
          S1
          (L1set nothin))
    S2
    (L1set nothin))
   (M<- (M2 S1 nothin nothin) S2 nothin)))

(define-metafunction esterel-eval
  M0 : -> M
  [(M0) ()])
(define-metafunction esterel-eval
  M1 : variable any -> M
  [(M1 any_1 any_2)
   ((any_1 (L1set any_2)) (M0))])
(define-metafunction esterel-eval
  M2 : variable any any -> M
  [(M2 any_1 any_2 any_3)
   ((any_1 (L2set any_2 any_3)) (M0))])

(define-metafunction esterel-eval
  M1* : variable L -> M
  [(M1* any_1 L)
   ((any_1 L) (M0))])

(define-judgment-form esterel-eval
  #:mode     (Mderef I I        O)
  #:contract (Mderef M variable L)
  [----------
   (Mderef ((any_k L) M) any_k L)]
  [(Mderef M any_k2 L)
   (side-condition ,(not (equal? (term any_k1) (term any_k2))))
   ----------
   (Mderef ((any_k1 _) M) any_k2 L)])

(define-judgment-form esterel-eval
  #:mode     (Mderef* I I        O)
  #:contract (Mderef* M variable L)
  [----------
   (Mderef* () any_k (L0set))]
  [----------
   (Mderef* ((any_k L) M) any_k L)]
  [(Mderef* M any_k2 L)
   (side-condition ,(not (equal? (term any_k1) (term any_k2))))
   ----------
   (Mderef* ((any_k1 _) M) any_k2 L)])

(define-metafunction esterel-eval
  Mrestrict-range : M any -> M
  [(Mrestrict-range () _) ()]
  [(Mrestrict-range ((any_k L) M) any)
   (Mrestrict-range M any)
   (where () (Lset-sub L (L1set any)))]
  [(Mrestrict-range ((any_k L) M) any)
   ((any_k (Lset-sub L (L1set any)))
    (Mrestrict-range M any))])

(module+ test
  (test-term-equal
   (Mrestrict-range (M1 S1 nothin) nothin)
   (M0))
  (test-term-equal
   (Mrestrict-range
    (M<- (M1 S1 nothin) S1 paus)
    nothin)
   (M1 S1 paus)))

(define-metafunction esterel-eval
  Mrestrict-domain : M variable -> M
  [(Mrestrict-domain () any) ()]
  [(Mrestrict-domain ((any_k L) M) any_k)
   M]
  [(Mrestrict-domain ((any_k L) M) any_2)
   ((any_k L) (Mrestrict-domain M any_2))])

(module+ test
  (test-term-equal
   (Mrestrict-domain (M1 S1 nothin) S2)
   (M1 S1 nothin))
  (test-term-equal
   (Mrestrict-domain (M1 S1 nothin) S1)
   (M0))
  (test-term-equal
   (Mrestrict-domain (M0) S1)
   (M0)))

(define-metafunction esterel-eval
  Mrestrict-domain* : M (variable ...) -> M
  [(Mrestrict-domain* M ()) M]
  [(Mrestrict-domain* M (any_1 any ...))
   (Mrestrict-domain*
    (Mrestrict-domain M any_1)
    (any ...))])

(module+ test
  (let ([r
         (term
          (M<- (M<- (M<- (M0) S1 nothin)
                    S2
                    nothin)
               S3
               nothin))])
    (test-term-equal
     (Mrestrict-domain* ,r (S1 S2))
     (Mrestrict-domain
      (Mrestrict-domain ,r S1)
      S2))
    (test-term-equal
     (Mrestrict-domain* ,r (S1 S2))
     (Mrestrict-domain
      (Mrestrict-domain ,r S2)
      S1))))

(define-metafunction esterel-eval
  Mmax* : M-S-κ M-S-κ -> M-S-κ
  [(Mmax* () M-S-κ) M-S-κ]
  [(Mmax* ((S_k L-κ_1) M-S-κ_1) M-S-κ_2)
   (Mmax*
    M-S-κ_1
    (M<-*
     (Mrestrict-domain M-S-κ_2 S_k)
     S_k
     (Lmax* L-κ_1 L-κ_2)))
   (judgment-holds
    (Mderef* M-S-κ_2 S L-κ_2))])
  


(define-metafunction esterel-eval
  MU : M M -> M
  [(MU () M) M]
  [(MU ((any_k L) M_r) M)
   (MU M_r
       (M<-* M any_k L))])

(module+ test
  (test-term-equal
   (MU
    (M<-* (M1 S1 nothin)
          S1
          (L1set nothin))
    (M0))
   (M2 S1 nothin nothin))
  (test-term-equal
   (MU
    (M<-* (M1 S1 nothin)
          S1
          (L1set nothin))
    (M<-* (M1 S1 nothin)
          S1
          (L1set nothin)))
   (M<- (M<- (M2 S1 nothin nothin) S1 nothin) S1 nothin))
  (test-term-equal
   (MU
    (M<-* (M1 S1 nothin)
          S1
          (L1set nothin))
    (M<-* (M1 S2 nothin)
          S2
          (L1set nothin)))

   (M<-
    (M<- (M2 S2 nothin nothin)
         S1 nothin)
    S1 nothin)))

(define-metafunction esterel-eval
  Mdom : M -> L
  [(Mdom ()) ()]
  [(Mdom ((any _) M)) (any (Mdom M))])

(module+ test
  (test-term-equal
   (Mdom (M<- (M1 S1 nothin) S2 nothin))
   (L2set S1 S2)))

(define-metafunction esterel-eval
  Mrestrict-range-to : M any -> M
  [(Mrestrict-range-to () any) ()]
  [(Mrestrict-range-to ((any_k L) M) any)
   (Mrestrict-range-to M any)
   (judgment-holds (L¬∈ any L))]
  [(Mrestrict-range-to ((any_k L) M) any)
   ((any_k (L1set any))
    (Mrestrict-range-to M any))])
(module+ test
  (test-term-equal
   (Mrestrict-range-to (M0) nothin)
   (M0))
  (test-term-equal
   (Mrestrict-range-to (M1 S1 nothin) nothin)
   (M1 S1 nothin))
  (test-term-equal
   (Mrestrict-range-to (M1 S1 pause) nothin)
   (M0))
  (test-term-equal
   (Mrestrict-range-to (M<- (M1 S1 pause) S1 nothin) nothin)
   (M1 S1 nothin)))
  

(define-metafunction esterel-eval
  M---κ↓ : M -> M
  [(M---κ↓ ()) ()]
  [(M---κ↓ ((any_k L-κ) M))
   ((any_k (Lharp... L-κ))
    (M---κ↓ M))])

(module+ test
  (test-term-equal
   (M---κ↓ (M1 S1 0))
   (M1 S1 nothin)))

(module+ test
  (test-judgment-holds
   (Mderef (M1 S1 nothin) S1 (nothin ())))
  (test-judgment-holds
   (Mderef (M<- (M1 S1 nothin) S1 paus)
           S1
           (nothin (paus ()))))
  (test-judgment-holds
   (Mderef (M<- (M1 S1 nothin) S2 paus)
           S1
           (nothin ())))
  (test-judgment-holds
   (Mderef (M<- (M1 S1 nothin) S2 paus)
           S2
           (paus ()))))