module sn-calculus-compatconf.in-lift where

open import sn-calculus-compatconf.base

open import sn-calculus
open import utility renaming (_U̬_ to _∪_)
open import context-properties
  using (get-view ; wrap-rho ; unwrap-rho
       ; ->E-view ; E-view-main-bind ; _a~_
       ; ->E-view-term ; ->E-view-inner-term ; done-E-view-term-disjoint)

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.Binding
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Context.Properties
  using (plug)
open import Esterel.Environment as Env
  using (Env ; []env ; _←_)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; cong ; trans ; subst ; module ≡-Reasoning)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; _∷_ ; [] ; _++_ ; map)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; _,′_ ; proj₁ ; proj₂ ; _×_ ; ∃)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)

open ->E-view

open EvaluationContext1
open _≐_⟦_⟧e
open Context1
open _≐_⟦_⟧c

{-
Base case where (E , C) = (_∷_ , []). LHS is arbitrary ->E-view reduction
and RHS is a merge. This case is delegated to R-confluence.

     p
  ρθ. E⟦E₁⟦qin⟧⟧       -- sn⟶₁ ->    ρθq. E⟦E₁⟦qo⟧⟧
 (ρθ) E⟦E₂⟦ρθ'.rin⟧⟧   -- sn⟶₁ ->   (ρθ)  E⟦ρθ'.E₂⟦rin⟧⟧
-}
1-steplρ-E-view-ecin-lift : ∀{E E₁ Ei p qin q qo rin r ro θ θq BV FV} →
  {ρθ·psn⟶₁ρθq·q  :  ρ θ · p sn⟶₁ ρ θq · q} →
  CorrectBinding p BV FV →

  (p≐E⟦qin⟧  :  p ≐ (E ++ (E₁ ∷ Ei)) ⟦ qin ⟧e) →
  (q≐E⟦qo⟧   :  q ≐ (E ++ (E₁ ∷ Ei)) ⟦ qo ⟧e) →
  ->E-view  ρθ·psn⟶₁ρθq·q  p≐E⟦qin⟧  q≐E⟦qo⟧ →

  (p≐E⟦rin⟧  :  p ≐ (map ceval E) ⟦ rin ⟧c) →
  (r≐E⟦ro⟧   :  r ≐ (map ceval E) ⟦ ro ⟧c) →
  (rinsn⟶₁ro  :  rin sn⟶₁ ro) →

  ⊥

1-steplρ-E-view-ecin-lift {[]} {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  (depar₁ p'≐E⟦qin⟧) q≐E⟦qo⟧ e-view dchole dchole
  (rpar-done-right p'/halted q'/done) =
         (done-E-view-term-disjoint
           (dhalted (halted-⟦⟧e p'/halted p'≐E⟦qin⟧))
           (->E-view-inner-term e-view))

1-steplρ-E-view-ecin-lift {[]} {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  (depar₂ q'≐E⟦qin⟧) q≐E⟦qo⟧ e-view dchole dchole
  (rpar-done-right p'/halted q'/done) =
         (done-E-view-term-disjoint
           (done-⟦⟧e q'/done q'≐E⟦qin⟧)
           (->E-view-inner-term e-view))

1-steplρ-E-view-ecin-lift {[]} {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  (depar₁ p'≐E⟦qin⟧) q≐E⟦qo⟧ e-view dchole dchole
  (rpar-done-left p'/done q'/halted) =
         (done-E-view-term-disjoint
           (done-⟦⟧e p'/done p'≐E⟦qin⟧)
           (->E-view-inner-term e-view))

1-steplρ-E-view-ecin-lift {[]} {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  (depar₂ q'≐E⟦qin⟧) q≐E⟦qo⟧ e-view dchole dchole
  (rpar-done-left p'/done q'/halted) =
         (done-E-view-term-disjoint
           (dhalted (halted-⟦⟧e q'/halted q'≐E⟦qin⟧))
           (->E-view-inner-term e-view))

1-steplρ-E-view-ecin-lift {[]} {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  (deseq dehole) q≐E⟦qo⟧ () dchole dchole
  rseq-done

1-steplρ-E-view-ecin-lift {[]} {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  (deseq dehole) q≐E⟦qo⟧ () dchole dchole
  rseq-exit

1-steplρ-E-view-ecin-lift {[]} {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  (deloopˢ dehole) q≐E⟦qo⟧ () dchole dchole
  rloopˢ-exit

1-steplρ-E-view-ecin-lift {[]} {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  (desuspend p≐E⟦qin⟧) q≐E⟦qo⟧ e-view dchole dchole
  (rsuspend-done p/halted) =
         (done-E-view-term-disjoint
           (dhalted (halted-⟦⟧e p/halted p≐E⟦qin⟧))
           (->E-view-inner-term e-view))

1-steplρ-E-view-ecin-lift {[]} {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  (detrap p≐E⟦qin⟧) q≐E⟦qo⟧ e-view dchole dchole
  (rtrap-done p/halted) =
         (done-E-view-term-disjoint
           (dhalted (halted-⟦⟧e p/halted p≐E⟦qin⟧))
           (->E-view-inner-term e-view))


1-steplρ-E-view-ecin-lift {E₁ ∷ E} {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBpar cbp cbq _ _ _ _)
  (depar₁ p≐E⟦qin⟧) (depar₁ q≐E⟦qo⟧) e-view-E₁
  (dcpar₁ p≐E⟦rin⟧) (dcpar₁ r≐E⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (depar₁ p≐E⟦qin⟧) (depar₁ q≐E⟦qo⟧)
         p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view) =
  1-steplρ-E-view-ecin-lift cbp p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐E⟦rin⟧ r≐E⟦ro⟧ rinsn⟶₁ro


1-steplρ-E-view-ecin-lift {E₁ ∷ E} {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBpar cbp cbq _ _ _ _)
  (depar₂ p≐E⟦qin⟧) (depar₂ q≐E⟦qo⟧) e-view-E₁
  (dcpar₂ p≐E⟦rin⟧) (dcpar₂ r≐E⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (depar₂ p≐E⟦qin⟧) (depar₂ q≐E⟦qo⟧)
         p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view) =
  1-steplρ-E-view-ecin-lift cbq p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐E⟦rin⟧ r≐E⟦ro⟧ rinsn⟶₁ro


1-steplρ-E-view-ecin-lift {E₁ ∷ E} {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBseq cbp cbq _)
  (deseq p≐E⟦qin⟧) (deseq q≐E⟦qo⟧) e-view-E₁
  (dcseq₁ p≐E⟦rin⟧) (dcseq₁ r≐E⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (deseq p≐E⟦qin⟧) (deseq q≐E⟦qo⟧)
         p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view) =
  1-steplρ-E-view-ecin-lift cbp p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐E⟦rin⟧ r≐E⟦ro⟧ rinsn⟶₁ro


1-steplρ-E-view-ecin-lift {E₁ ∷ E} {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBloopˢ cbp cbq _ _)
  (deloopˢ p≐E⟦qin⟧) (deloopˢ q≐E⟦qo⟧) e-view-E₁
  (dcloopˢ₁ p≐E⟦rin⟧) (dcloopˢ₁ r≐E⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (deloopˢ p≐E⟦qin⟧) (deloopˢ q≐E⟦qo⟧)
         p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view) =
  1-steplρ-E-view-ecin-lift cbp p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐E⟦rin⟧ r≐E⟦ro⟧ rinsn⟶₁ro


1-steplρ-E-view-ecin-lift {E₁ ∷ E} {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBsusp cb' _)
  (desuspend p≐E⟦qin⟧) (desuspend q≐E⟦qo⟧) e-view-E₁
  (dcsuspend p≐E⟦rin⟧) (dcsuspend r≐E⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (desuspend p≐E⟦qin⟧) (desuspend q≐E⟦qo⟧)
         p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view) =
  1-steplρ-E-view-ecin-lift cb' p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐E⟦rin⟧ r≐E⟦ro⟧ rinsn⟶₁ro


1-steplρ-E-view-ecin-lift {E₁ ∷ E} {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBtrap cb')
  (detrap p≐E⟦qin⟧) (detrap q≐E⟦qo⟧) e-view-E₁
  (dctrap p≐E⟦rin⟧) (dctrap r≐E⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (detrap p≐E⟦qin⟧) (detrap q≐E⟦qo⟧)
         p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view) =
  1-steplρ-E-view-ecin-lift cb' p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐E⟦rin⟧ r≐E⟦ro⟧ rinsn⟶₁ro
