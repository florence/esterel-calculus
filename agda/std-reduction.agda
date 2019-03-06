module std-reduction where

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; sig ; []env ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)
open import sn-calculus using (all-ready ; [s,δe]-env ; [x,δe]-env ; δ)

open import std-reduction.Base

open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Nullary
  using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_)
open _≡_
open import Data.Nat using (_+_ ; zero ; suc)
open import Data.List
  using ([])

infix 4 _⇁_

data _⇁_ : Term → Term → Set where
  std-par-right : ∀ {p q r E θ} →
    left-most θ E →
    (p' :  halted p) → 
    (q' :  done q) →
    r ≐ E ⟦ (p ∥ q) ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ (value-max (dhalted p') q' (inj₁ p')) ⟧e)
  std-par-left : ∀ {p q r E θ} →
    left-most θ E →
    (p' :  paused p) → 
    (q' :  halted q) →
    r ≐ E ⟦ (p ∥ q) ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ (value-max (dpaused p') (dhalted q') (inj₂ q')) ⟧e)
  std-is-present : ∀ {p q r E θ} →
    left-most θ E →
     ∀ S →
    (S∈ : Env.isSig∈ S θ) →
    Env.sig-stats{S} θ S∈ ≡ Signal.present →
    r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ p ⟧e)
  std-is-absent : ∀ {p q r E θ} →
    left-most θ E →
    ∀ S →
    (S∈ : Env.isSig∈ S θ) →
    Env.sig-stats{S} θ S∈ ≡ Signal.absent →
    r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ q ⟧e)   
  std-emit : ∀{θ E r} →
    left-most θ E →
    ∀ S →
    (S∈ : (Env.isSig∈ S θ)) →
    (¬S≡a : ¬ (Env.sig-stats{S} θ S∈) ≡ Signal.absent) →
    r ≐ E ⟦ emit S ⟧e → 
    (ρ θ · r) ⇁ (ρ (Env.set-sig{S} θ S∈ Signal.present) · E ⟦ nothin ⟧e)
  std-loop-unroll : ∀{θ E r p} →
    left-most θ E →
    r ≐ E ⟦ loop p ⟧e → 
    (ρ θ · r) ⇁ (ρ θ · E ⟦ (loopˢ p p) ⟧e)
  std-seq-done : ∀{θ E r q} →
    left-most θ E →
    r ≐ E ⟦ (nothin >> q) ⟧e →
    ρ θ · r ⇁ (ρ θ · E ⟦ q ⟧e)
  std-seq-exit : ∀{θ E r q n} →
    left-most θ E →
    r ≐ E ⟦ (exit n >> q) ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ (exit n) ⟧e)
  std-loopˢ-exit : ∀{θ E r q n} →
    left-most θ E →
    r ≐ E ⟦ (loopˢ (exit n) q) ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ (exit n) ⟧e)
  std-suspend-done : ∀{θ E r p S} →
    left-most θ E →
    (p' : halted p) →
    r ≐ E ⟦ (suspend p S) ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ p ⟧e)
  std-trap-done : ∀{θ E r p} →
    left-most θ E →
    (p' : halted p) →
    r ≐ E ⟦ (trap p) ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ (↓ p') ⟧e)
  std-raise-signal : ∀{θ E r p S} →
    left-most θ E →
    r ≐ E ⟦ (signl S p) ⟧e →
     (ρ θ · r) ⇁
     (ρ θ ·
         E ⟦ (ρ (Θ SigMap.[ S ↦ Signal.unknown ] ShrMap.empty VarMap.empty) ·
               p) ⟧e)
  std-raise-shared : ∀{θ r s e p E} →
    left-most θ E →
    (e' : all-ready e θ) →
    r ≐ E ⟦ shared s ≔ e in: p ⟧e →
    (ρ θ · r) ⇁
    (ρ θ ·
      E ⟦ (ρ [s,δe]-env s (δ e') · p) ⟧e)
  std-set-shared-value-old : ∀{θ r s e E} →
    left-most θ E →
    (e' : all-ready e θ) →
    (s∈ : (Env.isShr∈ s θ)) →
    Env.shr-stats{s} θ s∈ ≡ SharedVar.old →
    r ≐ E ⟦ s ⇐ e ⟧e →
    (ρ θ · r) ⇁
    (ρ (Env.set-shr{s} θ s∈ (SharedVar.new) (δ e')) ·
      E ⟦ nothin ⟧e)

  std-set-shared-value-new : ∀{θ r s e E} →
    left-most θ E →
    (e' : all-ready e θ) →
    (s∈ : (Env.isShr∈ s θ)) →
    Env.shr-stats{s} θ s∈ ≡ SharedVar.new →
    r ≐ E ⟦ s ⇐ e ⟧e →
    (ρ θ · r) ⇁
    (ρ (Env.set-shr{s} θ s∈ (SharedVar.new) (Env.shr-vals{s} θ s∈ + δ e')) ·
      E ⟦ nothin ⟧e)

  -- unshared state
  std-raise-var : ∀{θ r x p e E} →
    left-most θ E →
    (e' : all-ready e θ) →
    r ≐ E ⟦ var x ≔ e in: p ⟧e →
    (ρ θ · r) ⇁
    (ρ θ ·
      E ⟦ (ρ [x,δe]-env x (δ e') · p) ⟧e)

  std-set-var : ∀{θ r x e E} →
    left-most θ E →
    (x∈ : (Env.isVar∈ x θ)) →
    (e' : all-ready e θ) →
    r ≐ E ⟦ x ≔ e ⟧e →
    (ρ θ · r) ⇁
    (ρ (Env.set-var{x} θ x∈ (δ e')) ·
      E ⟦ nothin ⟧e)

  -- if
  std-if-false : ∀{θ r p q x E} →
    left-most θ E →
    (x∈ : (Env.isVar∈ x θ)) →
    Env.var-vals{x} θ x∈ ≡ zero →
    r ≐ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ q ⟧e)

  std-if-true : ∀{θ r p q x E n} →
    left-most θ E →
    (x∈ : (Env.isVar∈ x θ)) →
    Env.var-vals{x} θ x∈ ≡ suc n →
    r ≐ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e →
    (ρ θ · r) ⇁ (ρ θ · E ⟦ p ⟧e)

  std-merge : ∀{θ₁ θ₂ r p E} →
    left-most θ₁ E →
    r ≐ E ⟦ ρ θ₂ · p ⟧e →
    (ρ θ₁ · r) ⇁ (ρ (θ₁ ← θ₂) · E ⟦ p ⟧e)

  std-absent : ∀{θ p} →
    blocked-or-done θ p →
    ¬ (can-set-absent θ p ≡ []) →
    ρ θ · p ⇁ ρ (set-all-absent θ (can-set-absent θ p)) · p

  std-readyness : ∀{θ p} →
    blocked-or-done θ p →
    (can-set-absent θ p ≡ []) →
    ¬ (can-set-ready θ p ≡ []) →
    ρ θ · p ⇁ ρ (set-all-ready θ (can-set-ready θ p)) · p

