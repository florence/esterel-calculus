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
  std-par-right : ∀ {p q r E θ A} →
    (lmθE : left-most θ E)  →
    (haltedp :  halted p) → 
    (doneq :  done q) →
    (r=E⟦p∥q⟧ : r ≐ E ⟦ (p ∥ q) ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ (value-max (dhalted haltedp) doneq (inj₁ haltedp)) ⟧e)
  std-par-left : ∀ {p q r E θ A} →
    (lmθE : left-most θ E)  →
    (pausedp :  paused p) → 
    (haltedq :  halted q) →
    (r=E⟦p∥q⟧ : r ≐ E ⟦ (p ∥ q) ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ (value-max (dpaused pausedp) (dhalted haltedq) (inj₂ haltedq)) ⟧e)
  std-is-present : ∀ {p q r E θ A} →
    (lmθE : left-most θ E)  →
     ∀ S →
    (S∈ : Env.isSig∈ S θ) →
    (θ⦅S⦆=present : Env.sig-stats{S} θ S∈ ≡ Signal.present) →
    (r=E⟦presentSpq⟧ : r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ p ⟧e)
  std-is-absent : ∀ {p q r E θ A} →
    (lmθE : left-most θ E)  →
    ∀ S →
    (S∈ : Env.isSig∈ S θ) →
    (θ⦅S⦆=absent : Env.sig-stats{S} θ S∈ ≡ Signal.absent) →
    (r=E⟦presentSpq⟧ : r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ q ⟧e)   
  std-emit : ∀{θ E r} →
    (lmθE : left-most θ E)  →
    ∀ S →
    (S∈ : (Env.isSig∈ S θ)) →
    (¬S≡a : ¬ (Env.sig-stats{S} θ S∈) ≡ Signal.absent) →
    (r=E⟦emitS⟧ : r ≐ E ⟦ emit S ⟧e) → 
    (ρ⟨ θ , GO ⟩· r) ⇁ (ρ⟨ (Env.set-sig{S} θ S∈ Signal.present) , GO ⟩· E ⟦ nothin ⟧e)
  std-loop-unroll : ∀{θ E r p A} →
    (lmθE : left-most θ E)  →
    (r=E⟦loopp⟧ : r ≐ E ⟦ loop p ⟧e) → 
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ (loopˢ p p) ⟧e)
  std-seq-done : ∀{θ E r q A} →
    (lmθE : left-most θ E)  →
    (r=E⟦nothing>>q⟧ : r ≐ E ⟦ (nothin >> q) ⟧e) →
    ρ⟨ θ , A ⟩· r ⇁ (ρ⟨ θ , A ⟩· E ⟦ q ⟧e)
  std-seq-exit : ∀{θ E r q n A} →
    (lmθE : left-most θ E)  →
    (r=E⟦exitn>>q⟧ : r ≐ E ⟦ (exit n >> q) ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ (exit n) ⟧e)
  std-loopˢ-exit : ∀{θ E r q n A} →
    (lmθE : left-most θ E)  →
    (r=E⟦loopˢexitnq⟧ : r ≐ E ⟦ (loopˢ (exit n) q) ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ (exit n) ⟧e)
  std-suspend-done : ∀{θ E r p S A} →
    (lmθE : left-most θ E)  →
    (haltedp : halted p) →
    (r=E⟦suspendpS⟧ : r ≐ E ⟦ (suspend p S) ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ p ⟧e)
  std-trap-done : ∀{θ E r p A} →
    (lmθE : left-most θ E)  →
    (haltedp : halted p) →
    (r=E⟦trapp⟧ : r ≐ E ⟦ (trap p) ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ (↓ haltedp) ⟧e)
  std-raise-signal : ∀{θ E r p S A} →
    (lmθE : left-most θ E)  →
    (r=E⟦signalsp⟧ : r ≐ E ⟦ (signl S p) ⟧e) →
     (ρ⟨ θ , A ⟩· r) ⇁
     (ρ⟨ θ , A ⟩·
         E ⟦ (ρ⟨ (Θ SigMap.[ S ↦ Signal.unknown ] ShrMap.empty VarMap.empty) , WAIT ⟩·
               p) ⟧e)
  std-raise-shared : ∀{θ r s e p E A} →
    (lmθE : left-most θ E)  →
    (e' : all-ready e θ) →
    (r=E⟦shareds=ep⟧ : r ≐ E ⟦ shared s ≔ e in: p ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁
    (ρ⟨ θ , A ⟩·
      E ⟦ (ρ⟨ [s,δe]-env s (δ e') , WAIT ⟩· p) ⟧e)
  std-set-shared-value-old : ∀{θ r s e E} →
    (lmθE : left-most θ E)  →
    (e' : all-ready e θ) →
    (s∈ : (Env.isShr∈ s θ)) →
    (θ⦅s⦆=old : Env.shr-stats{s} θ s∈ ≡ SharedVar.old) →
    (r=E⟦s<=e⟧ : r ≐ E ⟦ s ⇐ e ⟧e) →
    (ρ⟨ θ , GO ⟩· r) ⇁
    (ρ⟨ (Env.set-shr{s} θ s∈ (SharedVar.new) (δ e')) , GO ⟩·
      E ⟦ nothin ⟧e)

  std-set-shared-value-new : ∀{θ r s e E} →
    (lmθE : left-most θ E)  →
    (e' : all-ready e θ) →
    (s∈ : (Env.isShr∈ s θ)) →
    (θ⦅s⦆=new : Env.shr-stats{s} θ s∈ ≡ SharedVar.new) →
    (r=E⟦s<=e⟧ : r ≐ E ⟦ s ⇐ e ⟧e) →
    (ρ⟨ θ , GO ⟩· r) ⇁
    (ρ⟨ (Env.set-shr{s} θ s∈ (SharedVar.new) (Env.shr-vals{s} θ s∈ + δ e')) , GO ⟩·
      E ⟦ nothin ⟧e)

  -- unshared state
  std-raise-var : ∀{θ r x p e E A} →
    (lmθE : left-most θ E)  →
    (e' : all-ready e θ) →
   (r=E⟦varx=ep⟧ : r ≐ E ⟦ var x ≔ e in: p ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁
    (ρ⟨ θ , A ⟩·
      E ⟦ (ρ⟨ [x,δe]-env x (δ e') , WAIT ⟩· p) ⟧e)

  std-set-var : ∀{θ r x e E A} →
    (lmθE : left-most θ E)  →
    (x∈ : (Env.isVar∈ x θ)) →
    (e' : all-ready e θ) →
    (r=E⟦x=e⟧ : r ≐ E ⟦ x ≔ e ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁
    (ρ⟨ (Env.set-var{x} θ x∈ (δ e')) , A ⟩·
      E ⟦ nothin ⟧e)

  -- if
  std-if-false : ∀{θ r p q x E A} →
    (lmθE : left-most θ E)  →
    (x∈ : (Env.isVar∈ x θ)) →
    (θ⦅x⦆=0 : Env.var-vals{x} θ x∈ ≡ zero) →
    (r=E⟦ifxpq⟧ : r ≐ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ q ⟧e)

  std-if-true : ∀{θ r p q x E n A} →
    (lmθE : left-most θ E)  →
    (x∈ : (Env.isVar∈ x θ)) →
    (θ⦅x⦆≠0 : Env.var-vals{x} θ x∈ ≡ suc n) →
    (r=E⟦ifxpq⟧ : r ≐ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) →
    (ρ⟨ θ , A ⟩· r) ⇁ (ρ⟨ θ , A ⟩· E ⟦ p ⟧e)

  std-merge : ∀{θ₁ θ₂ r p E A₁ A₂} →
    (lmθ₁E : left-most θ₁ E) →
    (r=E⟦ρ⟨θ₂,A₂⟩·p⟧ : r ≐ E ⟦ ρ⟨ θ₂ , A₂ ⟩· p ⟧e) →
    (ρ⟨ θ₁ , A₁ ⟩· r) ⇁ (ρ⟨ (θ₁ ← θ₂) , (A-max A₁ A₂) ⟩· E ⟦ p ⟧e)

  std-absent : ∀{θ p A} →
    (BVDθAp : blocked-or-done θ A p) →
    (can-set-something-absent : ¬ (can-set-absent θ p ≡ [])) →
    ρ⟨ θ , A ⟩· p ⇁ ρ⟨ (set-all-absent θ (can-set-absent θ p)) , A ⟩· p

  std-readyness : ∀{θ p A} →
    (BVDθAp : blocked-or-done θ A p) →
    (can-set-nothing-absent : (can-set-absent θ p ≡ [])) →
    (can-set-something-ready : ¬ (can-set-ready θ p ≡ [])) →
    ρ⟨ θ , A ⟩· p ⇁ ρ⟨ (set-all-ready θ (can-set-ready θ p)) , A ⟩· p

