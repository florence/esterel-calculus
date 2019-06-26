module Esterel.Variable.Shared where

open import Data.Nat
  using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Function
  using (_∘_)
open import Relation.Nullary
  using (Dec ; yes ; no ; ¬_)
open import Relation.Binary
  using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; trans ; sym)

open import Data.Key

data SharedVar : Set where
  _ₛₕ : ℕ → SharedVar

unwrap : SharedVar → ℕ
unwrap (n ₛₕ) = n

unwrap-inverse : ∀ {s} → (unwrap s) ₛₕ ≡ s
unwrap-inverse {_ ₛₕ} = refl

unwrap-injective : ∀ {s t} → unwrap s ≡ unwrap t → s ≡ t
unwrap-injective s'≡t' = trans (sym unwrap-inverse) (trans (cong _ₛₕ s'≡t') unwrap-inverse)



-- for backward compatibility
unwrap-neq : ∀{k1 : SharedVar} → ∀{k2 : SharedVar} → ¬ k1 ≡ k2 → ¬ (unwrap k1) ≡ (unwrap k2)
unwrap-neq = (_∘ unwrap-injective)

wrap : ℕ → SharedVar
wrap = _ₛₕ

wrap-injective : ∀ {s t} → wrap s ≡ wrap t → s ≡ t
wrap-injective refl = refl


bijective : ∀{x} → unwrap (wrap x) ≡ x
bijective = refl

instance
  Key : BijectiveKey SharedVar
  Key = bijective-key unwrap wrap unwrap-injective wrap-injective bijective

_≟_ : Decidable {A = SharedVar} _≡_
(s ₛₕ) ≟ (t ₛₕ) with s ≟ℕ t
... | yes p = yes (cong _ₛₕ p)
... | no ¬p = no (¬p ∘ cong unwrap)

data Status : Set where
  ready : Status
  new  : Status
  old : Status

_≟ₛₜ_ : Decidable {A = Status} _≡_
ready ≟ₛₜ ready = yes refl
ready ≟ₛₜ new   = no λ()
ready ≟ₛₜ old   = no λ()
new   ≟ₛₜ ready = no λ()
new   ≟ₛₜ new   = yes refl
new   ≟ₛₜ old   = no λ()
old   ≟ₛₜ ready = no λ()
old   ≟ₛₜ new   = no λ()
old   ≟ₛₜ old   = yes refl
