module Esterel.Variable.Sequential where

open import Data.Key

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


data SeqVar : Set where
  _ᵥ : ℕ → SeqVar

unwrap : SeqVar → ℕ
unwrap (n ᵥ) = n

unwrap-inverse : ∀ {s} → (unwrap s) ᵥ ≡ s
unwrap-inverse {_ ᵥ} = refl

unwrap-injective : ∀ {s t} → unwrap s ≡ unwrap t → s ≡ t
unwrap-injective s'≡t' = trans (sym unwrap-inverse) (trans (cong _ᵥ s'≡t') unwrap-inverse)

-- for backward compatibility
unwrap-neq : ∀{k1 : SeqVar} → ∀{k2 : SeqVar} → ¬ k1 ≡ k2 → ¬ (unwrap k1) ≡ (unwrap k2)
unwrap-neq = (_∘ unwrap-injective)

wrap : ℕ → SeqVar
wrap = _ᵥ

wrap-injective : ∀ {s t} → wrap s ≡ wrap t → s ≡ t
wrap-injective refl = refl


bijective : ∀{x} → unwrap (wrap x) ≡ x
bijective = refl

instance
  Key : BijectiveKey SeqVar
  Key = bijective-key unwrap wrap unwrap-injective wrap-injective bijective




_≟_ : Decidable {A = SeqVar} _≡_
(s ᵥ) ≟ (t ᵥ) with s ≟ℕ t
... | yes p = yes (cong _ᵥ p)
... | no ¬p = no (¬p ∘ cong unwrap)
