module Esterel.Variable.Signal where

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

data Signal : Set where
  _ₛ : (S : ℕ) → Signal

unwrap : Signal → ℕ
unwrap (n ₛ) = n

unwrap-inverse : ∀ {s} → (unwrap s) ₛ ≡ s
unwrap-inverse {_ ₛ} = refl

unwrap-injective : ∀ {s t} → unwrap s ≡ unwrap t → s ≡ t
unwrap-injective s'≡t' = trans (sym unwrap-inverse) (trans (cong _ₛ s'≡t') unwrap-inverse)

wrap : ℕ → Signal
wrap = _ₛ

wrap-injective : ∀ {s t} → wrap s ≡ wrap t → s ≡ t
wrap-injective refl = refl

bijective : ∀{x} → unwrap (wrap x) ≡ x
bijective = refl

instance
  Key : BijectiveKey Signal
  Key = bijective-key unwrap wrap unwrap-injective wrap-injective bijective


-- for backward compatibility
unwrap-neq : ∀{k1 : Signal} → ∀{k2 : Signal} → ¬ k1 ≡ k2 → ¬ (unwrap k1) ≡ (unwrap k2)
unwrap-neq = (_∘ unwrap-injective)

_≟_ : Decidable {A = Signal} _≡_
(s ₛ) ≟ (t ₛ) with s ≟ℕ t
... | yes p = yes (cong _ₛ p)
... | no ¬p = no (¬p ∘ cong unwrap)

data Status : Set where
  present : Status
  absent  : Status
  unknown : Status

_≟ₛₜ_ : Decidable {A = Status} _≡_
present ≟ₛₜ present = yes refl
present ≟ₛₜ absent  = no λ()
present ≟ₛₜ unknown = no λ()
absent  ≟ₛₜ present = no λ()
absent  ≟ₛₜ absent  = yes refl
absent  ≟ₛₜ unknown = no λ()
unknown ≟ₛₜ present = no λ()
unknown ≟ₛₜ absent  = no λ()
unknown ≟ₛₜ unknown = yes refl
