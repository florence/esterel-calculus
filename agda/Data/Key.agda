module Data.Key where

open import Relation.Binary.PropositionalEquality
  using (_≡_)
open import Data.Nat
  using (ℕ)

record BijectiveKey (K : Set) : Set where
  constructor bijective-key
  field
    inject : K → ℕ
    surject : ℕ → K
    inject-injective : ∀ {k1 k2} → inject k1 ≡ inject k2 → k1 ≡ k2
    surject-injective : ∀ {k1 k2} → surject k1 ≡ surject k2 → k1 ≡ k2
    surject-inject : ∀ {k} → inject (surject k) ≡ k

