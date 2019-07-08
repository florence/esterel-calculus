open import Data.Key

module Data.FiniteMap.Properties
  (Key : Set)
  {{b : BijectiveKey Key}}
 where

open BijectiveKey b

open import Data.FiniteMap(Key) as FMap

open import Data.OrderedListMap.Properties(Key)(inject) as OMap
  using (tail-keys-∈-equal)


open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)
open import Data.Maybe as Maybe
  using (Maybe ; just ; nothing)
open import Data.List as List
  using (_∷_ ; [])
open import Function
  using (_$_)
open import Data.Product as Prod
  using (proj₁)
  

keys+∈-tail-equal : ∀{Value}
                     → (l : Map Value)
                     → ∀ x
                     → (0 ∷ (List.map proj₁ $ keys+∈ (nothing ∷ l))) ≡ (List.map proj₁ $ keys+∈ (just x ∷ l))
keys+∈-tail-equal = tail-keys-∈-equal _
 

proj₁∈-unchanged : ∀{Value}
                   → (l : Map Value)
                   → keys l ≡ List.map proj₁ (keys+∈ l)
proj₁∈-unchanged = OMap.proj₁∈-unchanged _
