open import Data.Key

module Data.FiniteMap.Properties
  (Key : Set)
  {{b : BijectiveKey Key}}
 where

open BijectiveKey b

open import Data.FiniteMap(Key) as FMap

open import Data.OrderedListMap.Properties(Key)(inject) as OMap
  using (tail-keys-∈-equal)

open import utility
  using ()
  renaming (_⊆¹_ to _⊆_)


open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)
open import Data.Maybe as Maybe
  using (Maybe ; just ; nothing)
open import Data.List as List
  using (_∷_ ; [])
open import Function
  using (_$_)
open import Data.Product as Prod
  using (proj₁ ; _,_)

open import Data.List.Any as ListAny
  
keys+∈-tail-equal : ∀{Value}
                     → (l : Map Value)
                     → ∀ x
                     → (0 ∷ (List.map proj₁ $ keys+∈ (nothing ∷ l))) ≡ (List.map proj₁ $ keys+∈ (just x ∷ l))
keys+∈-tail-equal = tail-keys-∈-equal _
 

proj₁∈-unchanged : ∀{Value}
                   → (l : Map Value)
                   → keys l ≡ List.map proj₁ (keys+∈ l)
proj₁∈-unchanged = OMap.proj₁∈-unchanged _

lift-in : ∀{Value} (l : Map Value) → ∀ x → ∈Dom x l → ListAny.Any (λ {(k , _) → (inject x) ≡ k}) (keys+∈ l)
lift-in l x ∈ = OMap.lift-in _ l (inject x) ∈

keys⇔-means-equal :
  ∀{Value}(a b : Map Value)
  → (keys a) ⊆ (keys b)
  → (keys b) ⊆ (keys a)
  → ((keys a) ≡ (keys b))
keys⇔-means-equal = OMap.domain⇔-means-equal _ 


module Canonical {Value : Set} where
  open import Data.OrderedListMap.Properties(Key)(inject)(Value)
    renaming (module Canonical to C)
  open C public
    using (Canonical)
  update-canonical : ∀{m1} → Canonical m1 → (k : Key) → (v : Value)
                     → Canonical (update m1 k v)
  update-canonical c k v = C.m-insert-maintains-canonical _ v (inject k) c

  union-canonical : ∀{m1 m2} → Canonical m1 → Canonical m2 → Canonical (union m1 m2)
  union-canonical = C.U-maintains-canonical

  single-canonical : ∀ k v → Canonical [ k ↦ v ]
  single-canonical k v = C.m-insert-empty-is-canonical v (inject k)

  empty-canonical : Canonical []
  empty-canonical = C.empty
