open import Data.Nat as Nat
  using (ℕ ; _+_ ; zero ; suc) 

module Data.OrderedListMap.Properties
  (Key : Set)
  (inject : Key → ℕ)
  (Value : Set)
  where

open import Data.OrderedListMap(Key)(inject)(Value)
open import utility

open import Data.List as List
  using (_∷_ ; [] ; List)
open import Data.List.Any as ListAny
  using (Any ; any ; here ; there)
open import Function
  using (_∘_ ; _$_ ; id )
open import Data.Product as Prod
  using (Σ ; Σ-syntax ; _,_ ; proj₁ ; proj₂ ; _×_ ; _,′_ ; ∃-syntax ; ∃)
open import Relation.Binary.PropositionalEquality as Eql
  using (_≡_ ; refl ; cong ; sym) 
open import Data.Maybe as Maybe
  using (Maybe ; just ; nothing)

open import Data.List.Properties as ListP
  using (map-compose)


ProdMap+proj₁≡l+proj₁ : ∀{A : Set}{B : Set}{C : A → Set}{D : B → Set}
                      → (l : A → B) → (r : ∀ {x} → C x → D (l x))
                      → (lst : List (Σ A C))
                      → (List.map proj₁ (List.map (Prod.map{P = C}{Q = D} l r) lst))
                        ≡
                        (List.map l (List.map proj₁ lst))
ProdMap+proj₁≡l+proj₁ l r [] = refl
ProdMap+proj₁≡l+proj₁{D = D} l r (x ∷ lst)
  =  cong (l (proj₁ x) ∷_) $ ProdMap+proj₁≡l+proj₁{D = D} l r lst 
  


tail-keys-∈-equal : ∀ mp x → (0 ∷ (List.map proj₁ (Dom'+∈ (nothing ∷ mp)))) ≡ (List.map proj₁ (Dom'+∈ (just x ∷ mp)))
tail-keys-∈-equal [] x = refl
tail-keys-∈-equal (x₁ ∷ mp) x
  rewrite ProdMap+proj₁≡l+proj₁ id (there{x = 0}) $ Dom'+∈-help (List.map suc (Dom' (x₁ ∷ mp)))
         | tail-keys-∈-equal mp x
         | ListP.map-id $ List.map proj₁ (Dom'+∈-help (List.map suc (Dom' (x₁ ∷ mp))))
        = refl

Dom'-help-suc-swap : ∀  l
                     → List.map proj₁ (Dom'+∈-help (List.map suc l))
                       ≡
                       (List.map suc $ List.map proj₁ $ Dom'+∈-help l)
Dom'-help-suc-swap [] = refl
Dom'-help-suc-swap (x ∷ l)
  rewrite ProdMap+proj₁≡l+proj₁ id (there{x = suc x}) (Dom'+∈-help (List.map suc l))
        | ProdMap+proj₁≡l+proj₁ id (there{x = x}) (Dom'+∈-help l)
        | ListP.map-id $ List.map proj₁ (Dom'+∈-help (List.map suc l)) 
        | ListP.map-id $ List.map proj₁ (Dom'+∈-help l) 
  = cong (suc x ∷_) $ Dom'-help-suc-swap l


proj₁∈-unchanged : ∀ sigs → Dom' sigs ≡ (List.map proj₁ $ Dom'+∈ sigs)
proj₁∈-unchanged [] = refl
proj₁∈-unchanged (nothing ∷ sigs)
  rewrite Dom'-help-suc-swap $ (Dom' sigs)
   = cong (List.map suc) $ proj₁∈-unchanged sigs
proj₁∈-unchanged (just x ∷ sigs)
  rewrite ProdMap+proj₁≡l+proj₁ id (there{x = 0}) $ Dom'+∈-help (List.map suc (Dom' sigs))
         | ListP.map-id $ List.map proj₁ (Dom'+∈-help (List.map suc (Dom' sigs)))
         | Dom'-help-suc-swap $ (Dom' sigs)
  = cong ((0 ∷_) ∘ List.map suc) $ proj₁∈-unchanged sigs

