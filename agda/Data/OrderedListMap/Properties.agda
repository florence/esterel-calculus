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
  using (_≡_ ; refl ; cong ; sym ; inspect ; [_] ; module ≡-Reasoning) 
open import Data.Maybe as Maybe
  using (Maybe ; just ; nothing)

open import Data.List.Properties as ListP
  using (map-compose)

open ≡-Reasoning


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

suc-isprodsucin : ∀ l → Dom'+∈-help (List.map suc l) ≡ List.map (Prod.map suc sucin) (Dom'+∈-help l)
suc-isprodsucin [] = refl
suc-isprodsucin (x ∷ l)
   rewrite suc-isprodsucin l
  = cong ((suc x , here refl) ∷_)
         $ (begin
              List.map (Prod.map₂ there) (List.map (Prod.map suc sucin) (Dom'+∈-help l))
              ≡⟨ sym $ ListP.map-compose (Dom'+∈-help l) ⟩
              List.map ((Prod.map₂ there) ∘ (Prod.map suc sucin)) (Dom'+∈-help l)
              ≡⟨ ListP.map-cong (λ { (fst , snd) → refl}) (Dom'+∈-help l) ⟩
              List.map ((Prod.map suc sucin) ∘ (Prod.map₂ there)) (Dom'+∈-help l)
              ≡⟨ ListP.map-compose (Dom'+∈-help l) ⟩
              List.map (Prod.map suc sucin) (List.map (Prod.map₂ there) (Dom'+∈-help l)) ∎)

module Canonical where
  data Canonical : (l : LMap) → Set where
    empty : Canonical []
    just-empty : ∀ x → Canonical (just x ∷ [])
    cons-j : ∀{l} x → Canonical l → Canonical ((just x) ∷ l)
    cons-n : ∀{x l} → (Canonical (x ∷ l)) → Canonical (nothing ∷ x ∷ l)

  canonical-insert-just : ∀{x l} y → Canonical (x ∷ l) →  Canonical (just y ∷ l)
  canonical-insert-just y (just-empty x) = just-empty y
  canonical-insert-just y (cons-j x can) = cons-j y can
  canonical-insert-just y (cons-n can) = cons-j y can

  m-insert-empty-is-canonical : ∀ x n → Canonical (m-insert (just x) n [])
  m-insert-empty-is-canonical x zero = just-empty x
  m-insert-empty-is-canonical x (suc zero) = cons-n (just-empty x)
  m-insert-empty-is-canonical x (suc (suc n)) = cons-n (m-insert-empty-is-canonical x (suc n))

  m-insert-maintains-canonical : ∀ l x n → Canonical l → Canonical (m-insert (just x) n l)
  m-insert-maintains-canonical [] x zero can = just-empty x
  m-insert-maintains-canonical (x₁ ∷ l) x zero can = canonical-insert-just x can
  m-insert-maintains-canonical [] x (suc n) can = m-insert-empty-is-canonical x (suc n)
  m-insert-maintains-canonical (just x₁ ∷ .[]) x (suc zero) (just-empty .x₁) = cons-j x₁ (just-empty x)
  m-insert-maintains-canonical (just x₁ ∷ l) x (suc zero) (cons-j .x₁ can)
    = cons-j x₁ (m-insert-maintains-canonical l x zero can )
  m-insert-maintains-canonical (just x₁ ∷ .[]) x (suc (suc n)) (just-empty .x₁)
    = cons-j x₁ (m-insert-empty-is-canonical x (suc n))
  m-insert-maintains-canonical (just x₁ ∷ l) x (suc (suc n)) (cons-j .x₁ can)
   = cons-j x₁ (m-insert-maintains-canonical l x (suc n) can)
  m-insert-maintains-canonical (nothing ∷ a ∷ b) x (suc zero) (cons-n can)
    = cons-n (m-insert-maintains-canonical (a ∷ b) x zero can)
  m-insert-maintains-canonical (nothing ∷ a ∷ b) x (suc (suc n)) (cons-n can)
    = cons-n (m-insert-maintains-canonical (a ∷ b) x (suc n) can)

  normalize : LMap → ∃ Canonical
  normalize [] = [] , empty
  normalize (x ∷ l)
    with normalize l
  normalize (just x ∷ l)
          | l' , can
   = _ , cons-j x can
  normalize (nothing ∷ l) | [] , can
    = _ , can
  normalize (nothing ∷ l)
    | x ∷ l' , can = _ , cons-n can
