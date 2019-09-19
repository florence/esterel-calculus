module Data.Sublist.Any where

open import Data.Sublist as Sl
  hiding (map)
open import Data.Sublist.Properties

open import Data.List.Any as ListAny
  using ()
  renaming (here to lhere ; there to lthere ; Any to lAny)

open import Data.List as List
  using (List ; [] ; _∷_ ; length ; _++_)
open import Data.Nat as Nat
  using (suc ; _≤_)
open import Level
  using (_⊔_)

open import Data.Product as Prod
  using (∃ ; _,_ ; proj₁)

open import Function
  using (_$_ ; _∘_)

import Relation.Binary.PropositionalEquality as P

import Data.List.Properties as ListP

data Any {a v}{V : Set v}{l : List V}  (P : V → Set a) : ∀{n} → Sublist l n → Set (a ⊔ v) where
  here : ∀{n} → (sl : Sublist l (suc n)) → P (get sl) → Any P sl
  there : ∀{n} {n<l : (suc n) ≤ (length l)} {sl : Sublist l n} → Any P sl → Any P (elem n n<l sl)


lookup' : ∀{a v}{V : Set v}{l : List V}{P : V → Set a}{off}{sl : Sublist l off} → Any P sl → ∃ P
lookup' (here sl x) = (get sl) , x
lookup' (there any) = lookup' any

lookup : ∀{a v}{V : Set v}{l : List V}{P : V → Set a}{off}{sl : Sublist l off} → Any P sl → V
lookup = proj₁ ∘ lookup'



map : ∀{a v1 v2}{V1 : Set v1}{V2 : Set v2}{l : List V1}{P : V1 → Set a}{off}{sl : Sublist l off}
      {Q : V2 → Set a}
      → (f : V1 → V2)
      → (cast : ∀ x → P x → Q (f x))
      → Any P sl 
      → Any Q (Sl.map f sl)
map {Q = Q} f cast (here sl x)
  = here (Sl.map f sl)
    $ P.subst Q (map-get f sl) (cast (get sl) x)
map{l = l} f cast (there any)
   rewrite P.sym $ ListP.length-map f l
   = there (map f cast any) 


convert : ∀{a v}{V : Set v}{l : List V} {P : V → Set a} → lAny P l → Any P (sublist l)
convert {l = l} lany = convert-rec (sublist l) lany
  where
   convert-rec : ∀{a v}{V : Set v}{l1 : List V}{l2 : List V}{P : V → Set a}
                 → (sl : (Sublist (l1 ++ l2) (length l2)))
                 → lAny P l2 → Any P sl
   convert-rec{l1 = l1}{l2@(x ∷ xs)}{P = P'} sl (lhere px)
     = here sl (P.subst P'
                       (P.trans (P.sym $ get-first-is-first-from-head x xs) (P.sym $ ++-get-≡ l1 (length xs) sl (sublist l2)))
                       px)
   convert-rec {l1 = l1} {x ∷ xs} (elem _ _ sl2) (lthere lany)
     rewrite P.sym $ ListP.++-assoc l1 List.[ x ] xs
     = there $ convert-rec sl2 lany
