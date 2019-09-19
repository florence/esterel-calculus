module Data.Sublist.Forall where

open import utility.HeterogeneousEquality

open import Data.Sublist
open import Data.Sublist.Any
open import Data.Sublist.Properties as SLP
  using ()

open import Data.Nat as Nat
  using (suc ; ℕ)
open import Data.List as List
  using (List ; length ; _∷_ ; [] )
import Data.List.Any as lAny
open import Level
  using (_⊔_)
open import Relation.Unary
  using (Pred ; Irrelevant)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_)
open import Relation.Binary.HeterogeneousEquality as H
  using (_≅_)
open import Data.Fin as Fin
  using (Fin ; fromℕ≤)
  renaming (zero to fzero ; suc to fsuc)
open import Data.Product as Prod
  using (proj₂)

open import Function
  using (_$_ ; _∋_)


data ∀ˢ {a i}{A : Set a}{l : List A} (P : Pred A i) : ∀{off} → Sublist l off → Set (a ⊔ i) where
  ∀empty : ∀ˢ P empty
  ∀cons  : ∀{off} → (sl : Sublist l (suc off)) → P (get sl) → ∀ˢ P (next sl)
           → ∀ˢ P sl

∀-off : ∀ {a i}{A : Set a}{l : List A} {P : Pred A i}{off} {sl :  Sublist l off}
        → ∀ˢ P sl → ℕ
∀-off {off = off} _ = off
       

uncurry-∀ˢ : ∀ {a i}{A : Set a}{l : List A} {P : Pred A i} {off} → (sl : Sublist l off)
           → (∀ v → lAny.Any (_≡_ v) l → P v) → ∀ˢ P sl
uncurry-∀ˢ empty f = ∀empty
uncurry-∀ˢ l@(elem n n<l sl) f
  = ∀cons l (f (get l) (get-in l)) (uncurry-∀ˢ sl f) 
  where
    lookup-in : ∀{a}{A : Set a}
                 → (l : List A)
                 → (f : Fin (length l))
                 → lAny.Any (_≡_ $ List.lookup l f) l
    lookup-in [] ()
    lookup-in (x ∷ l) fzero = lAny.here _≡_.refl
    lookup-in (x ∷ l) (fsuc f) = lAny.there (lookup-in l f)
    get-in : ∀{a}{A : Set a}{off}{l : List A}
             → (sl : Sublist l (suc off))
             → lAny.Any (_≡_ (get sl)) l
    get-in {l = l} (elem n n<l sl) = lookup-in l $ fromℕ≤ $ get-sub-lt n (length l) n<l

$ᵃ : ∀{a1 a2 v}{V : Set v}{l : List V}{off}{sl : Sublist l off}
      {P1 : V → Set a1}{P2 : V → Set a2}
      → (a : Any P1 sl) → ∀ˢ P2 sl
      → P2 (lookup a)
$ᵃ (here sl x) (∀cons .sl x₁ all) = x₁
$ᵃ (there any) (∀cons _ x all) = $ᵃ any all

curry-∀ˢ : ∀ {a i}{A : Set a}{l : List A} {P : Pred A i} 
           → ∀ˢ P (sublist l) → (∀ v → lAny.Any (_≡_ v) l → P v)
curry-∀ˢ all v v∈
  rewrite proj₂ $ lookup' (convert v∈)
  = $ᵃ (convert v∈) all


∀ˢ-irrelevant : ∀ {a i}{A : Set a}{l : List A}{P : Pred A i}{off}
                → Irrelevant P
                → Irrelevant (∀ˢ{l = l} P {off = off})
∀ˢ-irrelevant irp ∀empty ∀empty
  = _≡_.refl
∀ˢ-irrelevant irp (∀cons sl x sl1) (∀cons .sl x₁ sl2)
  rewrite ∀ˢ-irrelevant  irp sl1 sl2
        | irp x x₁
  = _≡_.refl


∀ˢ-irrelevant-het : ∀ {a i}{A : Set a}{B : Set a}{l1 : List A}{l2 : List B}{P : Pred A i}{off1 off2}
                → Irrelevant P
                → (sl1 : Sublist l1 off1)
                → (sl2 : Sublist l2 off2)
                → (trfl : A ≡ B)
                → l1 ≅ l2
                → off1 ≡ off2
                → (a1 : ∀ˢ P sl1)
                → (a2 : ∀ˢ (P.subst (λ T → Pred T i) trfl P) sl2)
                → (a1 ≅ a2)
∀ˢ-irrelevant-het {A = A} {l1} {l2} {P} irp .empty .empty P.refl H.refl P.refl ∀empty ∀empty = H.refl
∀ˢ-irrelevant-het {A = A} {l1} {l2} {P} irp sl1 sl2 P.refl H.refl P.refl (∀cons .sl1 x a1) (∀cons .sl2 x₁ a2)
  with (SLP.equal-list-equal-sublist-het sl1 sl2 H.refl H.refl P.refl)
∀ˢ-irrelevant-het {A = A} {_} {l1} {l1} {P} irp .(elem n n<l sl2) l@(elem n n<l sl2) P.refl H.refl P.refl (∀cons .(elem n n<l sl2) x a1) (∀cons .(elem n n<l sl2) x₁ a2)
               | H.refl
               rewrite irp x₁ x
   = H.cong (∀cons l x) (∀ˢ-irrelevant-het {P = P} irp sl2 sl2 P.refl H.refl P.refl a1 a2)
