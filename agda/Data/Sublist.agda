module Data.Sublist where

open import Data.Nat as Nat
  using (ℕ ; pred ; zero ; suc ; _≤_ ; _<_ ; _∸_)
open _≤_
open import Data.Nat.Properties
  using (≤-refl ; ≤⇒pred≤ ; _<?_ ; +-mono-≤ ; ≤-stepsˡ)
open import Data.Fin
  using (Fin ; fromℕ≤)
  renaming (zero to fzero ; suc to fsuc)
open import Data.List as List
  using (List ; length ; _∷_ ; [])
open import Data.List.Properties as ListProp
open import Function
  using (_$_ ; _∘_ ; id ; const)
open import Relation.Nullary
  using (yes ; no)
open import Data.Empty
  using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≢_ ; _≡_ ; sym )

data Sublist {a}{A : Set a} (l : List A) : ℕ → Set where
     empty : Sublist l 0
     elem  : (n : ℕ) → (n<l : (suc n) ≤ (length l)) → Sublist l n → Sublist l (suc n)



build-sublist : ∀{a}{A : Set a}
                → {l : List A}
                → (n : ℕ)
                → (n≤l : n ≤ (length l))
                → Sublist l n
build-sublist {l = []} zero z≤s = empty
build-sublist {l = []} (suc n) ()
build-sublist {l = l@(_ ∷ _)} zero n≤l = empty
build-sublist {l = l@(_ ∷ _)} (suc n) n≤l = elem n n≤l $ build-sublist n $ ≤⇒pred≤ n≤l

--elem (suc n) n≤l (build-sublist n {!!})

sublist : ∀{a}{A : Set a} → (l : List A) → Sublist l (length l)
sublist l = build-sublist (length l) ≤-refl

get-sub-lt : ∀ n l → n < l → (l ∸ (suc n)) < l
get-sub-lt zero .(suc _) (s≤s n<l) = ≤-refl
get-sub-lt (suc n) (suc l) (s≤s n<l) = ≤-stepsˡ 1 $ get-sub-lt n l n<l
 
get : ∀{a A l n} → Sublist{a}{A} l (suc n) → A
get {l = l} {n} (elem n n<l sl)
  = List.lookup l $ fromℕ≤ $ get-sub-lt n (length l) n<l
   
map : ∀{a b}{A : Set a}{B : Set b}{l : List A}{off} → (f : A → B) → Sublist l off → Sublist (List.map f l) off
map f empty = empty
map {l = l} f (elem n n<l sl)
   rewrite sym $ ListProp.length-map f l
   = elem n n<l (map f sl)

visit : ∀{i a o n}{I : Set i}{A : Set a}{O : A → Set o}{l : List I}
        → (f : I → (af : A) → ((ar : A) → O ar) → O af)
        → ((ai : A) → O ai)
        → (a : A)
        → Sublist l n
        → O a
visit f g a empty = g a
visit f g a l@(elem n n<l sl) = f (get l) a (λ a → visit f g a sl)

-- a variant of visit that work more like the well founded recursion forms
visit-rec : ∀{i a n}{I : Set i}{A : Set a}{l : List I} → (f : I → A → (A → A) → A) → A → Sublist l n → A
visit-rec{A = A} f a l = visit f id a l


get-n : ∀{a}{A : Set a}{l : List A}{n} → Sublist l n → ℕ
get-n {n = n} _ = n

module Tests where
  open import Relation.Binary.PropositionalEquality
    using (refl ; _≡_)
  l = (0 ∷ 1 ∷ 2 ∷ [])
  sl3 = (sublist l)
  sl2 : (Sublist l 2)
  sl2 with sl3
  sl2 | elem .2 n<l x = x
  sl1 : Sublist l 1
  sl1 with sl2
  sl1 | elem .1 n<l x = x
  t3 : (get sl3) ≡ 0
  t3 = refl
  t2 : (get sl2) ≡ 1
  t2 = refl
  t1 : (get sl1) ≡ 2
  t1 = refl


  
