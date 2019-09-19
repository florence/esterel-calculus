module Data.Sublist where

open import Data.Nat as Nat
  using (ℕ ; pred ; zero ; suc ; _≤_ ; _<_ ; _∸_ ; _+_)
open _≤_
open import Data.Nat.Properties as NatP
  using (≤-refl ; ≤⇒pred≤ ; _<?_ ; +-mono-≤ ; ≤-stepsˡ)
open import Data.Fin
  using (Fin ; fromℕ≤)
  renaming (zero to fzero ; suc to fsuc)
open import Data.List as List
  using (List ; length ; _∷_ ; [] ; [_] ; _++_)
open import Data.List.Properties as ListProp
open import Function
  using (_$_ ; _∘_ ; id ; const ; _∋_)
open import Relation.Nullary
  using (yes ; no)
open import Data.Empty
  using (⊥-elim)
open import Relation.Binary.PropositionalEquality as P
  using (_≢_ ; _≡_ ; sym )
open import Data.List.Any as lAny
  using (Any)
open import Data.Product as Prod
  using (_,_ ; Σ ; _×_ ; proj₁ ; proj₂ ; ∃-syntax)

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

get∈ : ∀{a A l n} → (sl : Sublist{a}{A} l (suc n)) → (Any (_≡_ (get sl)) l)
get∈ {A = A} {l} (elem n n<l sl)
 = lookup∈ l $ fromℕ≤ $ get-sub-lt n (length l) n<l 
 where
  lookup∈ : ∀ (l : List A) → (n : Fin (length l)) → Any (_≡_ (List.lookup l n)) l
  lookup∈ [] ()
  lookup∈ (x ∷ l) fzero = lAny.here P.refl
  lookup∈ (x ∷ l) (fsuc n) = lAny.there (lookup∈ l n)

next : ∀{a A l n} → Sublist{a}{A} l (suc n) → Sublist{a}{A} l n
next (elem n n<l sl) = sl
   
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

Rec : ∀{i  a}{I : Set i}→ (l : List I) → (n : ℕ) → (A : ∀{n} → Sublist l n → Set a) → Set a
Rec l n A = ∀{m} → (suc m) ≡ n → (sl : Sublist l m) → (A sl)

visit-rec : ∀{i a n}{I : Set i}{l : List I}{A : ∀{n} → Sublist l n → Set a}
            → (f : ∀{n} → (sl : Sublist l n) → (Rec l n A) → A sl)
            → (sl : Sublist l n) → A sl
visit-rec f sl
  = f sl (λ { _≡_.refl l → visit-rec f l})


get-n : ∀{a}{A : Set a}{l : List A}{n} → Sublist l n → ℕ
get-n {n = n} _ = n

split :  ∀{a}{A : Set a}{l : List A}{n} → Sublist l n
         → Σ (List A × List A) λ {(l1 , l2) → l1 ++ l2 ≡ l × (length l2) ≡ n}
split {l = l}{off} empty = (l , []) , ListProp.++-identityʳ l , P.refl 
split {A = A} {l = l}{suc off} (elem n n<l sl)
  with split sl
... | ((l1 , l2) , P.refl , eq2)
  with ((Σ (A × List A) λ {(x , l) → l1 ≡ (l ++ [ x ])}) ∋
         (Prod.uncurry (ct' l1) (eql l1 P.refl)))
     where
       eql : ∀ l1' → l1' ≡ l1 → ∃[ n ] ((length l1) ≡ (suc n))
       eql l1' P.refl with
            NatP.+-cancelˡ-≤ off
                (P.subst₂
                  (_≤_)
                  (NatP.+-comm 1 off)
                  (P.trans
                   (P.subst
                     (λ b → (length (l1 ++ l2)) ≡ (length l1) + b)
                     eq2
                     (ListProp.length-++ l1 {l2}))
                   (NatP.+-comm (length l1) off))
                  n<l)
       eql [] P.refl | ()
       eql (x ∷ l1') P.refl | q = length l1' , P.refl
       
       ct : ∀ x l →  Σ (A × List A) λ {(x' , l') → x ∷ l ≡ (l' ++ [ x' ])}
       ct x [] = (x , []) , P.refl
       ct x (x₁ ∷ l)
         with ct x₁ l
       ct x (x₁ ∷ .[]) | (.x₁ , []) , P.refl = (x₁ , [ x ]) , P.refl 
       ct x (x₁ ∷ .(l' ++ x' ∷ [])) | (x' , .x₁ ∷ l') , P.refl = (x' , x ∷ x₁ ∷ l') , P.refl
       ct' : ∀ l n → (length l) ≡ (suc n) → Σ (A × List A) λ {(x' , l') → l ≡ (l' ++ [ x' ])}
       ct' [] n ()
       ct' (x ∷ l) _ P.refl = ct x l
... | (x , l1') , P.refl
    = (l1' , (x ∷ l2))
      , (P.sym $ ListProp.++-assoc l1' [ x ] l2)
      , (P.cong suc eq2)

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


  
