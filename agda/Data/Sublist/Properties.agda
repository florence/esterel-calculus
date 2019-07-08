module Data.Sublist.Properties where

open import Data.Sublist

open import Data.List as List
  using (List ; [] ; _++_ ; _∷_ ; lookup ; length)
open import Relation.Binary.PropositionalEquality
  using (refl ; _≡_ ; cong ; inspect ; [_] ; subst ; sym)
open import Data.Nat as Nat
  using (ℕ ; zero ; suc ; _∸_ ; _+_ ; _<_ ; _≤_)
open _≤_
open import Relation.Binary
  using (Irrelevant)
open import Relation.Nullary
  using (¬_)
open import Function
  using (_$_)
open import Data.Fin
  using (fromℕ≤)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Relation.Binary.HeterogeneousEquality
  using (_≅_)
  renaming (refl to hrefl ; cong to hcong)

open import Data.Nat.Properties as NatProp
  using ()
open import Data.List.Properties as ListProp
  using ()
open import Data.Fin.Properties as FinProp
  using ()

sublist-irrelevant : ∀{a}{A : Set a} → Irrelevant $ Sublist{A = A}
sublist-irrelevant empty empty = refl
sublist-irrelevant (elem n n<l a) (elem .n n<l₁ b)
  rewrite NatProp.≤-irrelevance n<l n<l₁
        | sublist-irrelevant a b
  = refl

sucn-not≤n : ∀ {n} → ¬ suc n ≤ n
sucn-not≤n {zero} ()
sucn-not≤n {suc n} (s≤s lt) = sucn-not≤n lt


fromℕ≤-suc-must-suc : ∀{m}{n} → (lt : m < n) → ¬ fromℕ≤ (s≤s lt) ≡ Data.Fin.zero
fromℕ≤-suc-must-suc {zero} {zero} ()
fromℕ≤-suc-must-suc {zero} {suc n} (s≤s lt) ()
fromℕ≤-suc-must-suc {suc m} {zero} ()
fromℕ≤-suc-must-suc {suc m} {suc n} (s≤s lt) ()

fromℕ≤-inner : ∀{m}{n}{fin} → (lt : m < n) → fromℕ≤ (s≤s lt) ≡ Data.Fin.suc fin →  fromℕ≤ lt ≡ fin
fromℕ≤-inner {zero} {zero} () eq
fromℕ≤-inner {zero} {suc n} (s≤s lt) refl = refl
fromℕ≤-inner {suc m} {zero} () eq
fromℕ≤-inner {suc m} {suc n} (s≤s lt) refl = refl

ug : ∀{a}{A : Set a}{i}{l} → (h : List A)  → i ≤ (length l) → i ≤ (length (h ++ l))
ug [] lt = lt
ug (x ∷ h) lt = NatProp.≤-stepsˡ 1 $ ug h lt

lookup-++ : ∀{a}{A : Set a}
            → (h : List A) → (l : List A)
            → ∀ index
            → (index ≤ (length l))
            → (i<l : (length l) ∸  index < (length l))
            → (i<h++l : ((length (h ++ l)) ∸ index) < length (h ++ l))
            → lookup l (fromℕ≤ i<l) ≡ lookup (h ++ l) (fromℕ≤ i<h++l) 
lookup-++ [] l index lt i<l i<h++l rewrite NatProp.≤-irrelevance i<l i<h++l = refl
lookup-++ (x ∷ h) l index lt i<l (s≤s i<h++l)
 with fromℕ≤ (s≤s i<h++l) | inspect fromℕ≤ (s≤s i<h++l)
lookup-++ (x ∷ h) l index lt i<l (s≤s i<h++l) | Data.Fin.zero | [ eq ]
   rewrite NatProp.+-∸-assoc 1 (ug{i = index}{l} h lt)
   = ⊥-elim $ fromℕ≤-suc-must-suc{(length (h ++ l)) ∸ index}{(length (h ++ l))} i<h++l eq
   --⊥-elim $ fromℕ≤-suc-must-suc (s≤s {!i<h++l!}) {!!}  {!eq!}
lookup-++ (x ∷ h) l index lt i<l (s≤s i<h++l) | Data.Fin.suc fin | [ eq ]
   rewrite NatProp.+-∸-assoc 1 (ug{i = index}{l} h lt)
   = subst (λ x → lookup l (fromℕ≤ i<l) ≡ lookup (h ++ l) x) (fromℕ≤-inner i<h++l eq)  (lookup-++ h l index lt i<l i<h++l) 


++-get-≡ : ∀{a}{A : Set a}{l : List A} h off
           → (sl1 : Sublist (h ++ l) (suc off))
           → (sl2 : Sublist l (suc off))
           → get sl1 ≡ get sl2
++-get-≡ {l = l} h off (elem .off n<h++l sl1) (elem .off n<l sl2)
  rewrite lookup-++ h l (suc off) n<l
                    (get-sub-lt _ _ n<l)
                    $ get-sub-lt _ _ n<h++l
     = refl

map-lookup : ∀{a b}{A : Set a}{B : Set b}{off1}{off2}
             → (f : A → B) 
             → (l : List A)
             → (o1 : off1 < (length l))
             → (o2 : off2 < (length (List.map f l)))
             → off1 ≡ off2
             → (f $ lookup l (fromℕ≤ o1)) ≡ lookup (List.map f l) (fromℕ≤ o2) 
map-lookup {off1 = zero} {off2 = .zero} f [] () o2 refl
map-lookup {off1 = zero} {off2 = .zero} f (x ∷ l) (s≤s z≤n) (s≤s z≤n) refl = refl
map-lookup {off1 = suc off} {off2 = .suc off} f [] () o2 refl
map-lookup {off1 = suc off} {off2 = .suc off} f (x ∷ l) (s≤s o1) (s≤s o2) refl
   with fromℕ≤ (s≤s o1) | inspect fromℕ≤ (s≤s o1) 
... | Data.Fin.zero | [ eq ] = ⊥-elim $ fromℕ≤-suc-must-suc o1 eq 
... | Data.Fin.suc a | [ eq ] with fromℕ≤ (s≤s o2) | inspect fromℕ≤ (s≤s o2)
... | Data.Fin.zero | [ eq2 ] = ⊥-elim $ fromℕ≤-suc-must-suc o2 eq2 
... | Data.Fin.suc b | [ eq2 ]
   rewrite sym $ fromℕ≤-inner o1 eq
         | sym $ fromℕ≤-inner o2 eq2
   = map-lookup f l o1 o2 refl


map-get : ∀{a b}{A : Set a}{B : Set b}{l}{off}
          → (f : A → B)
          → (sl : (Sublist l (suc off)))
          → (f (get sl)) ≡ (get (map f sl))
map-get{l = l} f (elem n n<l sl) with map f (elem n n<l sl)
map-get{a}{b}{A}{B}{l = l} f (elem n n<l sl) | elem .n n<l₁ x
  = map-lookup f l
               (get-sub-lt _ _ n<l)
               (get-sub-lt _ _ n<l₁)
               $ sym $ cong (_∸ suc n) (ListProp.length-map f l)

equal-list-equal-sublist : ∀{a}{A : Set a}{l1}{l2}{off}
                           → (sl1 : Sublist{A = A} l1 off)
                           → (sl2 : Sublist l2 off)
                           → l1 ≡ l2
                           → sl1 ≅ sl2

equal-list-equal-sublist empty empty refl = hrefl
equal-list-equal-sublist (elem n n<l sl1) (elem .n n<l₁ sl2) refl
  rewrite NatProp.≤-irrelevance n<l₁ n<l
  = hcong (elem n n<l) $ equal-list-equal-sublist sl1 sl2 refl 
           
{-

lookup-tail-get-equal : ∀{a}{A : Set a} →  (l : List A) → ∀ x n
      → n < (length l)
      → (n<l   : ((length l) ∸ suc n) < (length l))
      → (n<x∷l : ((length (x ∷ l)) ∸ suc n) < (length (x ∷ l)))
      → lookup l (fromℕ≤ n<l)
        ≡
        lookup (x ∷ l) (fromℕ≤ n<x∷l)
lookup-tail-get-equal l x n lt n<l n<x∷l
  rewrite (NatProp.+-∸-assoc 1 {length l} {suc n} lt)
  = lookup-tail-get-equal-help l x ((length l) ∸ suc n) n<l n<x∷l
  where
    lookup-tail-get-equal-help : ∀{a}{A : Set a} →  (l : List A) → ∀ x n
      → (n<l   : n < (length l))
      → (n<x∷l : (suc n) < (length (x ∷ l)))
      → lookup l (fromℕ≤ n<l)
        ≡
        lookup (x ∷ l) (fromℕ≤ n<x∷l)
    lookup-tail-get-equal-help l x zero n>l n<x∷l = {!!}
    lookup-tail-get-equal-help l x (suc n) n>l n<x∷l = {!!}


lookup-tail-get-equal l x n n<1 n<x∷l = {!!} 

sublist-tail-get-equal : ∀{a}{A : Set a}{l : List A}{off} x
                         → (sl1 : Sublist l (suc off))
                         → (sl2 : Sublist (x ∷ l) (suc off))
                         → (get sl1) ≡ (get sl2)
sublist-tail-get-equal{l = l} x (elem n n<l sl1) (elem .n n<l₁ sl2)
    = lookup-tail-get-equal l x n n<l (get-sub-lt n (length l) n<l) (get-sub-lt n (length (x ∷ l)) n<l₁)

-- 
-}
