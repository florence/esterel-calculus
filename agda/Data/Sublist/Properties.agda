{-# OPTIONS --allow-unsolved-metas #-}
module Data.Sublist.Properties where

open import Data.Sublist
open import utility.HeterogeneousEquality

open import Data.List as List
  using (List ; [] ; _++_ ; _∷_ ; lookup ; length)
open import Relation.Binary.PropositionalEquality
  using (refl ; _≡_ ; cong ; inspect ; [_] ; subst ; sym ; trans)
open import Data.Nat as Nat
  using (ℕ ; zero ; suc ; _∸_ ; _+_ ; _<_ ; _≤_)
open _≤_
open import Relation.Binary
  using (Irrelevant)
open import Relation.Nullary
  using (¬_)
open import Function
  using (_$_ ; _∋_ ; id)
open import Data.Fin as Fin
  using (fromℕ≤)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Relation.Binary.HeterogeneousEquality as Het
  using (_≅_ ; ≡-to-≅ ; ≅-to-type-≡)
  renaming (refl to hrefl ; cong to hcong)
open import Data.Maybe as Maybe
  using (just)
open import Data.Product as Prod
  using (_,_ ; _,′_ ; proj₁ ; proj₂ ; Σ-syntax ; _×_)


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


fromℕ≤-suc-must-suc : ∀{m}{n} → (lt : m < n) → ¬ fromℕ≤ (s≤s lt) ≡ Fin.zero
fromℕ≤-suc-must-suc {zero} {zero} ()
fromℕ≤-suc-must-suc {zero} {suc n} (s≤s lt) ()
fromℕ≤-suc-must-suc {suc m} {zero} ()
fromℕ≤-suc-must-suc {suc m} {suc n} (s≤s lt) ()

fromℕ≤-inner : ∀{m}{n}{fin} → (lt : m < n) → fromℕ≤ (s≤s lt) ≡ Fin.suc fin →  fromℕ≤ lt ≡ fin
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
lookup-++ (x ∷ h) l index lt i<l (s≤s i<h++l) | Fin.zero | [ eq ]
   rewrite NatProp.+-∸-assoc 1 (ug{i = index}{l} h lt)
   = ⊥-elim $ fromℕ≤-suc-must-suc{(length (h ++ l)) ∸ index}{(length (h ++ l))} i<h++l eq
   --⊥-elim $ fromℕ≤-suc-must-suc (s≤s {!i<h++l!}) {!!}  {!eq!}
lookup-++ (x ∷ h) l index lt i<l (s≤s i<h++l) | Fin.suc fin | [ eq ]
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
... | Fin.zero | [ eq ] = ⊥-elim $ fromℕ≤-suc-must-suc o1 eq 
... | Fin.suc a | [ eq ] with fromℕ≤ (s≤s o2) | inspect fromℕ≤ (s≤s o2)
... | Fin.zero | [ eq2 ] = ⊥-elim $ fromℕ≤-suc-must-suc o2 eq2 
... | Fin.suc b | [ eq2 ]
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

equal-list-equal-sublist-het : ∀{a}{A : Set a}{B : Set a}{l1}{l2}{off1 off2}
                               → (sl1 : Sublist{A = A} l1 off1)
                               → (sl2 : Sublist{A = B} l2 off2)
                               → A ≅ B
                               → l1 ≅ l2
                               → off1 ≡ off2
                               → sl1 ≅ sl2
equal-list-equal-sublist-het empty empty eq1 eq2 refl
   = Het.cong₂ (λ T l → empty{l = l}) eq1 eq2
equal-list-equal-sublist-het{A = A}{B = B}{l1 = l1}{l2 = l2}{off1 = (suc off)}{off2 = .(suc off)} (elem n n<l sl1) (elem .n n<l₁ sl2) eq1 eq2 refl
  = (cong₄
         (λ _ l lt sub → (elem{l = l} n lt sub))
         eq1 
         eq2
         (het-list-lt-eq n l1 l2 n<l n<l₁ eq1 eq2)
         $ equal-list-equal-sublist-het sl1 sl2 eq1 eq2 refl)

     
    where
      het-cons-injective : ∀ (x : A) → (y : B)
                           → (l1 : List A) → (l2 : List B)
                           → A ≅ B
                           → (x ∷ l1 ≅ y ∷ l2)
                           → x ≅ y × (l1 ≅ l2)
      het-cons-injective x .x l2 .l2 hrefl hrefl = hrefl , hrefl
      het-list-lt-eq : ∀ n → (l1 : List A) → (l2 : List B)
                        → (n<l1 : n < (length l1))
                        → (n<l2 : n < (length l2))
                        → A ≅ B
                        → l1 ≅ l2
                        → n<l1 ≅ n<l2
      het-list-lt-eq n [] [] n<l1 n<l2 eq1 eq2 = ≡-to-≅ $ NatProp.≤-irrelevance n<l1 n<l2
      het-list-lt-eq n [] (x ∷ l2) n<l1 n<l2 hrefl ()
      het-list-lt-eq n (x ∷ l1) [] n<l1 n<l2 hrefl ()
      het-list-lt-eq zero (x ∷ .l2) (.x ∷ l2) (s≤s z≤n) (s≤s z≤n) hrefl hrefl = hrefl
      het-list-lt-eq (suc n) (x ∷ l1) (x₁ ∷ l2) (s≤s n<l1) (s≤s n<l2) eq1 eq2
        =  cong₄{B = List}{C = λ t _ → t}{D = λ _ l _ → n < length l}{E = λ t l x lt → (suc n) < (length (x ∷ l))}
               (λ _ _ _ lt → s≤s lt)
               eq1 (proj₂ (het-cons-injective x x₁ l1 l2 eq1 eq2))
               (proj₁ (het-cons-injective x x₁ l1 l2 eq1 eq2))
               $ het-list-lt-eq n l1 l2 n<l1 n<l2 eq1
               $ proj₂ $ het-cons-injective x x₁ l1 l2 eq1 eq2

fromℕ-subt-lt-head : ∀ l lt →
  (fromℕ≤ (get-sub-lt l (suc l) lt))
    ≡
  Fin.zero
fromℕ-subt-lt-head l lt
  with (get-sub-lt l (suc l) lt)
fromℕ-subt-lt-head l lt | s≤s x
  with  (suc l) ∸ (suc l) | NatProp.n∸n≡0 (suc l)
fromℕ-subt-lt-head l lt | s≤s z≤n | .0 | refl = refl


get-first-is-first-from-head : ∀{a}{A : Set a}→ (x : A) → (l : List A)
                               → (get (sublist (x ∷ l))) ≡ x
get-first-is-first-from-head x l
 = cong (lookup (x ∷ l)) $ fromℕ-subt-lt-head (length l) (s≤s (NatProp.≤-reflexive refl))
           
get-first-is-first : ∀{a}{A : Set a}{l}{off}
                     → (sl : Sublist{A = A} l (suc off))
                     → (suc off) ≡ (length l)
                     → just (get sl) ≡ (List.head l)
get-first-is-first {l = []} {off} sl ()
get-first-is-first {l = x ∷ l} {.(length l)} sl refl
  rewrite sublist-irrelevant sl (sublist (x ∷ l))
    = cong just $ get-first-is-first-from-head x l 
  

split-stepʳ : ∀{a}{A : Set a}{l : List A}{off}
             → (s1 : Sublist l (suc off))
             → (s2 : Sublist l off)
             → (proj₂ (proj₁ (split s1)))
                 ≡
               ((get s1) ∷ (proj₂ (proj₁ (split s2))))
split-stepʳ l@(elem n n<l s1) s2
    with split l
       | split s2
... | (l1 , l2) , eq1 , eq2
    | (sl1 , sl2) , seq1 , seq2
  rewrite sublist-irrelevant s1 s2
    = {!trans eq1 (sym seq1)!}

split-stepˡ : ∀{a}{A : Set a}{l : List A}{off}
             → (s1 : Sublist l (suc off))
             → (s2 : Sublist l off)
             → ((proj₁ (proj₁ (split s1))) ++ List.[ (get s1) ])
                 ≡
               (proj₂ (proj₁ (split s2)))
split-stepˡ l@(elem n n<l s1) sl2
   with split l
      | split sl2
      | split-stepʳ l sl2
... | a | b | refl rewrite sublist-irrelevant s1 sl2
  = {!!}

              
split-startˡ : ∀{a}{A : Set a}
              → (l : List A)
              → [] ≡ (proj₁ (proj₁ (split (sublist l))))
split-startˡ l with (split (sublist l))
split-startˡ .b | ([] , b) , refl , eq2 = refl
split-startˡ .(x ∷ a ++ b) | (x ∷ a , b) , refl , eq2
  with NatProp.+-cancelʳ-≡ 0
        (suc (length a))
        (subst
           (λ x → (length b) ≡ suc x)
           (ListProp.length-++ a {b})
           eq2)
... | ()
  
               

split-startʳ : ∀{a}{A : Set a}
              → (l : List A)
              → l ≡ (proj₂ (proj₁ (split (sublist l))))
split-startʳ l with split (sublist l)
                 | split-startˡ l
... | (.[] , q) , refl , _ | refl = refl             
