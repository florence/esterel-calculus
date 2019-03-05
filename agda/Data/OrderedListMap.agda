import Level
open import Relation.Binary
  using (Decidable ; Rel ; IsStrictTotalOrder ; Tri)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; sym ; module ≡-Reasoning ; inspect ; subst)
open import Data.Nat as Nat
  using (ℕ ; suc ; zero ; _≤′_ ; _≤_ ; _+_ ; s≤s ; z≤n ; ≤′-refl ;
         ≤′-step)
open import Data.Nat.Properties as NatP
  using (≤⇒≤′ ; ≤′⇒≤ ;  m≤m+n ; s≤′s)
open import Data.Nat.Properties.Simple as NatPS
  using (+-comm ; +-suc)
open import Data.Product using (∃)

open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
import Relation.Unary as U

open import Data.MoreNatProp

module Data.OrderedListMap
  (Key : Set)
  (inject : Key → ℕ)
  (Value : Set)
  where

open import utility

open import Data.Maybe using (just ; nothing ; Maybe)

open import Function
  using (_∘_ ; _∋_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; _++_ ; [_] ; [] ; _∷_ ; map)
open import Data.List.All as All
  using (All)

open import Data.Product
  using (Σ ; Σ-syntax ; _,_ ; proj₁ ; proj₂ ; _×_ ; _,′_ ; ∃-syntax)
open import Data.Sum
  using (inj₁ ; inj₂ ; _⊎_)
open import Data.Unit
  using (⊤ ; tt)
open import Relation.Nullary
  using (yes ; no ; ¬_)
open import Data.List.Any using (here ; there)
open import Data.List.Any.Properties using (∷↔ ; ⊥↔Any[])
  renaming ( ++⁺ˡ  to ++ˡ ; ++⁺ʳ to ++ʳ ) 
open import Function using (_∘_)
open import Function.Inverse using (_↔_ ; Inverse)
open import Function.Equality using (Π)

open import Data.Bool using (Bool ; true ; false)

infix 6 _U_

LMap : Set
LMap = List (Maybe Value)

m-insert : Maybe Value → ℕ → LMap → LMap
m-insert v zero [] = [ v ]
m-insert nothing zero (x ∷ l) = x ∷ l
m-insert (just v) zero (x ∷ l) = (just v) ∷ l
m-insert v (suc n) [] = nothing ∷ (m-insert v n [])
m-insert v (suc n) (x ∷ l) = x ∷ (m-insert v n l)

insert : Key → Value → LMap → LMap
insert k v l = m-insert (just v) (inject k) l

Dom' : LMap → List ℕ
Dom' [] = []
Dom' ((just _) ∷ l) = 0 ∷ (map suc (Dom' l))
Dom' (nothing ∷ l) = (map suc (Dom' l))

_U_ : LMap → LMap → LMap
[] U m2 = m2
(x ∷ m1) U [] = (x ∷ m1)
(just x ∷ m1) U (just x₁ ∷ m2) = just x₁ ∷ (m1 U m2)
(just x ∷ m1) U (nothing ∷ m2) = just x ∷ (m1 U m2)
(nothing ∷ m1) U (just x ∷ m2) = just x ∷ (m1 U m2)
(nothing ∷ m1) U (nothing ∷ m2) = nothing ∷ (m1 U m2)

dist'::b : ∀{V1 V2 S1 S2} → (distinct'{ℕ} (S1 ∷ V1) (S2 ∷ V2)) → (distinct' V1 V2)
dist'::b d = dist'-sym (dist':: (dist'-sym (dist':: d)))

dist-cons : ∀{k k' l l'} → distinct'{ℕ} (k ∷ l) (k' ∷ l') → ¬ k ≡ k'
dist-cons {k} d refl = d k (here refl) (here refl)

data dist-dom : LMap → LMap → Set where
  el : ∀{l} → dist-dom [] l
  le : ∀{l} → dist-dom l []
  cl : ∀{l1 l2 v} → dist-dom l1 l2 → dist-dom (nothing ∷ l1) ((just v) ∷ l2)
  lc : ∀{l1 l2 v} → dist-dom l1 l2 → dist-dom ((just v) ∷ l1) (nothing ∷ l2)
  nn : ∀{l1 l2} → dist-dom l1 l2 → dist-dom (nothing ∷ l1) (nothing ∷ l2)


∈→⊥ : ∀{A} {z : A} → z ∈ [] → ⊥
∈→⊥{A}{z} ()

-- Π._⟨$⟩_ (Inverse.from (⊥↔Any[]{A = A}{P = _≡_ z})) x

dist-b : ∀{l l' x} → distinct' (x ∷ l) (x ∷ l') → ⊥
dist-b{x = x} d with (dist-cons d)
... | relf = d x (here refl) (here refl)

sucin : ∀{z n} → z ∈ n → (suc z) ∈ (map suc n)
sucin {z} {.(_ ∷ _)} (here px) rewrite px = here refl
sucin {z} {.(_ ∷ _)} (there I) = (there (sucin I))

suc≡ : ∀{z w} → suc z ≡ suc w → z ≡ w
suc≡ refl = refl

sucout : ∀{z n} → (suc z) ∈ (map suc n) → z ∈ n
sucout {z} {[]} ()
sucout {z} {x ∷ n} (here px) rewrite suc≡ px = (here refl)
sucout {z} {x ∷ n} (there I) = (there (sucout I))

dist-map : ∀{m n} → distinct' (map suc m) (map suc n) → distinct' m n
dist-map {[]} {[]} d = λ z x x₁ → ∈→⊥ x
dist-map {[]} {x ∷ n} d = λ z x₁ x₂ →  ∈→⊥ x₁
dist-map {x ∷ m} {[]} d = λ z x₁ x₂ → ∈→⊥ x₂
dist-map {zero ∷ m} {zero ∷ n} d =  ⊥-elim (dist-b d)
dist-map {zero ∷ m} {suc y ∷ n} d z x x₁ = d (suc z) (sucin x) (sucin x₁)
dist-map {suc y ∷ m} {zero ∷ n} d z x x₁ = d (suc z) (sucin x) (sucin x₁)
dist-map {suc _ ∷ m} {suc y ∷ n} d z x x₁ = d (suc z) (sucin x) (sucin x₁)

dist-in : ∀{m1 m2 x y} → distinct' (Dom' (x ∷ m1)) (Dom' (y ∷ m2)) → distinct' (Dom' m1) (Dom' m2)
dist-in {[]} {[]} {x} {y} dd = λ z x₁ x₂ → ∈→⊥ x₁
dist-in {[]} {x ∷ m2} {x₁} {y} dd = λ z x₂ x₃ → ∈→⊥ x₂
dist-in {x ∷ m1} {[]} {x₁} {y} dd = λ z x₂ x₃ → ∈→⊥ x₃
dist-in {h₁ ∷ m1} {h₂ ∷ m2} {just x} {just x₁} dd = ⊥-elim (dist-b dd)
dist-in {h₁ ∷ m1} {h₂ ∷ m2} {just x} {nothing} dd = λ z x₁ x₂ → (dist'-sym (dist':: (dist'-sym dd))) _ (sucin x₁) (sucin x₂)
dist-in {h₁ ∷ m1} {h₂ ∷ m2} {nothing} {just x} dd = λ z x₁ x₂ → (dist':: dd) _ (sucin x₁) (sucin x₂)
dist-in {h₁ ∷ m1} {h₂ ∷ m2} {nothing} {nothing} dd = dist-map dd
-- ((Π._⟨$⟩_ (Inverse.to (∷↔ (_≡_ _)))) (inj₂ x₂))

dist-gen : ∀{m1 m2} → distinct' (Dom' m1) (Dom' m2) → dist-dom m1 m2
dist-gen {[]} {[]} dd = el
dist-gen {[]} {x ∷ m2} dd = el
dist-gen {x ∷ m1} {[]} dd = le
dist-gen {just x ∷ m1} {just x₁ ∷ m2} dd = ⊥-elim (dist-b dd)
dist-gen {just x ∷ m1} {nothing ∷ m2} dd = lc (dist-gen (dist-in{m1}{m2}{just x}{nothing} dd))
dist-gen {nothing ∷ m1} {just x ∷ m2} dd = cl (dist-gen (dist-in{m1}{m2}{nothing}{just x} dd))
dist-gen {nothing ∷ m1} {nothing ∷ m2} dd = nn (dist-gen (dist-in{m1}{m2}{nothing}{nothing} dd))

U-comm' : ∀{m1 m2} → dist-dom m1 m2 → (m1 U m2) ≡ (m2 U m1)
U-comm' {.[]} {[]} el = refl
U-comm' {.[]} {x ∷ m2} el = refl
U-comm' {[]} {.[]} le = refl
U-comm' {x ∷ m1} {.[]} le = refl
U-comm' {.(nothing ∷ _)} {.(just _ ∷ _)} (cl dd) rewrite U-comm' dd = refl
U-comm' {.(just _ ∷ _)} {.(nothing ∷ _)} (lc dd) rewrite U-comm' dd = refl
U-comm' {.(nothing ∷ _)} {.(nothing ∷ _)} (nn dd) rewrite U-comm' dd = refl

U-comm : ∀{m1 m2} → distinct' (Dom' m1) (Dom' m2) → (m1 U m2) ≡ (m2 U m1)
U-comm{m1}{m2} dd = U-comm'{m1}{m2} (dist-gen dd)

U-assoc' : ∀ m1 m2 m3 → m1 U (m2 U m3) ≡ (m1 U m2) U m3
U-assoc' [] m2 m3 = refl
U-assoc' (x ∷ m1) [] m3 = refl
U-assoc' (x ∷ m1) (x₁ ∷ m2) []
  rewrite U-comm {(x ∷ m1) U (x₁ ∷ m2)} {[]} (λ _ _ ()) = refl
U-assoc' (just x ∷ m1) (just x₁ ∷ m2) (just x₂ ∷ m3) rewrite U-assoc' m1 m2 m3 = refl
U-assoc' (just x ∷ m1) (just x₁ ∷ m2) (nothing ∷ m3) rewrite U-assoc' m1 m2 m3 = refl
U-assoc' (just x ∷ m1) (nothing ∷ m2) (just x₁ ∷ m3) rewrite U-assoc' m1 m2 m3 = refl
U-assoc' (just x ∷ m1) (nothing ∷ m2) (nothing ∷ m3) rewrite U-assoc' m1 m2 m3 = refl
U-assoc' (nothing ∷ m1) (just x ∷ m2) (just x₁ ∷ m3) rewrite U-assoc' m1 m2 m3 = refl
U-assoc' (nothing ∷ m1) (just x ∷ m2) (nothing ∷ m3) rewrite U-assoc' m1 m2 m3 = refl
U-assoc' (nothing ∷ m1) (nothing ∷ m2) (just x ∷ m3) rewrite U-assoc' m1 m2 m3 = refl
U-assoc' (nothing ∷ m1) (nothing ∷ m2) (nothing ∷ m3) rewrite U-assoc' m1 m2 m3 = refl

U-assoc : ∀ m1 m2 m3 → m1 U (m2 U m3) ≡ (m1 U m2) U m3
U-assoc m1 m2 m3 = U-assoc' m1 m2 m3

0∈S : ∀{l} → 0 ∈ (map suc l) → ⊥
0∈S {[]} ()
0∈S {x ∷ l} (here ())
0∈S {x ∷ l} (there p) = 0∈S p

n∈S : ∀{n x l} → suc n ∈ Dom' (x ∷ l) → n ∈ Dom' l
n∈S {n} {just x} {[]} (here ())
n∈S {n} {just x} {[]} (there ())
n∈S {n} {just x} {x₁ ∷ l} (here ())
n∈S {n} {just x} {x₁ ∷ l} (there p) = sucout p
n∈S {n} {nothing} {[]} ()
n∈S {n} {nothing} {x ∷ l} p = sucout p

n+1∈S : ∀ {n x m} → n ∈ (Dom' m) → (suc n) ∈ (Dom' (x ∷ m))
n+1∈S {n} {just x} {m} n∈ = there (sucin n∈)
n+1∈S {n} {nothing} {m} n∈ = sucin n∈

deref : (n : ℕ) → (l : LMap) → n ∈ (Dom' l) → Value
deref zero [] ()
deref zero (just x ∷ l) p = x
deref zero (nothing ∷ l) p = ⊥-elim (0∈S p)
deref (suc n) [] ()
deref (suc n) (x ∷ l) p = deref n l (n∈S{n}{x}{l} p)

-- thrms
deref-∈-irr : ∀{k l} → (∈1 : k ∈ (Dom' l)) →  (∈2 : k ∈ (Dom' l)) → deref k l ∈1 ≡ deref k l ∈2
deref-∈-irr {zero} {[]} () ∈2
deref-∈-irr {suc k} {[]} () ∈2
deref-∈-irr {zero} {just x ∷ l} ∈1 ∈2 = refl
deref-∈-irr {zero} {nothing ∷ l} ∈1 ∈2 = ⊥-elim (0∈S ∈1)
deref-∈-irr {suc k} {x ∷ l} ∈1 ∈2 = deref-∈-irr (n∈S{k}{x}{l} ∈1) (n∈S{k}{x}{l} ∈2) 

insert-mono' : ∀{l d l' d' n n' v} → n ∈ d → d ≡ (Dom' l) → d' ≡ (Dom' l') → l' ≡ (m-insert (just v) n' l) → n ∈ d'
insert-mono' {[]} {.[]} {[]} {.[]} {zero} {zero} () refl refl l'eq
insert-mono' {[]} {.[]} {[]} {.[]} {zero} {suc n'} () refl refl l'eq
insert-mono' {[]} {.[]} {[]} {.[]} {suc n} {zero} () refl refl l'eq
insert-mono' {[]} {.[]} {[]} {.[]} {suc n} {suc n'} () refl refl l'eq
insert-mono' {[]} {.[]} {x ∷ l'} {.(Dom' (x ∷ l'))} {zero} {zero} () refl refl l'eq
insert-mono' {[]} {.[]} {x ∷ l'} {.(Dom' (x ∷ l'))} {zero} {suc n'} () refl refl l'eq
insert-mono' {[]} {.[]} {x ∷ l'} {.(Dom' (x ∷ l'))} {suc n} {zero} () refl refl l'eq
insert-mono' {[]} {.[]} {x ∷ l'} {.(Dom' (x ∷ l'))} {suc n} {suc n'} () refl refl l'eq
insert-mono' {x ∷ l} {.(Dom' (x ∷ l))} {[]} {.[]} {zero} {zero} n∈ refl refl ()
insert-mono' {x ∷ l} {.(Dom' (x ∷ l))} {[]} {.[]} {zero} {suc n'} n∈ refl refl ()
insert-mono' {x ∷ l} {.(Dom' (x ∷ l))} {[]} {.[]} {suc n} {zero} n∈ refl refl ()
insert-mono' {x ∷ l} {.(Dom' (x ∷ l))} {[]} {.[]} {suc n} {suc n'} n∈ refl refl ()
insert-mono' {just x₁ ∷ l} {.(0 ∷ map suc (Dom' l))} {just x ∷ l'} {.(0 ∷ map suc (Dom' l'))} {zero} {zero} {v} N∈ refl refl l'eq = here refl
insert-mono' {just x₁ ∷ l} {.(0 ∷ map suc (Dom' l))} {nothing ∷ l'} {.(map suc (Dom' l'))} {zero} {zero} {v} N∈ refl refl ()
insert-mono' {nothing ∷ .l'} {.(map suc (Dom' l'))} {.(just _) ∷ l'} {.(0 ∷ map suc (Dom' l'))} {zero} {zero} n∈ refl refl refl = here refl
insert-mono' {just x₁ ∷ l} {.(0 ∷ map suc (Dom' l))} {just x ∷ l'} {.(0 ∷ map suc (Dom' l'))} {zero} {suc n'} n∈ refl refl l'eq = here refl
insert-mono' {nothing ∷ l} {.(map suc (Dom' l))} {just x ∷ l'} {.(0 ∷ map suc (Dom' l'))} {zero} {suc n'} n∈ refl refl l'eq = here refl
insert-mono' {just x₁ ∷ .l'} {.(0 ∷ map suc (Dom' l'))} {just x ∷ l'} {.(0 ∷ map suc (Dom' l'))} {suc n} {zero} (here ()) refl refl refl
insert-mono' {just x₁ ∷ .l'} {.(0 ∷ map suc (Dom' l'))} {just x ∷ l'} {.(0 ∷ map suc (Dom' l'))} {suc n} {zero} (there n∈) refl refl refl
    = there n∈
insert-mono' {nothing ∷ .l'} {.(map suc (Dom' l'))} {just x ∷ l'} {.(0 ∷ map suc (Dom' l'))} {suc n} {zero} n∈ refl refl refl = there n∈
insert-mono' {just x ∷ l} {.(0 ∷ map suc (Dom' l))} {nothing ∷ l'} {.(map suc (Dom' l'))} {suc n} {zero} n∈ refl refl ()
insert-mono' {nothing ∷ l} {.(map suc (Dom' l))} {nothing ∷ l'} {.(map suc (Dom' l'))} {suc n} {zero} n∈ refl refl ()
insert-mono' {just x₁ ∷ l} {.(0 ∷ map suc (Dom' l))} {just x ∷ l'} {.(0 ∷ map suc (Dom' l'))} {suc n} {suc n'} (here ()) refl refl l'eq
insert-mono' {just x₁ ∷ l} {.(0 ∷ map suc (Dom' l))} {just .x₁ ∷ .(m-insert (just _) n' l)} {.(0 ∷ map suc (Dom' (m-insert (just _) n' l)))} {suc n} {suc n'} {v} (there n∈) refl refl refl
  = there (sucin (insert-mono'{l = l}{l' = (m-insert (just _) n' l)}{n = n}{n' = n'}{v} (sucout n∈) refl refl refl))
insert-mono' {just x ∷ l} {.(0 ∷ map suc (Dom' l))} {nothing ∷ l'} {.(map suc (Dom' l'))} {suc n} {suc n'} (here ()) refl refl l'eq
insert-mono' {just x ∷ l} {.(0 ∷ map suc (Dom' l))} {nothing ∷ l'} {.(map suc (Dom' l'))} {suc n} {suc n'} {v} (there n∈) refl refl ()
insert-mono' {nothing ∷ l} {.(map suc (Dom' l))} {just x ∷ l'} {.(0 ∷ map suc (Dom' l'))} {suc n} {suc n'} n∈ refl refl ()
insert-mono' {nothing ∷ l} {.(map suc (Dom' l))} {nothing ∷ l'} {.(map suc (Dom' l'))} {suc n} {suc n'} {v} n∈ refl refl refl
  =  sucin (insert-mono'{l = l}{l' = l'}{n = n}{n' = n'}{v = v} (sucout n∈) refl refl refl)
insert-mono' {just x ∷ l} {.(0 ∷ map suc (Dom' l))} {nothing ∷ l'} {.(map suc (Dom' l'))} {zero} {suc n'} n∈ refl refl ()
insert-mono' {nothing ∷ l} {.(map suc (Dom' l))} {nothing ∷ l'} {.(map suc (Dom' l'))} {zero} {suc n'} n∈ refl refl l'eq = ⊥-elim (0∈S n∈)

insert-mono : ∀{m n n' v} → n ∈ (Dom' m) → n ∈ (Dom' (m-insert (just v) n' m))
insert-mono{m}{n}{n'}{v} i = insert-mono'{m}{Dom' m}{(m-insert (just v) n' m)}{(Dom' (m-insert (just v) n' m))}{n}{n'}{v} i refl refl refl

U-mono : ∀{m m' n} → n ∈ (Dom' m) → n ∈ (Dom' (m U m'))
U-mono {[]} {m'} {n} ()
U-mono {just x ∷ m} {[]} {n} (here px) = here px
U-mono {just x ∷ m} {just x₁ ∷ m'} {n} (here px) = here px
U-mono {just x ∷ m} {nothing ∷ m'} {n} (here px) = here px
U-mono {just x ∷ m} {[]} {n} (there ∈) = there ∈
U-mono {just x ∷ m} {just x₁ ∷ m'} {zero} (there ∈) = here refl
U-mono {just x ∷ m} {nothing ∷ m'} {zero} (there ∈) = here refl
U-mono {just x ∷ m} {just x₁ ∷ m'} {suc n} (there ∈) = there (sucin (U-mono{m}{m'}{n} (sucout ∈)))
U-mono {just x ∷ m} {nothing ∷ m'} {suc n} (there ∈) = there (sucin (U-mono{m}{m'}{n} (sucout ∈)))
U-mono {nothing ∷ m} {[]} {n} ∈ = ∈
U-mono {nothing ∷ m} {just x ∷ m'} {zero} ∈ = here refl
U-mono {nothing ∷ m} {just x ∷ m'} {suc n} ∈ = there (sucin (U-mono{m}{m'}{n} (sucout ∈)))
U-mono {nothing ∷ m} {nothing ∷ m'} {zero} ∈ = ⊥-elim (0∈S ∈)
U-mono {nothing ∷ m} {nothing ∷ m'} {suc n} ∈ = (sucin (U-mono{m}{m'}{n} (sucout ∈)))



U⁻ : ∀ {m m' n} → n ∈ Dom' (m U m') → (n ∈ Dom' m) ⊎ (n ∈ Dom' m')
U⁻ {[]} {[]} {n} n∈Dom⟨mUm'⟩ = inj₁ n∈Dom⟨mUm'⟩
U⁻ {[]} {x ∷ m'} {n} n∈Dom⟨mUm'⟩ = inj₂ n∈Dom⟨mUm'⟩
U⁻ {x ∷ m} {[]} {n} n∈Dom⟨mUm'⟩ = inj₁ n∈Dom⟨mUm'⟩
U⁻ {just x ∷ m} {just x₁ ∷ m'} {zero} n∈Dom⟨mUm'⟩ = inj₁ (here refl)
U⁻ {just x ∷ m} {just x₁ ∷ m'} {suc n} (here ())
U⁻ {just x ∷ m} {just x₁ ∷ m'} {suc n} (there n∈Dom⟨mUm'⟩) with U⁻ {m} {m'} {n} (sucout n∈Dom⟨mUm'⟩)
... | inj₁ ∈Dom-m  = inj₁ (there (sucin ∈Dom-m))
... | inj₂ ∈Dom-m' = inj₂ (there (sucin ∈Dom-m'))
U⁻ {just x ∷ m} {nothing ∷ m'} {zero} n∈Dom⟨mUm'⟩ = inj₁ (here refl)
U⁻ {just x ∷ m} {nothing ∷ m'} {suc n} (here ())
U⁻ {just x ∷ m} {nothing ∷ m'} {suc n} (there n∈Dom⟨mUm'⟩) with U⁻ {m} {m'} {n} (sucout n∈Dom⟨mUm'⟩)
... | inj₁ ∈Dom-m  = inj₁ (there (sucin ∈Dom-m))
... | inj₂ ∈Dom-m' = inj₂ (sucin ∈Dom-m')
U⁻ {nothing ∷ m} {just x ∷ m'} {zero} n∈Dom⟨mUm'⟩ = inj₂ (here refl)
U⁻ {nothing ∷ m} {just x ∷ m'} {suc n} (here ())
U⁻ {nothing ∷ m} {just x ∷ m'} {suc n} (there n∈Dom⟨mUm'⟩) with U⁻ {m} {m'} {n} (sucout n∈Dom⟨mUm'⟩)
... | inj₁ ∈Dom-m  = inj₁ (sucin ∈Dom-m)
... | inj₂ ∈Dom-m' = inj₂ (there (sucin ∈Dom-m'))
U⁻ {nothing ∷ m} {nothing ∷ m'} {zero} n∈Dom⟨mUm'⟩ = ⊥-elim (0∈S n∈Dom⟨mUm'⟩)
U⁻ {nothing ∷ m} {nothing ∷ m'} {suc n} n∈Dom⟨mUm'⟩ with U⁻ {m} {m'} {n} (sucout n∈Dom⟨mUm'⟩)
... | inj₁ ∈Dom-m  = inj₁ (sucin ∈Dom-m)
... | inj₂ ∈Dom-m' = inj₂ (sucin ∈Dom-m')

Dom'-1map : ∀ n v → Dom' (m-insert (just v) n []) ≡ (n ∷ [])
Dom'-1map zero v = refl
Dom'-1map (suc n) v rewrite Dom'-1map n v = refl

Dom'-2map : ∀ n₁ v₁ n₂ v₂ →
  (Dom' (m-insert (just v₂) n₂ (m-insert (just v₁) n₁ [])) ≡ n₁ ∷ [] × n₁ ≡ n₂) ⊎
  (Dom' (m-insert (just v₂) n₂ (m-insert (just v₁) n₁ [])) ≡ n₁ ∷ n₂ ∷ []) ⊎
  (Dom' (m-insert (just v₂) n₂ (m-insert (just v₁) n₁ [])) ≡ n₂ ∷ n₁ ∷ [])
Dom'-2map zero v₁ zero v₂ = inj₁ (refl , refl)
Dom'-2map zero v₁ (suc n₂) v₂ rewrite Dom'-1map n₂ v₂ = inj₂ (inj₁ refl)
Dom'-2map (suc n₁) v₁ zero v₂ rewrite Dom'-1map n₁ v₁ = inj₂ (inj₂ refl)
Dom'-2map (suc n₁) v₁ (suc n₂) v₂ with Dom'-2map n₁ v₁ n₂ v₂
... | inj₁ (xs≡[n₁] , refl)  rewrite xs≡[n₁] = inj₁ (refl , refl)
... | inj₂ (inj₁ xs≡[n₁,n₂]) rewrite xs≡[n₁,n₂] = inj₂ (inj₁ refl)
... | inj₂ (inj₂ xs≡[n₂,n₁]) rewrite xs≡[n₂,n₁] = inj₂ (inj₂ refl)

negsucun : ∀{k k'} → ¬ (suc k ≡ suc k') → k ≡ k' → ⊥
negsucun neg = (λ eq → neg (cong suc eq))

-- sucout : ∀{z n} → (suc z) ∈ (map suc n) → z ∈ n
sucinout : ∀{k nn}
           → (kin : (suc k) ∈ (map suc nn))
           → sucin (sucout kin) ≡ kin
sucinout {zero} {[]} ()
sucinout {zero} {.0 ∷ nn₁} (here refl) = refl
sucinout {zero} {x ∷ nn₁} (there kin) rewrite (sucinout{zero}{nn₁} kin) = refl
sucinout {suc k} {[]} ()
sucinout {suc k} {.(suc k) ∷ nn₁} (here refl) = refl
sucinout {suc k} {x ∷ nn₁} (there kin) rewrite (sucinout{(suc k)}{nn₁} kin) = refl

domzero : ∀{m} → zero ∈ (Dom' (nothing ∷ m)) → ⊥
domzero {[]} = λ ()
domzero {x ∷ m} = 0∈S

domin : ∀{x m z} → x ∈ Dom' m → suc x ∈ Dom' (z ∷ m)
domin {x} {m} {just z}  x∈Dom'm = there (sucin x∈Dom'm)
domin {x} {m} {nothing} x∈Dom'm = sucin x∈Dom'm

n∈Sbij : ∀{k x m} → ∀{kin : (suc k) ∈ (Dom' (x ∷ m))} → ∀{kin2 : (suc k) ∈ (Dom' (x ∷ m))} → (n∈S{k}{x}{m} kin) ≡ (n∈S{k}{x}{m} kin2) → kin ≡ kin2
n∈Sbij {k} {just x} {[]} {here ()} {kin2} eq
n∈Sbij {k} {just x} {[]} {there ()} {kin2} eq
n∈Sbij {k} {just x} {x₁ ∷ m} {here ()} {kin2} eq
n∈Sbij {k} {just x} {x₁ ∷ m} {there kin} {here ()} eq
n∈Sbij {k} {just x} {x₁ ∷ m} {there kin} {there kin2} eq with (cong sucin eq)
... | eq2 rewrite (sucinout kin) | (sucinout kin2) =  cong there eq2
n∈Sbij {k} {nothing} {[]} {kin} {()} eq
n∈Sbij {k} {nothing} {x ∷ m} {kin} {kin2} eq with cong sucin eq
... | eq2 rewrite (sucinout kin) | (sucinout kin2) = eq2

ineq : ∀{k m} → (kin1 : k ∈ (Dom' m)) → (kin2 : k ∈ (Dom' m)) → kin1 ≡ kin2
ineq {zero} {[]} () kin2
ineq {zero} {just x ∷ m} (here refl) (here refl) = refl
ineq {zero} {just x ∷ m} (here refl) (there kin2) = ⊥-elim (0∈S kin2)
ineq {zero} {just x ∷ m} (there kin1) (here px) = ⊥-elim (0∈S kin1)
ineq {zero} {just x ∷ m} (there kin1) (there kin2) = ⊥-elim (0∈S kin1)
ineq {zero} {nothing ∷ m} kin1 kin2 = ⊥-elim (domzero{m} kin1)
ineq {suc k} {[]} () kin2
ineq {suc k} {just x ∷ m} (here ()) (here px₁)
ineq {suc k} {just x ∷ m} (here ()) (there kin2)
ineq {suc k} {just x ∷ m} (there kin1) (here ())
ineq {suc k} {just x ∷ m} (there kin1) (there kin2) rewrite sym (sucinout kin1) | sym (sucinout kin2) = cong there (cong sucin (ineq{k}{m} (sucout kin1) (sucout kin2)))
ineq {suc k} {nothing ∷ m} kin1 kin2 = n∈Sbij{k}{nothing}{m} (ineq{k}{m} (n∈S{x = nothing}{l = m} kin1) (n∈S{x = nothing}{l = m} kin2))

Dom'-comm : ∀ m1 m2 → Dom' (m1 U m2) ≡ Dom' (m2 U m1)
Dom'-comm [] m2 rewrite U-comm {m2} {[]} (λ _ _ ()) = refl
Dom'-comm (x ∷ m1) [] = refl
Dom'-comm (just x ∷ m1) (just x₁ ∷ m2) rewrite Dom'-comm m1 m2 = refl
Dom'-comm (just x ∷ m1) (nothing ∷ m2) rewrite Dom'-comm m1 m2 = refl
Dom'-comm (nothing ∷ m1) (just x ∷ m2) rewrite Dom'-comm m1 m2 = refl
Dom'-comm (nothing ∷ m1) (nothing ∷ m2) rewrite Dom'-comm m1 m2 = refl

Dom'-assoc-comm : ∀ m1 m2 m3 → Dom' ((m1 U m2) U m3) ≡ Dom' ((m1 U m3) U m2)
Dom'-assoc-comm [] m2 m3 = Dom'-comm m2 m3
Dom'-assoc-comm (x ∷ m1) [] m3 rewrite Dom'-comm ((x ∷ m1) U m3) [] = refl
Dom'-assoc-comm (x ∷ m1) (x₁ ∷ m2) [] rewrite Dom'-comm ((x ∷ m1) U (x₁ ∷ m2)) [] = refl
Dom'-assoc-comm (just x ∷ m1) (just x₁ ∷ m2) (just x₂ ∷ m3)
  rewrite Dom'-assoc-comm m1 m2 m3 = refl
Dom'-assoc-comm (just x ∷ m1) (just x₁ ∷ m2) (nothing ∷ m3)
  rewrite Dom'-assoc-comm m1 m2 m3 = refl
Dom'-assoc-comm (just x ∷ m1) (nothing ∷ m2) (just x₁ ∷ m3)
  rewrite Dom'-assoc-comm m1 m2 m3 = refl
Dom'-assoc-comm (just x ∷ m1) (nothing ∷ m2) (nothing ∷ m3)
  rewrite Dom'-assoc-comm m1 m2 m3 = refl
Dom'-assoc-comm (nothing ∷ m1) (just x ∷ m2) (just x₁ ∷ m3)
  rewrite Dom'-assoc-comm m1 m2 m3 = refl
Dom'-assoc-comm (nothing ∷ m1) (just x ∷ m2) (nothing ∷ m3)
  rewrite Dom'-assoc-comm m1 m2 m3 = refl
Dom'-assoc-comm (nothing ∷ m1) (nothing ∷ m2) (just x ∷ m3)
  rewrite Dom'-assoc-comm m1 m2 m3 = refl
Dom'-assoc-comm (nothing ∷ m1) (nothing ∷ m2) (nothing ∷ m3)
  rewrite Dom'-assoc-comm m1 m2 m3 = refl

putputget-neq : ∀{k k' m v v'}
                → ¬ (k ≡ k')
                → (kin : k ∈ (Dom' m))
                → (kin2 : k ∈ (Dom' (m-insert (just v') k' m)))
                → (deref k m kin) ≡ v
                → (deref k (m-insert (just v') k' m) kin2) ≡ v
putputget-neq {k} {k'} {[]} neq () kin2 eq
putputget-neq {.0} {zero} {just x ∷ m} neq (here refl) (here refl) refl = ⊥-elim (neq refl)
putputget-neq {.0} {zero} {just x ∷ m} neq (here refl) (there kin2) refl = ⊥-elim (neq refl)
putputget-neq {.0} {suc k'} {just x ∷ m} neq (here refl) (here refl) refl = refl
putputget-neq {.0} {suc k'} {just x ∷ m} neq (here refl) (there kin2) refl = refl
putputget-neq {zero} {zero} {just x ∷ m} neq (there kin) kin2 refl = ⊥-elim (neq refl)

putputget-neq {zero} {suc k'} {just x ∷ m} neq (there kin) kin2 refl = refl
putputget-neq {suc k} {suc k'} {just x ∷ m} neq (there kin) (here ()) refl
putputget-neq {zero} {zero} {nothing ∷ m} neq kin kin2 refl = ⊥-elim (neq refl)

putputget-neq {zero} {suc k'} {nothing ∷ m} neq kin kin2 refl = ⊥-elim (0∈S kin)
putputget-neq {suc k} {zero} {nothing ∷ m} neq kin (here ()) refl

putputget-neq {suc k} {suc k'} {just x ∷ m} {v} {v'} neq (there kin) (there kin2) refl
  rewrite ineq{k}{m-insert (just v') k' m} (n∈S{k}{just x}{m-insert (just v') k' m} (there kin2)) (sucout kin2)
     =  putputget-neq{k}{k'}{m}{v}{v'} (negsucun neq) (sucout kin) (sucout kin2) (deref-∈-irr{k}{m} (sucout kin) (n∈S{k}{x = just x}{m} (there kin))) 
putputget-neq {suc k} {suc k'} {nothing ∷ m} {v} {v'} neq kin kin2 refl
  rewrite ineq{k}{m-insert (just v') k' m} (n∈S{k}{nothing}{m-insert (just v') k' m} kin2) (sucout kin2)
    = putputget-neq{k}{k'}{m} (negsucun neq) (sucout kin) ((sucout kin2)) ((deref-∈-irr{k}{m} (sucout kin) (n∈S{k}{x = nothing}{m} kin)))

putputget-neq {suc k} {zero} {x ∷ m} {v} {v'} neq kin kin2 refl =  deref-∈-irr{k}{m} (n∈S{k}{just v'}{m} kin2) (n∈S{k}{x}{m} kin) 

putputget-eq : ∀ k m v v' →
               (m-insert (just v') k (m-insert (just v) k m))
                ≡ (m-insert (just v') k m)
putputget-eq zero [] v v' = refl
putputget-eq zero (x ∷ m) v v' = refl
putputget-eq (suc k) [] v v' rewrite putputget-eq k [] v v' = refl
putputget-eq (suc k) (x ∷ m) v v'  rewrite putputget-eq k m v v' = refl

getput : ∀ k m →
  (kin : k ∈ Dom' m) →
  m ≡ m-insert (just (deref k m kin)) k m
getput k [] ()
getput zero    (just x ∷ m)  kin = refl
getput zero    (nothing ∷ m) kin = ⊥-elim (0∈S kin)
getput (suc k) (just x ∷ m)  kin
  rewrite sym (getput k m (n∈S {k} {just x} {m} kin))
  = refl
getput (suc k) (nothing ∷ m) kin
  rewrite sym (getput k m (n∈S {k} {nothing} {m} kin))
  = refl

putget : ∀{k m v} → (kin : k ∈ (Dom' (m-insert (just v) k m))) → (deref k (m-insert (just v) k m) kin) ≡ v
putget {zero} {[]} {v} (here refl) = refl
putget {zero} {[]} {v} (there ())
putget {zero} {just x ∷ m} {v} (here refl) = refl
putget {zero} {just x ∷ m} {v} (there kin) = refl
putget {zero} {nothing ∷ m} {v} kin = refl
putget {suc k} {[]} {v} kin = putget{k}{[]}{v} ( (n∈S{k}{nothing}{(m-insert (just v) k [])} kin) )
putget {suc k} {x ∷ m} {v} kin = putget{k}{m}{v} ( (n∈S{k}{x} kin) )

put-U-U : ∀ k v m1 m2 →
  (kin1 : k ∈ Dom' m1) →
  (kin2 : k ∈ Dom' m2) →
    m1 U m2 ≡
    (m-insert (just v) k m1) U m2
put-U-U k v [] m2 () kin2
put-U-U k v (x ∷ m1) [] kin1 ()
put-U-U zero v (just x ∷ m1) (just x₁ ∷ m2) kin1 kin2 = refl
put-U-U zero v (just x ∷ m1) (nothing ∷ m2) kin1 kin2 = ⊥-elim (0∈S kin2)
put-U-U zero v (nothing ∷ m1) (x₁ ∷ m2) kin1 kin2 = ⊥-elim (0∈S kin1)
put-U-U (suc k) v (just x ∷ m1) (just x₁ ∷ m2) kin1 kin2
  rewrite put-U-U k v m1 m2
                  (n∈S {k} {just x}  {m1} kin1)
                  (n∈S {k} {just x₁} {m2} kin2)
  = refl
put-U-U (suc k) v (just x ∷ m1) (nothing ∷ m2) kin1 kin2
  rewrite put-U-U k v m1 m2
                  (n∈S {k} {just x}  {m1} kin1)
                  (n∈S {k} {nothing} {m2} kin2)
  = refl
put-U-U (suc k) v (nothing ∷ m1) (just x ∷ m2) kin1 kin2
  rewrite put-U-U k v m1 m2
                  (n∈S {k} {nothing} {m1} kin1)
                  (n∈S {k} {just x}  {m2} kin2)
  = refl
put-U-U (suc k) v (nothing ∷ m1) (nothing ∷ m2) kin1 kin2
  rewrite put-U-U k v m1 m2
                  (n∈S {k} {nothing} {m1} kin1)
                  (n∈S {k} {nothing} {m2} kin2)
  = refl

insert-comm : ∀{m k1 k2 v1 v2}
              → ¬ k1 ≡ k2
              → (m-insert (just v2) k2 (m-insert (just v1) k1 m)) ≡ (m-insert (just v1) k1 (m-insert (just v2) k2 m))
insert-comm {m} {zero} {zero} {v1} {v2} ¬k1≡k2 = ⊥-elim (¬k1≡k2 refl)
insert-comm {[]} {zero} {suc k2} {v1} {v2} ¬k1≡k2 = refl
insert-comm {x ∷ m} {zero} {suc k2} {v1} {v2} ¬k1≡k2 = refl
insert-comm {[]} {suc k1} {zero} {v1} {v2} ¬k1≡k2 = refl
insert-comm {x ∷ m} {suc k1} {zero} {v1} {v2} ¬k1≡k2 = refl
insert-comm {[]} {suc k1} {suc k2} {v1} {v2} ¬k1≡k2 rewrite insert-comm{[]}{k1}{k2}{v1}{v2} (λ x → ¬k1≡k2 (cong suc x)) = refl
insert-comm {x ∷ m} {suc k1} {suc k2} {v1} {v2} ¬k1≡k2 rewrite insert-comm{m}{k1}{k2}{v1}{v2} (λ x → ¬k1≡k2 (cong suc x)) = refl

insert-U-comm : ∀ k v m m' →
  ¬ (k ∈ Dom' m') →
    (m-insert (just v) k m) U m' ≡
    m-insert (just v) k (m U m')
insert-U-comm k v m [] k∉Domm'
  rewrite U-comm {m} {[]} (λ _ _ ())
        | U-comm {m-insert (just v) k m} {[]} (λ _ _ ())
  = refl
insert-U-comm zero v [] (just x ∷ m') k∉Domm' = ⊥-elim (k∉Domm' (here refl))
insert-U-comm zero v [] (nothing ∷ m') k∉Domm' = refl
insert-U-comm (suc k) v [] (just x ∷ m') k∉Domm'
  rewrite insert-U-comm k v [] m' (k∉Domm' ∘ there ∘ sucin {k} {Dom' m'})
  = refl
insert-U-comm (suc k) v [] (nothing ∷ m') k∉Domm'
  rewrite insert-U-comm k v [] m' (k∉Domm' ∘ sucin {k} {Dom' m'})
  = refl
insert-U-comm zero v (x ∷ m) (just x₁ ∷ m') k∉Domm' = ⊥-elim (k∉Domm' (here refl))
insert-U-comm zero v (just x ∷ m)  (nothing ∷ m') k∉Domm' = refl
insert-U-comm zero v (nothing ∷ m) (nothing ∷ m') k∉Domm' = refl
insert-U-comm (suc k) v (just x ∷ m)  (just x₁ ∷ m') k∉Domm'
  rewrite insert-U-comm k v m m' (k∉Domm' ∘ there ∘ sucin {k} {Dom' m'})
  = refl
insert-U-comm (suc k) v (nothing ∷ m) (just x₁ ∷ m') k∉Domm'
  rewrite insert-U-comm k v m m' (k∉Domm' ∘ there ∘ sucin {k} {Dom' m'})
  = refl
insert-U-comm (suc k) v (just x ∷ m)  (nothing ∷ m') k∉Domm'
  rewrite insert-U-comm k v m m' (k∉Domm' ∘ sucin {k} {Dom' m'})
  = refl
insert-U-comm (suc k) v (nothing ∷ m) (nothing ∷ m') k∉Domm'
  rewrite insert-U-comm k v m m' (k∉Domm' ∘ sucin {k} {Dom' m'})
  = refl

deref-U-right-irr : ∀ k m1 m2 kin12 kin2 →
  deref k (m1 U m2) kin12 ≡ deref k m2 kin2
deref-U-right-irr k m1 [] kin12 ()
deref-U-right-irr zero [] (x ∷ m2) kin12 kin2 = deref-∈-irr {l = x ∷ m2} kin12 kin2
deref-U-right-irr zero (just x ∷ m1)  (just x₁ ∷ m2) kin12 kin2 = refl
deref-U-right-irr zero (nothing ∷ m1) (just x ∷ m2)  kin12 kin2 = refl
deref-U-right-irr zero (x ∷ m1)       (nothing ∷ m2) kin12 kin2 = ⊥-elim (0∈S kin2)
deref-U-right-irr (suc k) [] (x ∷ m2) kin12 kin2 =
  deref-∈-irr {l = m2} (n∈S {k} {x} kin12) (n∈S {k} {x} kin2)
deref-U-right-irr (suc k) (just x ∷ m1)  (just x₁ ∷ m2) kin12 kin2 =
  deref-U-right-irr k m1 m2
    (n∈S {k} {just x₁} {m1 U m2} kin12) (n∈S {k} {just x₁} {m2} kin2)
deref-U-right-irr (suc k) (nothing ∷ m1) (just x₁ ∷ m2) kin12 kin2 =
  deref-U-right-irr k m1 m2
    (n∈S {k} {just x₁} {m1 U m2} kin12) (n∈S {k} {just x₁} {m2} kin2)
deref-U-right-irr (suc k) (just x ∷ m1)  (nothing ∷ m2) kin12 kin2 =
  deref-U-right-irr k m1 m2
    (n∈S {k} {just x} {m1 U m2} kin12) (n∈S {k} {nothing} {m2} kin2)
deref-U-right-irr (suc k) (nothing ∷ m1) (nothing ∷ m2) kin12 kin2 =
  deref-U-right-irr k m1 m2
    (n∈S {k} {nothing} {m1 U m2} kin12) (n∈S {k} {nothing} {m2} kin2)

∈-deref-U-irr : ∀ k m1 m2 m3 kin1 kin2 →
  (kin3 : k ∈ Dom' m3) →
  deref k (m1 U m3) kin1 ≡ deref k (m2 U m3) kin2
∈-deref-U-irr k [] m2 m3 kin1 kin2 kin3
  rewrite deref-U-right-irr k m2 m3 kin2 kin3
  = deref-∈-irr kin1 kin3
∈-deref-U-irr k (x ∷ m1) [] m3 kin1 kin2 kin3
  rewrite deref-U-right-irr k (x ∷ m1) m3 kin1 kin3
  = deref-∈-irr kin3 kin2
∈-deref-U-irr k (x ∷ m1) (x₁ ∷ m2) [] kin1 kin2 ()
∈-deref-U-irr zero (x ∷ m1) (x₁ ∷ m2) (nothing ∷ m3) kin1 kin2 kin3 = ⊥-elim (0∈S kin3)
∈-deref-U-irr zero (just x ∷ m1)  (just x₁ ∷ m2) (just x₂ ∷ m3) kin1 kin2 kin3 = refl
∈-deref-U-irr zero (just x ∷ m1)  (nothing ∷ m2) (just x₂ ∷ m3) kin1 kin2 kin3 = refl
∈-deref-U-irr zero (nothing ∷ m1) (just x₁ ∷ m2) (just x₂ ∷ m3) kin1 kin2 kin3 = refl
∈-deref-U-irr zero (nothing ∷ m1) (nothing ∷ m2) (just x₂ ∷ m3) kin1 kin2 kin3 = refl
∈-deref-U-irr (suc k) (just x ∷ m1) (just x₁ ∷ m2) (just x₂ ∷ m3) kin1 kin2 kin3 =
  ∈-deref-U-irr k m1 m2 m3
    (n∈S {k} {just x₂} {m1 U m3} kin1)
    (n∈S {k} {just x₂} {m2 U m3} kin2)
    (n∈S {k} {just x₂} {m3} kin3)
∈-deref-U-irr (suc k) (just x ∷ m1) (nothing ∷ m2) (just x₂ ∷ m3) kin1 kin2 kin3 =
  ∈-deref-U-irr k m1 m2 m3
    (n∈S {k} {just x₂} {m1 U m3} kin1)
    (n∈S {k} {just x₂} {m2 U m3} kin2)
    (n∈S {k} {just x₂} {m3} kin3)
∈-deref-U-irr (suc k) (nothing ∷ m1) (just x₁ ∷ m2) (just x₂ ∷ m3) kin1 kin2 kin3 =
  ∈-deref-U-irr k m1 m2 m3
    (n∈S {k} {just x₂} {m1 U m3} kin1)
    (n∈S {k} {just x₂} {m2 U m3} kin2)
    (n∈S {k} {just x₂} {m3} kin3)
∈-deref-U-irr (suc k) (nothing ∷ m1) (nothing ∷ m2) (just x₂ ∷ m3) kin1 kin2 kin3 =
  ∈-deref-U-irr k m1 m2 m3
    (n∈S {k} {just x₂} {m1 U m3} kin1)
    (n∈S {k} {just x₂} {m2 U m3} kin2)
    (n∈S {k} {just x₂} {m3} kin3)
∈-deref-U-irr (suc k) (just x ∷ m1) (just x₁ ∷ m2) (nothing ∷ m3) kin1 kin2 kin3 =
  ∈-deref-U-irr k m1 m2 m3
    (n∈S {k} {just x} {m1 U m3} kin1)
    (n∈S {k} {just x₁} {m2 U m3} kin2)
    (n∈S {k} {nothing} {m3} kin3)
∈-deref-U-irr (suc k) (just x ∷ m1) (nothing ∷ m2) (nothing ∷ m3) kin1 kin2 kin3 =
  ∈-deref-U-irr k m1 m2 m3
    (n∈S {k} {just x} {m1 U m3} kin1)
    (n∈S {k} {nothing} {m2 U m3} kin2)
    (n∈S {k} {nothing} {m3} kin3)
∈-deref-U-irr (suc k) (nothing ∷ m1) (just x₁ ∷ m2) (nothing ∷ m3) kin1 kin2 kin3 =
  ∈-deref-U-irr k m1 m2 m3
    (n∈S {k} {nothing} {m1 U m3} kin1)
    (n∈S {k} {just x₁} {m2 U m3} kin2)
    (n∈S {k} {nothing} {m3} kin3)
∈-deref-U-irr (suc k) (nothing ∷ m1) (nothing ∷ m2) (nothing ∷ m3) kin1 kin2 kin3 =
  ∈-deref-U-irr k m1 m2 m3
    (n∈S {k} {nothing} {m1 U m3} kin1)
    (n∈S {k} {nothing} {m2 U m3} kin2)
    (n∈S {k} {nothing} {m3} kin3)

deref-U-both-irr : ∀ k m1 m2 m3 kin1 kin2 kin13 kin23 →
  deref k m1 kin1 ≡ deref k m2 kin2 →
  deref k (m1 U m3) kin13 ≡ deref k (m2 U m3) kin23
deref-U-both-irr k [] m2 m3 () kin2 kin13 kin23 m1[k]≡m2[k]
deref-U-both-irr k (x ∷ m1) [] m3 kin1 () kin13 kin23 m1[k]≡m2[k]
deref-U-both-irr k (x ∷ m1) (x₁ ∷ m2) [] kin1 kin2 kin13 kin23 m1[k]≡m2[k]
  rewrite deref-∈-irr {l = x ∷ m1} kin13 kin1 | deref-∈-irr {l = x₁ ∷ m2} kin23 kin2
  = m1[k]≡m2[k]
deref-U-both-irr zero (just x ∷ m1)  (just x₁ ∷ m2) (nothing ∷ m3) _ _ _ _ m1[k]≡m2[k] = m1[k]≡m2[k]
deref-U-both-irr zero (just x ∷ m1)  (just x₁ ∷ m2) (just x₂ ∷ m3) _    _ _ _ _ = refl
deref-U-both-irr zero (just x ∷ m1)  (nothing ∷ m2) (just x₂ ∷ m3) _    _ _ _ _ = refl
deref-U-both-irr zero (nothing ∷ m1) (just x ∷ m2)  (just x₂ ∷ m3) _    _ _ _ _ = refl
deref-U-both-irr zero (nothing ∷ m1) (nothing ∷ m2) (just x₂ ∷ m3) _    _ _ _ _ = refl
deref-U-both-irr zero (nothing ∷ m1) (just x ∷ m2)  (nothing ∷ m3) kin1 _ _ _ _ = ⊥-elim (0∈S kin1)
deref-U-both-irr zero (nothing ∷ m1) (nothing ∷ m2) (nothing ∷ m3) kin1 _ _ _ _ = ⊥-elim (0∈S kin1)
deref-U-both-irr zero (just x ∷ m1)  (nothing ∷ m2) (nothing ∷ m3) _ kin2 _ _ _ = ⊥-elim (0∈S kin2)
deref-U-both-irr (suc k) (just x ∷ m1) (just x₁ ∷ m2) (just x₂ ∷ m3)
               kin1 kin2 kin13 kin23 m1[k]≡m2[k] =
  deref-U-both-irr k m1 m2 m3
    (n∈S {k} {just x} {m1} kin1) (n∈S {k} {just x₁} {m2} kin2)
    (n∈S {k} {just x₂} {m1 U m3} kin13) (n∈S {k} {just x₂} {m2 U m3} kin23)
    m1[k]≡m2[k]
deref-U-both-irr (suc k) (just x ∷ m1) (nothing ∷ m2) (just x₂ ∷ m3)
               kin1 kin2 kin13 kin23 m1[k]≡m2[k] =
  deref-U-both-irr k m1 m2 m3
    (n∈S {k} {just x} {m1} kin1) (n∈S {k} {nothing} {m2} kin2)
    (n∈S {k} {just x₂} {m1 U m3} kin13) (n∈S {k} {just x₂} {m2 U m3} kin23)
    m1[k]≡m2[k]
deref-U-both-irr (suc k) (nothing ∷ m1) (just x ∷ m2) (just x₂ ∷ m3)
               kin1 kin2 kin13 kin23 m1[k]≡m2[k] =
  deref-U-both-irr k m1 m2 m3
    (n∈S {k} {nothing} {m1} kin1) (n∈S {k} {just x} {m2} kin2)
    (n∈S {k} {just x₂} {m1 U m3} kin13) (n∈S {k} {just x₂} {m2 U m3} kin23)
    m1[k]≡m2[k]
deref-U-both-irr (suc k) (nothing ∷ m1) (nothing ∷ m2) (just x₂ ∷ m3)
               kin1 kin2 kin13 kin23 m1[k]≡m2[k] =
  deref-U-both-irr k m1 m2 m3
    (n∈S {k} {nothing} {m1} kin1) (n∈S {k} {nothing} {m2} kin2)
    (n∈S {k} {just x₂} {m1 U m3} kin13) (n∈S {k} {just x₂} {m2 U m3} kin23)
    m1[k]≡m2[k]
deref-U-both-irr (suc k) (just x ∷ m1) (just x₁ ∷ m2) (nothing ∷ m3)
               kin1 kin2 kin13 kin23 m1[k]≡m2[k] =
  deref-U-both-irr k m1 m2 m3
    (n∈S {k} {just x} {m1} kin1) (n∈S {k} {just x₁} {m2} kin2)
    (n∈S {k} {just x} {m1 U m3} kin13) (n∈S {k} {just x₁} {m2 U m3} kin23)
    m1[k]≡m2[k]
deref-U-both-irr (suc k) (just x ∷ m1) (nothing ∷ m2) (nothing ∷ m3)
               kin1 kin2 kin13 kin23 m1[k]≡m2[k] =
  deref-U-both-irr k m1 m2 m3
    (n∈S {k} {just x} {m1} kin1) (n∈S {k} {nothing} {m2} kin2)
    (n∈S {k} {just x} {m1 U m3} kin13) (n∈S {k} {nothing} {m2 U m3} kin23)
    m1[k]≡m2[k]
deref-U-both-irr (suc k) (nothing ∷ m1) (just x ∷ m2) (nothing ∷ m3)
               kin1 kin2 kin13 kin23 m1[k]≡m2[k] =
  deref-U-both-irr k m1 m2 m3
    (n∈S {k} {nothing} {m1} kin1) (n∈S {k} {just x} {m2} kin2)
    (n∈S {k} {nothing} {m1 U m3} kin13) (n∈S {k} {just x} {m2 U m3} kin23)
    m1[k]≡m2[k]
deref-U-both-irr (suc k) (nothing ∷ m1) (nothing ∷ m2) (nothing ∷ m3)
               kin1 kin2 kin13 kin23 m1[k]≡m2[k] =
  deref-U-both-irr k m1 m2 m3
    (n∈S {k} {nothing} {m1} kin1) (n∈S {k} {nothing} {m2} kin2)
    (n∈S {k} {nothing} {m1 U m3} kin13) (n∈S {k} {nothing} {m2 U m3} kin23)
    m1[k]≡m2[k]

U-domout : ∀ {k m₁ m₂} x x₁ → suc k ∈ Dom' ((x ∷ m₁) U (x₁ ∷ m₂)) → k ∈ Dom' (m₁ U m₂)
U-domout (just x₂) (just x₃) (here ())
U-domout (just x₂) (just x₃) (there suck∈'') = sucout suck∈''
U-domout (just x₂) nothing (here ())
U-domout (just x₂) nothing (there suck∈'') = sucout suck∈''
U-domout nothing (just x₂) (here ())
U-domout nothing (just x₂) (there suck∈'') = sucout suck∈''
U-domout nothing   nothing   suck∈'' = sucout suck∈''

U-∉-irr-get-help-help : ∀ k x x₁ m₁ m₂ →
  (k∈ : suc k ∈ Dom' ((x ∷ m₁) U (x₁ ∷ m₂))) →
  deref (suc k) ((x ∷ m₁) U (x₁ ∷ m₂)) k∈ ≡
    deref k (m₁ U m₂) (U-domout x x₁ k∈)
U-∉-irr-get-help-help k (just x) (just x₁) m₁ m₂ (here ())
U-∉-irr-get-help-help k (just x) (just x₁) m₁ m₂ (there k∈) = deref-∈-irr {k} {m₁ U m₂} (n∈S {k} {just x₁} {m₁ U m₂} (there k∈)) (sucout k∈)
U-∉-irr-get-help-help k (just x) nothing m₁ m₂ (here ())
U-∉-irr-get-help-help k (just x) nothing m₁ m₂ (there k∈) = deref-∈-irr {k} {m₁ U m₂} (n∈S {k} {just x} {m₁ U m₂} (there k∈)) (sucout k∈)
U-∉-irr-get-help-help k nothing (just x) m₁ m₂ (here ())
U-∉-irr-get-help-help k nothing (just x) m₁ m₂ (there k∈) = deref-∈-irr {k} {m₁ U m₂} (n∈S {k} {just x} {m₁ U m₂} (there k∈)) (sucout k∈)
U-∉-irr-get-help-help k nothing nothing m₁ m₂ k∈ =  deref-∈-irr {k} {m₁ U m₂} (n∈S {k} {nothing} {m₁ U m₂} k∈) (sucout k∈)

U-∉-irr-get-help : ∀ {m₁ m₂ k} → (k∈ : k ∈ Dom' m₁) → k ∉ Dom' m₂ → (k∈' : k ∈ Dom' (m₁ U m₂))  → deref k m₁ k∈ ≡ deref k (m₁ U m₂) k∈'
U-∉-irr-get-help {[]} {[]} {k} () k∉Dom⟨m₂⟩ k∈Dom⟨m₁Um₂⟩
U-∉-irr-get-help {[]} {x ∷ m₂} {k} () k∉Dom⟨m₂⟩ k∈Dom⟨m₁Um₂⟩
U-∉-irr-get-help {x ∷ m₁} {[]}      {k} k∈Dom⟨m₁⟩ k∉Dom⟨m₂⟩ k∈Dom⟨m₁Um₂⟩
  rewrite deref-∈-irr {k} {x ∷ m₁} k∈Dom⟨m₁⟩ k∈Dom⟨m₁Um₂⟩ = refl
U-∉-irr-get-help {x ∷ m₁} {just x₁ ∷ m₂} {zero} k∈Dom⟨m₁⟩ k∉Dom⟨m₂⟩ k∈Dom⟨m₁Um₂⟩ = ⊥-elim (k∉Dom⟨m₂⟩ (here refl))
U-∉-irr-get-help {just x ∷ m₁}  {nothing ∷ m₂} {zero} k∈Dom⟨m₁⟩ k∉Dom⟨m₂⟩ k∈Dom⟨m₁Um₂⟩ = refl
U-∉-irr-get-help {nothing ∷ m₁} {nothing ∷ m₂} {zero} k∈Dom⟨m₁⟩ k∉Dom⟨m₂⟩ k∈Dom⟨m₁Um₂⟩ = ⊥-elim (0∈S k∈Dom⟨m₁⟩)
U-∉-irr-get-help {x ∷ m₁} {x₁ ∷ m₂} {suc k} k∈Dom⟨m₁⟩ k∉Dom⟨m₂⟩ k∈Dom⟨m₁Um₂⟩
  with U-∉-irr-get-help {m₁} {m₂} {k} (n∈S {k} {x} k∈Dom⟨m₁⟩) (λ x₂ → k∉Dom⟨m₂⟩ (domin {k} {m₂} {x₁} x₂)) (U-domout x x₁ k∈Dom⟨m₁Um₂⟩)
... | eq rewrite U-∉-irr-get-help-help k x x₁ m₁ m₂ k∈Dom⟨m₁Um₂⟩ = eq

U-∉-irr-get : ∀ {m₁ m₂ k} → (k∈ : k ∈ Dom' m₁) → k ∉ Dom' m₂ → ∃ λ k∈' → deref k m₁ k∈ ≡ deref k (m₁ U m₂) k∈'
U-∉-irr-get {m₁} {m₂} {k} k∈Dom'm₁ k∉Dom'm₂ =
  _ , U-∉-irr-get-help {m₁} {m₂} {k} k∈Dom'm₁ k∉Dom'm₂ (U-mono {m₁} {m₂} k∈Dom'm₁)


split : ∀{a b : ℕ} {l l'} → a ∷ l ≡ b ∷ l' → ((_≡_ a b) × (_≡_ l l'))
split refl = refl , refl

mapsuc≡ : ∀{l l'} → map suc l ≡ map suc l' → l ≡ l'
mapsuc≡ {[]} {[]} eq = refl
mapsuc≡ {[]} {x ∷ l'} ()
mapsuc≡ {x ∷ l} {[]} ()
mapsuc≡ {x ∷ l} {x₁ ∷ l'} eq with split eq
... | (a , b) rewrite (suc≡ a) | (mapsuc≡ b) = refl

U-=-irr : ∀ m m' → (Dom' m) ≡ (Dom' m') → ∀ k k∈ k∈2 → deref k (m U m') k∈ ≡ deref k m' k∈2
U-=-irr [] [] eq k ()
U-=-irr [] (nothing ∷ m') eq k x  with (subst (λ l → k ∈ l) (sym eq) x)
... | ()
U-=-irr [] (just x ∷ m') ()
U-=-irr (just x ∷ m) [] ()
U-=-irr (nothing ∷ m) [] eq k k∈ ()
U-=-irr (just x ∷ m) (nothing ∷ m') eq = ⊥-elim (0∈S{Dom' m'} (subst (λ x → 0 ∈ x) eq ((0 ∈ (0 ∷ (map suc (Dom' m)))) ∋ (here refl))))
U-=-irr (nothing ∷ m) (just x ∷ m') eq = ⊥-elim (0∈S{Dom' m} (subst (λ x → 0 ∈ x) (sym eq) ((0 ∈ (0 ∷ (map suc (Dom' m')))) ∋ (here refl))))
U-=-irr (nothing ∷ m) (nothing ∷ m') eq zero k∈ k∈2 = ⊥-elim (0∈S k∈)
U-=-irr (nothing ∷ m) (nothing ∷ m') eq (suc k) k∈ k∈2 = U-=-irr m m' (mapsuc≡ eq) k (n∈S{k}{nothing}{m U m'} k∈) (n∈S{k}{nothing}{m'} k∈2)
U-=-irr (just x ∷ m) (just x₁ ∷ m') eq zero = λ k∈ k∈2 → refl
U-=-irr (just x ∷ m) (just x₁ ∷ m') eq (suc k) k∈ k∈2 = U-=-irr m m' ((mapsuc≡ (proj₂ (split eq)))) k (n∈S{k}{just x₁}{m U m'} k∈) (n∈S{k}{just x₁}{m'} k∈2)



U-single-overwrite : ∀ k v1 v2 → (m-insert (just v1) k [])  U  (m-insert (just v2) k []) ≡ (m-insert (just v2) k [])
U-single-overwrite zero v1 v2 = refl
U-single-overwrite (suc k) v1 v2 rewrite U-single-overwrite k v1 v2 = refl

set-single-val : ∀ k v k∈ → (deref k (m-insert (just v) k []) k∈) ≡ v 
set-single-val zero v (here refl) = refl
set-single-val zero v (there ())
set-single-val (suc k) v k∈ = set-single-val k v (n∈S{k}{nothing}{(m-insert (just v) k [])} k∈)

overwrite-single-val : ∀ k v m → k ∈ (Dom' m) → ((m-insert (just v) k []) U m) ≡ m
overwrite-single-val zero v [] ()
overwrite-single-val zero v (just x ∷ m) k∈ = refl
overwrite-single-val zero v (nothing ∷ m) k∈ = ⊥-elim (0∈S k∈)
overwrite-single-val (suc k) v [] ()
overwrite-single-val (suc k) v (just x ∷ m) (here ())
overwrite-single-val (suc k) v (just x ∷ m) (there k∈) rewrite overwrite-single-val k v m (sucout k∈) = refl
overwrite-single-val (suc k) v (nothing ∷ m) k∈ rewrite overwrite-single-val k v m (sucout k∈) = refl

U-insert-eq : ∀ k v m → (m-insert (just v) k m) ≡ m U (m-insert (just v) k [])
U-insert-eq zero v [] = refl
U-insert-eq zero v (just x ∷ m) rewrite U-comm{m}{[]} (λ z _ → λ ()) = refl
U-insert-eq zero v (nothing ∷ m) rewrite U-comm{m}{[]} (λ z _ → λ ()) = refl
U-insert-eq (suc k) v [] = refl
U-insert-eq (suc k) v (just x ∷ m) rewrite U-insert-eq k v m = refl
U-insert-eq (suc k) v (nothing ∷ m) rewrite U-insert-eq k v m = refl

insert-domain-eq : ∀ k v m → k ∈ (Dom' m) → (Dom' m) ≡ (Dom' (m-insert (just v) k m))
insert-domain-eq zero v [] ()
insert-domain-eq zero v (just x ∷ m) k∈ = refl
insert-domain-eq zero v (nothing ∷ m) k∈ = ⊥-elim (0∈S k∈)
insert-domain-eq (suc k) v [] ()
insert-domain-eq (suc k) v (just x ∷ m) (here ())
insert-domain-eq (suc k) v (just x ∷ m) (there k∈) rewrite insert-domain-eq k v m (sucout k∈) = refl
insert-domain-eq (suc k) v (nothing ∷ m) k∈ rewrite insert-domain-eq k v m (sucout k∈) = refl

insert-in-domain : ∀ m k v → k ∈ (Dom' (m-insert (just v) k m))
insert-in-domain [] zero v = here refl
insert-in-domain (x ∷ m) zero v = here refl
insert-in-domain [] (suc k) v = sucin (insert-in-domain [] k v)
insert-in-domain (x ∷ m) (suc k) v = domin{z = x} (insert-in-domain m k v)

insert-one-eq : ∀ k v k∈ → (deref k (m-insert (just v) k []) k∈) ≡ v
insert-one-eq zero v k∈ = refl
insert-one-eq (suc k) v k∈ = insert-one-eq k v (n∈S{k}{nothing}{(m-insert (just v) k [])} k∈)

insert-two-eq-one : ∀ k1 k2 v k1∈ → (deref k1 (m-insert (just v) k2 (m-insert (just v) k1 [])) k1∈) ≡ v
insert-two-eq-one zero zero v k1∈ = refl
insert-two-eq-one zero (suc k2) v k1∈ = refl
insert-two-eq-one (suc k1) zero v k1∈
  = insert-one-eq k1 v ( (n∈S{k1}{just v}{l = (m-insert (just v) k1 [])} k1∈) )
insert-two-eq-one (suc k1) (suc k2) v k1∈
     = insert-two-eq-one k1 k2 v ( (n∈S{k1}{nothing}{(m-insert (just v) k2 (m-insert (just v) k1 []))} k1∈))

insert-two-eq-two : ∀ k1 k2 v k2∈ → (deref k2 (m-insert (just v) k2 (m-insert (just v) k1 [])) k2∈) ≡ v
insert-two-eq-two zero zero v k2∈ = refl
insert-two-eq-two zero (suc k2) v k2∈
  = insert-one-eq k2 v ( (n∈S{k2}{just v}{l = (m-insert (just v) k2 [])} k2∈) )
insert-two-eq-two (suc k1) zero v k2∈ = refl
insert-two-eq-two (suc k1) (suc k2) v k2∈
     = insert-two-eq-two k1 k2 v ( (n∈S{k2}{nothing}{(m-insert (just v) k2 (m-insert (just v) k1 []))} k2∈))


data AllMap {i} (F : Value → Set i) : LMap → Set i where
  all : ∀ (m : LMap) → All (Data.Maybe.All F) m → AllMap F m

allMap : ∀ {i} m → {F : Value → Set i} → U.Decidable F → Dec (AllMap F m)
allMap m {F} dec with All.all (Data.Maybe.allDec dec)  m
allMap m {F} dec | yes p = yes (all m p)
allMap m {F} dec | no ¬p = no (λ { (all _ x) → ¬p x})

-- All.all (Data.Maybe.allDec F) m

deref∈ : ∀ {m} → (n : ℕ) → (n∈ : n ∈ (Dom' m)) → just (deref n m n∈) ∈ m
deref∈ {[]} zero ()
deref∈ {[]} (suc n) ()
deref∈ {just x ∷ m} zero n∈ = here refl
deref∈ {nothing ∷ m} zero n∈ = ⊥-elim (0∈S n∈)
deref∈ {just x ∷ m} (suc n) n∈ = there (deref∈ n (n∈S{n}{just x}{m} n∈))
deref∈ {nothing ∷ m} (suc n) n∈ = there (deref∈ n (n∈S{n}{nothing}{m} n∈))

allMap-lookup : ∀ {i} {F : Value → Set i} {m} → AllMap F m → ∀ (n : ℕ) → (k∈ : n ∈ (Dom' m)) → (F (deref n m k∈ ))
allMap-lookup {i} {F} (all m x) n n∈ with (All.lookup x) {just (deref n m n∈)} (deref∈ n n∈)
allMap-lookup {i} {F} (all m x) n n∈ | just px = px

allMap-tabulate : ∀ {i} {F : Value → Set i} {m} → (∀ (n : ℕ) → (k∈ : n ∈ (Dom' m)) → (F (deref n m k∈ ))) → AllMap F m
allMap-tabulate {m = []} FF = all [] All.[]
allMap-tabulate {F = F} {m = just x ∷ m} FF
   with allMap-tabulate{F = F} {m = m} (λ n k∈ →  subst F (deref-∈-irr (n∈S{n}{just x}{m} (there (sucin k∈))) k∈) (FF (suc n) (n+1∈S{n}{just x}{m} k∈)))
allMap-tabulate {_} {F} {just x ∷ m} FF | all .m x₁ = all (just x ∷ m) ((just (FF 0 (here refl))) All.∷ x₁)
allMap-tabulate {F = F} {m = nothing ∷ m} FF
   with allMap-tabulate {m = m} (λ n k∈ →  subst F (deref-∈-irr (n∈S{n}{nothing}{m} (sucin k∈)) k∈) (FF (suc n) (n+1∈S{n}{nothing}{m} k∈)) )
allMap-tabulate {_} {_} {nothing ∷ m} FF | all .m x = all (nothing ∷ m) (nothing All.∷ x)

andmap : ∀ {i} {F : Value → Set i} → U.Decidable F → (m : LMap) → Dec ∀ (n : ℕ) → (n∈ : n ∈ (Dom' m)) → (F (deref n m n∈))
andmap Fp m with allMap m Fp
andmap Fp m | yes p = yes (allMap-lookup p)
andmap Fp m | no ¬p = no (λ x → ¬p (allMap-tabulate x))

ocount : (Value -> Bool) -> LMap -> ℕ
ocount p [] = 0
ocount p (just x ∷ m) with p x
ocount p (just x ∷ m) | false = ocount p m
ocount p (just x ∷ m) | true = suc (ocount p m)
ocount p (nothing ∷ m) = ocount p m

change-one-ocount-goes-down :
  ∀ (m : LMap) ->
    (p : Value -> Bool) ->
    (n : ℕ) ->
    (k∈ : n ∈ (Dom' m)) ->
    p (deref n m k∈) ≡ true ->
    (v : Value) ->
    p v ≡ false ->
    ocount p m ≡ suc (ocount p (m-insert (just v) n m))
change-one-ocount-goes-down = f where
  f : ∀ (m : LMap) ->
    (p : Value -> Bool) ->
    (n : ℕ) ->
    (k∈ : n ∈ (Dom' m)) ->
    p (deref n m k∈) ≡ true ->
    (v : Value) ->
    p v ≡ false ->
    ocount p m ≡ suc (ocount p (m-insert (just v) n m))
  f [] p zero () p[derefnmk∈]≡true v pv≡false
  f (just x ∷ m) p zero k∈ p[derefnmk∈]≡true v pv≡false with p x
  ... | true with p v
  f (just x ∷ m) p zero k∈ p[derefnmk∈]≡true v () | true | true
  ... | false = refl
  f (just x ∷ m) p zero k∈ () v pv≡false | false
  f (nothing ∷ m) p zero k∈ p[derefnmk∈]≡true v pv≡false = ⊥-elim (0∈S k∈)
  f [] p (suc n) () p[derefnmk∈]≡true v pv≡false
  f (just x ∷ m) p (suc n) k∈ p[derefnmk∈]≡true v pv≡false with p x
  ... | true = cong suc (f m p n
                           (n∈S{x = just x}{l = m} k∈)
                           p[derefnmk∈]≡true v pv≡false)
  ... | false = f m p n (n∈S{x = just x}{l = m} k∈)
                  p[derefnmk∈]≡true v pv≡false
  f (nothing ∷ m) p (suc n) k∈ p[derefnmk∈]≡true v pv≡false
   = f m p n (n∈S{x = nothing}{l = m} k∈) p[derefnmk∈]≡true v pv≡false 

change-nothing-ocount-stays-same :
  ∀ (m : LMap) ->
    (p : Value -> Bool) ->
    (n : ℕ) ->
    (k∈ : n ∈ (Dom' m)) ->
    (v : Value) ->
    p (deref n m k∈) ≡ p v ->
    ocount p m ≡ ocount p (m-insert (just v) n m)
change-nothing-ocount-stays-same = f where

  f : ∀ (m : LMap) ->
    (p : Value -> Bool) ->
    (n : ℕ) ->
    (k∈ : n ∈ (Dom' m)) ->
    (v : Value) ->
    p (deref n m k∈) ≡ p v ->
    ocount p m ≡ ocount p (m-insert (just v) n m)
  f [] p zero () v pold≡pv
  f (just x ∷ m) p zero k∈ v pold≡pv with p x | p v
  f (just x ∷ m) p zero k∈ v pold≡pv | false | false = refl
  f (just x ∷ m) p zero k∈ v () | false | true
  f (just x ∷ m) p zero k∈ v () | true | false
  f (just x ∷ m) p zero k∈ v pold≡pv | true | true = refl
  f (nothing ∷ m) p zero k∈ v pold≡pv with p v
  f (nothing ∷ m) p zero k∈ v pold≡pv | false = refl
  f (nothing ∷ m) p zero k∈ v pold≡pv | true = ⊥-elim (0∈S k∈)
  f [] p (suc n) () v pold≡pv
  f (just x ∷ m) p (suc n) k∈ v pold≡pv with p x
  f (just x ∷ m) p (suc n) k∈ v pold≡pv | true =
     cong suc (f m p n (n∈S{x = just x}{l = m} k∈) v pold≡pv)
  f (just x ∷ m) p (suc n) k∈ v pold≡pv | false =
     f m p n (n∈S{x = just x}{l = m} k∈) v pold≡pv
  f (nothing ∷ m) p (suc n) k∈ v pold≡pv =
    f m p n (n∈S{x = nothing}{l = m} k∈) v pold≡pv


ocount-merge≤′sum-ocount :
  ∀ (m1 m2 : LMap) ->
    (p : Value -> Bool) ->
    ocount p (m1 U m2) ≤′ ocount p m1 + ocount p m2
ocount-merge≤′sum-ocount = f where

  f : ∀ (m1 m2 : LMap) ->
        (p : Value -> Bool) ->
        ocount p (m1 U m2) ≤′ ocount p m1 + ocount p m2
  f [] [] p = ≤′-refl
  f [] (x ∷ m2) p = ≤′-refl
  f (x ∷ m1) [] p = ≤⇒≤′ (m≤m+n (ocount p (x ∷ m1)) 0)
  f (just x ∷ m1) (just x₁ ∷ m2) p with p x | p x₁ | f m1 m2 p
  f (just x ∷ m1) (just x₁ ∷ m2) p | false | false | R = R
  f (just x ∷ m1) (just x₁ ∷ m2) p | false | true | R =
     ≤′-trans {y = suc (ocount p m1 + ocount p m2)}
              (s≤′s R) (≡is≤′ (sym (+-suc (ocount p m1) (ocount p m2))))
  f (just x ∷ m1) (just x₁ ∷ m2) p | true | false | R =
    ≤′-step R
  f (just x ∷ m1) (just x₁ ∷ m2) p | true | true | R =
    s≤′s (≤′-trans {y = ocount p m1 + ocount p m2}
         R
         (≤′+r {ocount p m2} {suc (ocount p m2)} {ocount p m1} (≤′-step ≤′-refl)))
  f (just x ∷ m1) (nothing ∷ m2) p with p x | f m1 m2 p
  f (just x ∷ m1) (nothing ∷ m2) p | false | R = R
  f (just x ∷ m1) (nothing ∷ m2) p | true | R = s≤′s R
  f (nothing ∷ m1) (just x ∷ m2) p with p x | f m1 m2 p
  f (nothing ∷ m1) (just x ∷ m2) p | false | R = R
  f (nothing ∷ m1) (just x ∷ m2) p | true | R =
     ≤′-trans {y = suc (ocount p m1 + ocount p m2)}
              (s≤′s R) (≡is≤′ (sym (+-suc (ocount p m1) (ocount p m2)))) 
  f (nothing ∷ m1) (nothing ∷ m2) p with f m1 m2 p
  ... | R = R


Dom'+∈ : (L : LMap) → List (∃[ n ] (n ∈ (Dom' L)))
Dom'+∈ L = help (Dom' L)
 where
  help : (x : List ℕ) → (List (∃[ y ] (y ∈ x)))
  help [] = []
  help (x ∷ x₁) = (x , here refl) ∷ map (λ {(a , b) → a , there b}) (help x₁)
