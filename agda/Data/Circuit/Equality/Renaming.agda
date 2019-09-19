module Data.Circuit.Equality.Renaming where

open import Data.Circuit
open Circ
open CircP 
  renaming (module Canonical to C)
open C using (Canonical)


open import utility
  using (_∈_ ;  ∈:: ; typeof)
  renaming (_⊆¹_ to _⊆_)

open import Data.Sublist as SL
  using (Sublist ; sublist ; get ; Rec ; visit-rec ; split ; get∈)
import Data.Sublist.Properties as SLP
open import Data.Sublist.Forall as Forall
  using (∀ˢ ; uncurry-∀ˢ ; ∀ˢ-irrelevant-het )
open ∀ˢ

open import Data.List as List
  using (length ; List ; _++_ ; _∷_)
import Data.List.Properties as ListP

open import Data.List.Any as LA
  using (here ; there)

open import Data.Nat as Nat
  using (ℕ ; _<_ ; _+_ ; zero ; suc ; _∸_ ; _≤_)
open _≤_
import Data.Nat.Properties as NatP

open import Data.Fin as Fin
  using (Fin ; fromℕ≤ ; toℕ)
import Data.Fin.Properties as FinP

open import Data.Product as Prod
  using (proj₁ ; proj₂ ; _×_ ; _,_ ; Σ-syntax ; ∃-syntax ; ∃)
open import Data.Sum as Sum
  using (inj₁ ; inj₂)

open import Data.Maybe as Maybe
  using (Maybe ; just ; nothing)


open import Relation.Binary.PropositionalEquality as P
  using (_≡_ ; inspect)
  renaming (module ≡-Reasoning to P)
open import Relation.Binary.HeterogeneousEquality as H
  using (_≅_)

open import Relation.Binary
  using (Setoid ; Irrelevant)
open import Relation.Unary
  using (Pred)
open import Relation.Nullary
 using (¬_ ; yes ; no)

open import Relation.Binary.Indexed.Heterogeneous.Core
  using (Reflexive ; Symmetric ; Transitive)

open import Function.Equality
  using (_⟶_ ; Π ; _⟨$⟩_)
open import Function.Bijection
  using (Bijection ; Bijective)

open import Function

{-

A renaming is a mapping from every name in a circuit
(variable and wire) to a new, unique name.

Since the set of names must be total, this means the
renaming is just a bijection from (Fin n) to (Fin n).
(Or rather three of them, for l, o, and i)


-}


record Renaming (l o i : ℕ) : Set where
 constructor a-renaming
 field
  l-rename : Bijection (FinP.setoid l) (FinP.setoid l)
  o-rename : Bijection (FinP.setoid o) (FinP.setoid o)
  i-rename : Bijection (FinP.setoid i) (FinP.setoid i) 

rename-poly : ∀ {l o i} → Renaming l o i
              → Polynomial (l + o + i)
              → Polynomial (l + o + i)
rename-poly r (op o p p₁)
 = op o (rename-poly r p) (rename-poly r p₁) 
rename-poly r (con c) = con c
rename-poly{l}{o}{i} r (var x)
  with to-wire-type l o i x
... | local n
  rewrite NatP.+-assoc l o i
  = var (Fin.inject+ (o + i) (to ⟨$⟩ n))
  where
    open Renaming r
    open Bijection l-rename
... | output n = var (Fin.inject+ i (Fin.raise l (to ⟨$⟩ n)))
  where
    open Renaming r
    open Bijection o-rename
... | input n = var (Fin.raise (l + o) (to ⟨$⟩ n))
  where
    open Renaming r
    open Bijection i-rename
rename-poly r (p :^ n) = (rename-poly r p) :^ n
rename-poly r (:- p) = :- (rename-poly r p) 


rename-k : ∀{l o i}
           → (r : Renaming l o i)
           → ∀ k → k < l + o → Key
rename-k {l}{o}{i} r k klt
  with fin-split l o $ fromℕ≤ klt 
... | inj₁ x = toℕ $ (Bijection.to (Renaming.l-rename r)) ⟨$⟩ x
... | inj₂ x = l + (toℕ $ (Bijection.to (Renaming.o-rename r)) ⟨$⟩ x)


rename-k-lt : ∀{l o i}
           → (r : Renaming l o i)
           → ∀ k → (klt : k < l + o)
           → (rename-k r k klt) < l + o
rename-k-lt {l} {o} r k klt
  with l Nat.≤? toℕ (fromℕ≤ klt)
... | yes p = NatP.+-monoʳ-< l (FinP.toℕ<n $ (Bijection.to (Renaming.o-rename r)) ⟨$⟩ Fin.reduce≥ (fromℕ≤ klt) p)
... | no ¬p = NatP.≤-stepsʳ o (FinP.toℕ<n $ (Bijection.to (Renaming.l-rename r)) ⟨$⟩ fromℕ≤ (NatP.≰⇒> ¬p))

rnk-inverse : ∀{l o i}
           → (r : Renaming l o i)
           → ∀ k
           → (klt : k < l + o)
           → (rnklt : (rename-k r k klt) < l + o)
           → k ≡ (rename-k r (rename-k r k klt) rnklt)
rnk-inverse{l}{o}{i} r k klt rnklt
  with l Nat.≤? toℕ (fromℕ≤ klt)
rnk-inverse {l} {o} {i} r k klt rnklt | yes p
  with l Nat.≤? toℕ (fromℕ≤ rnklt) 
rnk-inverse {l} {o} {i} r k klt rnklt | yes p | yes q
   = {!(rename-k-lt r k klt) !}
   --(FinP.toℕ-fromℕ≤ rnklt)
rnk-inverse {l} {o} {i} r k klt rnklt | yes p | no ¬p
  = {! P.subst (l ≤_) (FinP.toℕ-fromℕ≤ klt) p!}
    
  --P.subst (¬_ ∘ (l ≤_)) (FinP.toℕ-fromℕ≤ rnklt) ¬p
  --P.subst (l ≤_) (FinP.toℕ-fromℕ≤ klt) p
rnk-inverse {l} {o} {i} r k klt rnklt | no ¬p
  with l Nat.≤? toℕ (fromℕ≤ rnklt)  | inspect (l Nat.≤?_) (toℕ (fromℕ≤ rnklt))
rnk-inverse {l} {o} {i} r k klt rnklt | no ¬p | yes p  | _ = {!!}
rnk-inverse {l} {o} {i} r k klt rnklt | no ¬p | no ¬p₁ | P.[ eq ] = {! !}
--(FinP.toℕ-fromℕ≤ (NatP.≰⇒> ¬p₁))


rename-wires-rec : ∀{l o i n}
               → (w : Wires (l + o + i))
               → AllWires l o i w
               → Renaming l o i
               → Sublist (keys w) n
               → (rec : Rec (keys w) n (λ _ → Wires (l + o + i)))
               → Wires (l + o + i)
rename-wires-rec w safe-wires r Sublist.empty rec = empty
rename-wires-rec {l = l} {o} {i} w safe-wires r x@(Sublist.elem n n<l sl) rec 
  = union (rec P.refl sl)
    $ [ (rename-k r (get x) (safe w safe-wires (get x) (get∈ x))  ) ↦ rename-poly r (lookup w (get∈ x)) ]

rename-wires : ∀{l o i}
               → (w : Wires (l + o + i))
               → (AllWires l o i w)
               → Renaming l o i
               → Wires (l + o + i)
rename-wires {l = l} {o} {i} w safe-wires r
  = key-visit-rec
     w
     {A = const (Wires (l + o + i))}
     (rename-wires-rec w safe-wires r)


renaming-domain-unchanged : ∀{l o i}
                            → (w : Wires (l + o + i))
                            → (a : AllWires l o i w)
                            → (r : Renaming l o i)
                            → AllWires l o i (rename-wires w a r)
renaming-domain-unchanged {l}{o}{i} w a r
  = P.subst
     (_≡ (List.upTo _))
     (keys⇔-means-equal w (rename-wires w a r) sub1 sub2)
     a
  where
    sleq : ∀{n x}
           → (sl : Sublist (List.upTo x) (suc n))
           → (get sl) ≡ (suc n) ∸ x 
    sleq = {!!}

    rn = rename-k r


    step : ∀ k → (klt : k < l + o)
           → (∈Dom (rn k klt) w)
    step = {!!}

    step-rn : ∀ k → (klt : k < l + o)
           → (∈Dom (rn k klt) (rename-wires w a r))
    step-rn = {!!}


    sub1 : (keys w) ⊆ (keys (rename-wires w a r))
    sub1 k k∈ = P.subst
                 (λ k → ∈Dom k (rename-wires w a r))
                 (P.sym (rnk-inverse r k klt (safe w a (rn k klt) (step k klt)))) 
                 (step-rn (rn k klt) (safe w a (rn k klt) (step k klt)))
       where klt = (safe w a k k∈)


    sub2 : (keys (rename-wires w a r)) ⊆ (keys w)
    sub2 k k∈ = {!!}

          

rename-circuit : ∀{l o i} (c : (Circuit l o i))
                → Renaming l o i
                → (Circuit l o i)
rename-circuit {l}{o}{i} c r
  = circuit (rename-wires wires all-wires r)
            (renaming-domain-unchanged wires all-wires r)
  where open Circuit c

data WasRenamed {l o i} (c : (Circuit l o i)) : (Circuit l o i) → Set where
  a-renaming : ∀ (r : Renaming l o i) → WasRenamed c (rename-circuit c r)

renaming-sym : ∀{l o i} → Renaming l o i → Renaming l o i
renaming-sym (a-renaming l-rename o-rename i-rename)
  = a-renaming (biflip l-rename) (biflip o-rename) (biflip i-rename)
  where
    biflip : ∀{l1 l2 r1 r2} {l : (Setoid l1 l2)} {r : (Setoid r1 r2)}
             → Bijection l r
             → Bijection r l
    biflip bj = record
      { to = from
      ; bijective = record
         { injective = Injection.injective (LeftInverse.injection right-inverse) 
         ; surjective =
           record { from = to ; right-inverse-of = left-inverse-of } } }
      where
        open Bijection bj
        open import Function.LeftInverse
        open import Function.Injection



renaming-sym-inverse : ∀{l o i}
                       → (w : Wires (l + o + i))
                       → (a : AllWires l o i w)
                       → (r : Renaming l o i) 
                       → (rename-wires (rename-wires w a r)
                                       (renaming-domain-unchanged w a r)
                                       (renaming-sym r))
                         ≡
                         w
renaming-sym-inverse {l}{o}{i} w a r = {!!}
  where
    {- first, prove that all renamings are canonical -}
    A : ∀{n} → Sublist (keys w) n → Set
    A sl = Canonical $ visit-rec (rename-wires-rec w a r) sl 
    renaming-is-canonical-rec : ∀ {n} → (sl : Sublist (keys w) n) → (Rec (keys w) n A) → (A sl)
    renaming-is-canonical-rec Sublist.empty rec = C.empty-canonical
    renaming-is-canonical-rec l@(Sublist.elem n n<l sl) rec
      = C.union-canonical (rec P.refl sl)
        $  C.single-canonical (rename-k r (get l) (safe w a (get l) (get∈ l)) )
                              (rename-poly r (lookup w (get∈ l))) 

    renaming-is-canonical : Canonical (rename-wires w a r)
    renaming-is-canonical
      =  key-visit-rec w renaming-is-canonical-rec 
    {- next, prove that renamings don't change the domain -}
    -- done by renaming-domain-unchanged
    

was-renamed-sym : ∀ {l o i} {c1 c2 : Circuit l o i}
                → WasRenamed c1 c2 → WasRenamed c2 c1
was-renamed-sym {l}{o}{i}{c1 = c1}{c2} (a-renaming r)
   with ((rename-wires (Circuit.wires c2)
                       (Circuit.all-wires c2)
                       (renaming-sym r))
             ≡ (Circuit.wires c1)
            ∋
            (renaming-sym-inverse (Circuit.wires c1) (Circuit.all-wires c1) r))
... | eq1  = {!H.subst id
             (H.cong₂
              (λ w a → WasRenamed c2 (circuit w a))
              (H.≡-to-≅ eq1)
              (K-het
                 (renaming-domain-unchanged (Circuit.wires c2)
                   (Circuit.all-wires c2)
                   (renaming-sym r))
                 (Circuit.all-wires c1)))
              $ a-renaming{c =  c2} (renaming-sym r)!}
     where
       K-het : ∀{t}{T : Set t}{a b c : T}
               → (eq1 : a ≡ c) → (eq2 : b ≡ c)
               → eq1 ≅ eq2
       K-het P.refl P.refl = H.refl
       w1 = (rename-wires (Circuit.wires c2)
                          (Circuit.all-wires c2)
                          (renaming-sym r))
       a1 = (renaming-domain-unchanged (Circuit.wires c2)
                                       (Circuit.all-wires c2)
                                       (renaming-sym r))
