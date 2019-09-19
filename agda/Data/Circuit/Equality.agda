module Data.Circuit.Equality where

open import Data.Circuit
open Circ

open import Data.Circuit.Equality.Renaming public

open import utility using (_∈_ ;  ∈::)

open import Data.Sublist as SL
  using (Sublist ; sublist ; get ; Rec ; visit-rec)
open import Data.Sublist.Forall as Forall
  using (∀ˢ ; uncurry-∀ˢ ; ∀ˢ-irrelevant-het )
open ∀ˢ

open import Data.List as List
  using (length)

open import Data.Nat as Nat
  using (ℕ ; _<_ ; _+_ ; zero ; suc)
import Data.Nat.Properties as NatP

open import Data.Fin as Fin
  using (Fin ; fromℕ≤ ; toℕ)
import Data.Fin.Properties as FinP

open import Data.Product as Prod
  using (proj₁ ; proj₂ ; _×_ ; _,_ ; Σ-syntax ; ∃-syntax)
open import Data.Sum as Sum
  using (inj₁ ; inj₂)


open import Relation.Binary.PropositionalEquality as P
  using (_≡_)
  renaming (module ≡-Reasoning to P)
open import Relation.Binary.HeterogeneousEquality as H
  using (_≅_)


open import Relation.Binary
  using (Setoid)
open import Relation.Nullary
 using (¬_)

open import Relation.Binary.Indexed.Heterogeneous.Core
  using (Reflexive ; Symmetric ; Transitive)

open import Function.Equality
  using (_⟶_ ; Π ; _⟨$⟩_)
open import Function.Bijection
  using (Bijection ; Bijective)

open import Function


LocalSetoid : ∀{l o i} → (c : Circuit l o i) → Setoid _ _
LocalSetoid = P.setoid ∘ LocalWire
OutputSetoid : ∀{l o i} → (c : Circuit l o i) → Setoid _ _
OutputSetoid = P.setoid ∘ OutputWire
InputSetoid : ∀{l o i} → (c : Circuit l o i) → Setoid _ _
InputSetoid = P.setoid ∘ InputWire

data DoesNotContain {l o i}{c : Circuit l o i} (lw : LocalWire c) :
                    (Polynomial (order c)) → Set
                    where
     opcon : ∀{anop p1 p2}
             → DoesNotContain lw p1 → DoesNotContain lw p2
             → DoesNotContain lw (op anop p1 p2)
     concon : ∀ b → DoesNotContain lw (con b)
     varcon : (f : Fin (order c)) → ¬ f ≡ (lift-wire-name c (localwire-to-internal-name lw))
              → DoesNotContain lw (var f)
     ^con : ∀{p} n
            → DoesNotContain lw p 
            → DoesNotContain lw (p :^ n)
     -con : ∀{p} → DoesNotContain lw p
            → DoesNotContain lw (:- p)


record NotImmediatelySelfReferential
         {l o i} {c : Circuit l o i} (lw : LocalWire c) : Set
         where
     field
      lack-of-containment : DoesNotContain lw (deref-localwire lw)

{-

A Propigation in-lines a local wire which is not self referential

This is the only operation which can change the order of circuit

-}
{-
record IsPropigationOf (l o i : ℕ)
                       (equations-left : Wires ((suc l) + o + i))
                       (wire : Fin (suc (l + o)))
                       (equations-right : Wires (l + o + i)) :
                       Set where

record DidPropagation {l o i}
                   (c1 : Circuit (suc l) o i)
                   (lw : LocalWire c1)
                   (c2 : Circuit l o i) : Set
       where
   constructor propagation
   field
    is-not-self-referential : NotImmediatelySelfReferential lw
    is-prop-of : IsPropigationOf l o i 
                   (Circuit.wires c1)
                   (localwire-to-internal-name lw)
                   (Circuit.wires c2)
     
data Propagation : ∀{ll lr o i}
                   → (c1 : Circuit ll o i)
                   → (c2 : Circuit lr o i)
                   → Set where
  prop-left  : ∀{l o i}
               → (c1 : Circuit (suc l) o i) → (c2 : Circuit l o i)
               → (lw : LocalWire c1)
               → DidPropagation c1 lw c2
               → Propagation c1 c2
  prop-right : ∀{l o i}
               → (c1 : Circuit l o i) → (c2 : Circuit (suc l) o i)
               → (lw : LocalWire c2)
               → DidPropagation c2 lw c1
               → Propagation c1 c2
               
-}
{-
data Substitution : ∀ {l o i} (c1 c2 : Circuit l o i) → Set where
  expand : ∀ {l o i} → (c1 c2 : Circuit l o i)
           → Expanded (Circuit.wires c2) 
  contract : 
 -}    
  
{- equality is given by equality of the denotation of
   the boolean expressions`
  -}

_≡ₑ_ : ∀{n} → Polynomial n → Polynomial n → Set 
p1 ≡ₑ p2 = ∀ ρ → ⟦ p1 ⟧ ρ ≡ ⟦ p2 ⟧ ρ

SameValues : ∀{n} → (w1 w2 : Wires n) → Set
SameValues w1 w2 = ∀ k → (k∈ : ∈Dom k w1)
                   → Σ[ k∈' ∈ ∈Dom k w2 ]
                      (lookup w1 k∈) ≡ₑ (lookup w2 k∈')

same-values-refl : ∀{n} → (w : Wires n) → SameValues w w
same-values-refl w k k∈ = k∈ , λ ρ → P.refl

same-values-sym-under-domain-equality
  : ∀{n} {w1 w2 : Wires n}
    → (keys w1) ≡ (keys w2)
    → SameValues w1 w2
    → SameValues w2 w1
same-values-sym-under-domain-equality = {!!}

record _≡w_ {n} (w1 w2 : Wires n) : Set where
  constructor samewires
  field
    same-keys    : (keys w1) ≡ (keys w2)
    same-values  : SameValues w1 w2
                    
_≡wc_ : ∀{l o i} → Circuit l o i → Circuit l o i → Set
_≡wc_ c1 c2 = (Circuit.wires c1) ≡w (Circuit.wires c2)

≡wc-refl : ∀{l o i} → (c : Circuit l o i) → c ≡wc c
≡wc-refl c = samewires P.refl (same-values-refl wires)
  where open Circuit c
 
≡wc-sym : ∀{l o i} → (c1 c2 : Circuit l o i)
          → c1 ≡wc c2 → c2 ≡wc c1
≡wc-sym c1 c2 (samewires k v)
   = samewires (P.sym k)
     $ same-values-sym-under-domain-equality k v

{-

two steps to equality proving: first equate the
"spine" (the connections between nodes), then equate
bool expressions.

-}

data _=c=_ {i o} : ∀{ll rl} → Circuit ll o i  → Circuit rl o i → Set where
  bool-equil : ∀{l}
               → (c1 : Circuit l o i)
               → (c2 : Circuit l o i)
               → c1 ≡wc c2
               -----------------------
               → c1 =c= c2
  rename : ∀{l1 l2}
           → (c1 : Circuit l1 o i)
           → (c2 : Circuit l2 o i)
           → (c3 : Circuit l2 o i)
           → (c1 =c= c2)
           → (rn : WasRenamed c2 c3)
           --------------------
           → c1 =c= c3
           {-
  propagate : ∀{l1 l2 l3} 
              → (c1 : Circuit l1 o i)
              → (c2 : Circuit l2 o i)
              → (c3 : Circuit l3 o i)
              → (c1 =c= c2)
              → (Propagation c2 c3)
              ---------------------
              → c1 =c= c3 -}

refl : ∀{l o i}{c : Circuit l o i} → c =c= c
refl {c = c} = bool-equil c c (≡wc-refl c)

trans : ∀{l1 l2 l3 o i}{c1 : Circuit l1 o i}{c2 : Circuit l2 o i}{c3 : Circuit l3 o i}
        → c1 =c= c2 → c2 =c= c3 → c1 =c= c3
trans = {!!}


rename-wires-equal-is-sym
   : ∀ {l o i}
       {c1 c2 c3 : Circuit l o i}
     → (Circuit.wires c1) ≡w (Circuit.wires c2) 
     → WasRenamed c2 c3
     → WasRenamed c1 c3
rename-wires-equal-is-sym = {!!}

rename-sym-rec : ∀ {ll lr o i}
             {c1 : Circuit ll o i}{c2 c3 : Circuit lr o i}
             → c1 =c= c2
             → WasRenamed c2 c3
             → c3 =c= c1
rename-sym-rec {c1 = c1}{c2}{c3} (bool-equil c1 c2 x) rnc2→c3
  = rename c3 {!!} c1 {!!}
     {!!}
    {-(rename-wires-equal-is-sym
      {!!}
      (renaming-sym (rename-wires-equal-is-sym x rnc2→c3)) )-}
rename-sym-rec (rename c1 c2 c3 c1=c2 rn) rnc2→c3
 = {!!}

sym : ∀{ll lr o i}{c1 : Circuit ll o i}{c2 : Circuit lr o i}
      → c1 =c= c2 → c2 =c= c1
sym {c1 = c1} {c2} (bool-equil .c1 .c2 x) = bool-equil c2 c1 (≡wc-sym c1 c2 x)
sym {c1 = c1} {c3} (rename .c1 c2 .c3 c1=c2 rn)
  = {! rename c2 c1 ? (sym c1=c2) {!!} !}
--sym {c1 = c1} {c2} (propagate .c1 c3 .c2 c1=c2 x)
--  = {!!}



