module Data.Circuit where

import Data.FiniteMap
import Data.FiniteMap.Properties
open import Data.Key
open import Data.Sublist
  using (sublist)
open import Data.Sublist.Forall
  using (∀ˢ ; $ᵃ)
open import Data.Sublist.Any as sAny
  using ()

open import utility
  using (_∈_)

import Data.List.Any as lAny
import Data.List.Any.Properties as lAnyP

open import Data.Bool as Bool
open import Data.Bool.Solver
  using (module ∨-∧-Solver)
open import Data.Nat as Nat
  using (ℕ ; _<_ ; _+_ ; zero ; suc ; _≤_)
open import Data.List as List
  using (List ; _∷_)
open import Data.Product as Prod
  using (proj₁ ; proj₂ ; _×_ ; _,_ ; Σ-syntax ; ∃-syntax)
open import Data.Fin as Fin
  using (Fin ; toℕ ; inject+)
open import Function
open import Relation.Binary.PropositionalEquality as Prop
open import Relation.Nullary
open import Data.Sum
  using (_⊎_)
open _⊎_


open import Data.Maybe
  using (Maybe)
open Maybe


open import Data.Fin.Properties as FinP
open import Data.Nat.Properties as NatP
open import Data.Nat.Solver
  using ()
  renaming (module +-*-Solver to s)


open ∨-∧-Solver public

{-
 A circuit is a collection of local, input, and output wires.
 The value of an input wire is unknowable.
 The value of of output and local wires are given a series of 
 boolean equations that may refer to any other wire.

-}

instance
  finkey : BijectiveKey ℕ 
  finkey = bijective-key id id id id refl

Key = ℕ

module Circ = Data.FiniteMap Key
open Circ
module CircP = Data.FiniteMap.Properties Key

module RMap = Data.FiniteMap Key
RenamingMap = RMap.Map ℕ

Wires : ℕ → Set
Wires n = Circ.Map (Polynomial n)

AllWires : ∀ l o i  → Wires (l + o + i) → Set
AllWires l o i w = (keys w) ≡ (List.upTo (l + o))

lflip : ∀ x y (g : ℕ → ℕ)
        →  List.applyUpTo (λ x₁ → suc (y + g x₁)) x
            ≡
           List.applyUpTo (λ x₁ → y + suc (g x₁)) x
lflip zero y g = refl
lflip (suc x) y g rewrite NatP.+-suc y (g 0) = cong (suc y + g 0 ∷_) (lflip x y (g ∘ suc))


safe : ∀{x n} (w : Wires n)
       → (keys w) ≡ (List.upTo x)
       → ∀ k → ∈Dom k w
       → k < x 
safe {x = x} w eq k k∈ = t k 0 x (subst (k ∈_) eq k∈)
  where
    t : ∀ k y x → k ∈ (List.applyUpTo (y +_) x) → k < (y + x)
    t k y zero ()
    t k y (suc x) (lAny.here refl)
      rewrite NatP.+-comm y 0
            | NatP.+-suc y x
      = ≤-stepsʳ x NatP.≤-refl
    t k y (suc x) (lAny.there k∈)
      rewrite NatP.+-suc y x
            | NatP.+-suc y 0
      = t k (suc y) x (subst
                       (k ∈_)
                       (sym (lflip x y id))
                       k∈)

total : ∀{n x} (w : Wires n)
        → (keys w) ≡ (List.upTo x)
        → ∀ k → k < x
        → ∈Dom k w
total {x = x} w eq k klt = subst (k ∈_) (sym eq) (inupto x 0 k klt)
  where
    inupto : ∀ x y k → k < x → (y + k) ∈ List.applyUpTo (y +_) x
    inupto zero y k ()
    inupto (suc x) y .0 (Nat.s≤s Nat.z≤n) = lAny.here refl
    inupto (suc (suc x)) y (suc k) (Nat.s≤s (Nat.s≤s klt))
      = lAny.there
        $ subst
          id
          (begin
           suc (y + k) ∈ (suc (y + zero) ∷ List.applyUpTo (λ x₁ → suc (y + suc x₁)) x)
           ≡⟨ cong (_∈ (suc (y + zero) ∷ List.applyUpTo (λ x₁ → suc (y + suc x₁)) x))
                  (sym $ NatP.+-suc y k) ⟩
           (y + suc k) ∈ (suc (y + zero) ∷ List.applyUpTo (λ x₁ → suc (y + suc x₁)) x)
           ≡⟨ cong (λ n → (y + suc k) ∈ (n ∷ List.applyUpTo (λ x₁ → suc (y + suc x₁)) x))
                    (sym $ NatP.+-suc y 0) ⟩
           (y + suc k) ∈ (y + 1 ∷ List.applyUpTo (λ x₁ → suc (y + suc x₁)) x)
           ≡⟨ cong (λ l → (y + suc k) ∈ (y + 1 ∷ l))
                    (lflip x y suc) ⟩
           (y + suc k) ∈ (y + 1 ∷ List.applyUpTo (λ x₁ → y + suc (suc x₁)) x) ∎)
          $ inupto (suc x) (suc y) k (Nat.s≤s klt)
     where
       open Prop.≡-Reasoning
      
             

record Circuit (locals outputs inputs : ℕ)   : Set where
  {- 
     interpretation:
     names from [0,locals) are the local wires
     names from [locals, locals + outputs) are the output wires
     names from [locals + outputs, locals + outputs + inputs)
     that is we divide the number line from 0 to (locals + outputs + inputs)
     into:

         locals              outputs             inputs
     ------------------|---------------------|--------------|
     
     The inputs of the ciruit may not be written to, so the domain
     of the mapping must be `locals + outputs`. 

     
-}
  constructor circuit
  field
   wires : Wires (locals + outputs + inputs)
   all-wires : AllWires locals outputs inputs wires 


{- the order of a circuit is the order of its polynomials -}
order : ∀{l o i} → Circuit l o i → ℕ
order {l}{o}{i} _ = l + o + i

record LocalWire {l o i} (c : Circuit l o i) : Set where
  constructor localwire
  field
   fin : Fin l

record OutputWire {l o i} (c : Circuit l o i) : Set where
  constructor outputwire
  field
   fin : Fin o

record InputWire {l o i} (c : Circuit l o i) : Set where
  constructor inputwire
  field
   fin : Fin i

localwire-to-internal-name
  : ∀{l o i}{c : Circuit l o i} → LocalWire c → Fin (l + o)
localwire-to-internal-name {o = o} (localwire fin)
  = inject+ o fin

outputwire-to-internal-name
  : ∀{l o i}{c : Circuit l o i} → OutputWire c → Fin (l + o)
outputwire-to-internal-name {l}{o} (outputwire fin)
  rewrite NatP.+-comm l o
  = inject+ l fin

inputwire-to-internal-name
  : ∀{l o i}{c : Circuit l o i} → InputWire c → Fin (l + o + i)
inputwire-to-internal-name{l}{o}{i}(inputwire fin)
  rewrite (s.solve 3 (λ l o i → l s.:+ o s.:+ i s.:= (i s.:+ (l s.:+ o))) refl l o i)
  = inject+ (l + o) fin 

lift-wire-name : ∀{l o i} → Circuit l o i → Fin (l + o) → Fin (l + o + i)
lift-wire-name {i = i} _ = inject+ i

deref-localwire : ∀{l o i}{c : Circuit l o i}
                  → LocalWire c → Polynomial (order c)
deref-localwire {l}{o}{i} {c = c} lw
  = lookup wires (total wires all-wires k (FinP.toℕ<n kF))
    where
      open Circuit c
      kF = (localwire-to-internal-name lw)
      k = toℕ kF

data WireType (l o i : ℕ) : Set where
  local : Fin l → WireType l o i
  output : Fin o → WireType l o i
  input : Fin i → WireType l o i

fin-split : ∀ a b → Fin (a + b) → Fin a ⊎ Fin b
fin-split a b f
  with (toℕ f) NatP.≥? a
... | yes lt = inj₂ $ Fin.reduce≥ f lt
... | no nlt = inj₁ $ Fin.fromℕ≤ (NatP.≰⇒> nlt)

to-wire-type : ∀ l o i → Fin (l + o + i) → WireType l o i
to-wire-type l o i f 
  with fin-split (l + o) i f
... | inj₂ y = input y
... | inj₁ x
  with fin-split l o x
... | inj₁ a = local a
... | inj₂ b = output b
