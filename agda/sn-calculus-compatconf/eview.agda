module sn-calculus-compatconf.eview where

open import sn-calculus-compatconf.base
open import sn-calculus-compatconf.in-lift  using (1-steplρ-E-view-ecin-lift)
open import sn-calculus-compatconf.split    using (1-steplρ-E-view-ecsplit)
open import sn-calculus-compatconf.same     using (1-steplρ-E-view-ecsame)

open import sn-calculus
open import utility renaming (_U̬_ to _∪_)
open import context-properties
  using (get-view ; ->E-view ; ->pot-view)

open import sn-calculus-confluence
  using (R-confluent)

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.Binding
open import Esterel.Lang.CanFunction
  using (Can ; Canₛ ; Canₛₕ ; Canₖ ; module CodeSet)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Context.Properties
  using (plugc)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)

open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; cong ; trans ; subst ; module ≡-Reasoning)
open import Data.Bool
  using (Bool ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; _∷_ ; [] ; _++_)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using (++ˡ ; ++ʳ)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; zero ; suc ; _+_) renaming (_⊔_ to _⊔ℕ_)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; _,′_ ; proj₁ ; proj₂ ; _×_ ; ∃ ; map)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_ ; id ; _∋_)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open ->E-view
open ->pot-view

open EvaluationContext1
open _≐_⟦_⟧e
open Context1
open _≐_⟦_⟧c

open ListSet Data.Nat._≟_

{-
     p
  ρθ. E⟦qin⟧   -- sn⟶₁ ->    ρθq. E⟦qo⟧
 (ρθ) C⟦rin⟧   -- sn⟶  ->   (ρθ)  C⟦ro⟧
-}
1-steplρ-E-view : ∀{E C p qin q qo rin ro θ θq BV FV} →
  {ρθ·psn⟶₁ρθq·q  :  ρ θ · p sn⟶₁ ρ θq · q} →
  CorrectBinding (ρ θ · p) BV FV →

  (p≐E⟦qin⟧  :  p ≐ E ⟦ qin ⟧e) →
  (q≐E⟦qo⟧   :  q ≐ E ⟦ qo ⟧e) →
  ->E-view  ρθ·psn⟶₁ρθq·q  p≐E⟦qin⟧  q≐E⟦qo⟧ →

  (p≐E⟦rin⟧  :  p ≐ C ⟦ rin ⟧c) →
  (rinsn⟶₁ro  :  rin sn⟶₁ ro) →

  ∃ λ { (θo , po) →
    (ρ θq · q        sn⟶* ρ θo · po) ×
    (ρ θ · C ⟦ ro ⟧c sn⟶* ρ θo · po) }

1-steplρ-E-view (CBρ cb) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ rinsn⟶₁ro
  with get-context-prefix p≐E⟦qin⟧ p≐C⟦rin⟧
1-steplρ-E-view (CBρ cb) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ rinsn⟶₁ro | ecsame =
  map proj₁ (map (sn⟶*-inclusion ∘ sn⟶-inclusion) (sn⟶*-inclusion ∘ sn⟶-inclusion ∘ proj₁))
    (1-steplρ-E-view-ecsame cb p≐E⟦qin⟧ q≐E⟦qo⟧ e-view
      p≐C⟦rin⟧ (plugc refl) rinsn⟶₁ro)
1-steplρ-E-view (CBρ cb) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ rinsn⟶₁ro | ecin-lift =
  ⊥-elim
   (1-steplρ-E-view-ecin-lift cb p≐E⟦qin⟧ q≐E⟦qo⟧ e-view
     p≐C⟦rin⟧ (plugc refl) rinsn⟶₁ro)
1-steplρ-E-view (CBρ cb) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ rinsn⟶₁ro | ecsplit div
  with 1-steplρ-E-view-ecsplit cb div p≐E⟦qin⟧ q≐E⟦qo⟧ e-view
                                            p≐C⟦rin⟧ (plugc refl) rinsn⟶₁ro
... | po , inj₁ refl  , _ , _ , _ , ρθ·rsn⟶₁ρθq·po , e-view' =
  _ , rrefl ,′ sn⟶*-inclusion (sn⟶-inclusion ρθ·rsn⟶₁ρθq·po)
... | po , inj₂ qsn⟶po , _ , _ , _ , ρθ·rsn⟶₁ρθq·po , e-view' =
  _ , sn⟶*-inclusion (Context1-sn⟶ (cenv _) qsn⟶po) ,′ sn⟶*-inclusion (sn⟶-inclusion ρθ·rsn⟶₁ρθq·po)
