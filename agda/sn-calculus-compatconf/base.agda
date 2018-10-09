module sn-calculus-compatconf.base where

open import sn-calculus
open import utility renaming (_U̬_ to _∪_)

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.Binding
open import Esterel.Lang.PotentialFunction
  using (Can ; Canₛ ; Canₛₕ ; Canₖ ; module CodeSet)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Context.Properties
  using (unplug ; unplugc ; plug ; plugc ; ⟦⟧e-to-⟦⟧c)
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
  using (List ; _∷_ ; [] ; _++_ ; map)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using (++ˡ ; ++ʳ)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; zero ; suc ; _+_) renaming (_⊔_ to _⊔ℕ_)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; _,′_ ; proj₁ ; proj₂ ; _×_ ; ∃)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_ ; id ; _∋_)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open EvaluationContext1
open _≐_⟦_⟧e
open Context1
open _≐_⟦_⟧c

open ListSet Data.Nat._≟_


data two-roads-diverged : EvaluationContext → Context → Set where
  divout-disjoint : ∀ {C₁ C}    → two-roads-diverged []                         (C₁ ∷ C)
  divpar-split₁   : ∀ {E C p q} → two-roads-diverged (epar₁ q ∷ E) (ceval (epar₂ p) ∷ C)
  divpar-split₂   : ∀ {E C p q} → two-roads-diverged (epar₂ p ∷ E) (ceval (epar₁ q) ∷ C)
  divseq-split    : ∀ {E C p q} → two-roads-diverged (eseq q  ∷ E) (cseq₂ p         ∷ C)
  divloop-splitˢ  : ∀ {E C p q} → two-roads-diverged (eloopˢ q  ∷ E) (cloopˢ₂ p       ∷ C)
  divin : ∀ {E₁ E C} → two-roads-diverged E C → two-roads-diverged (E₁ ∷ E) (ceval E₁ ∷ C)


data context-prefix : EvaluationContext → Context → Set where
  ecsame     : ∀ {E}       → context-prefix E                (map ceval E)
  ecin-lift  : ∀ {E E₁ E'} → context-prefix (E ++ (E₁ ∷ E')) (map ceval E)
  ecsplit    : ∀ {E C} → (div : two-roads-diverged E C) → context-prefix E C


get-context-prefix : ∀ {E C p q r} →
  p ≐ E ⟦ q ⟧e → p ≐ C ⟦ r ⟧c →
  context-prefix E C
get-context-prefix {[]} {[]} dehole p≐C⟦r⟧ = ecsame
get-context-prefix {[]} {C₁ ∷ C} dehole p≐C⟦r⟧ = ecsplit divout-disjoint
get-context-prefix {E₁ ∷ E} p≐E⟦q⟧ dchole = ecin-lift
get-context-prefix (depar₁ p≐E⟦q⟧) (dcpar₂ p≐C⟦r⟧) = ecsplit divpar-split₁
get-context-prefix (depar₂ p≐E⟦q⟧) (dcpar₁ p≐C⟦r⟧) = ecsplit divpar-split₂
get-context-prefix (deseq  p≐E⟦q⟧) (dcseq₂ p≐C⟦r⟧) = ecsplit divseq-split
get-context-prefix (deloopˢ p≐E⟦q⟧) (dcloopˢ₂ p≐C⟦r⟧) = ecsplit divloop-splitˢ
get-context-prefix (depar₁ p≐E⟦q⟧) (dcpar₁ p≐C⟦r⟧)
  with get-context-prefix p≐E⟦q⟧ p≐C⟦r⟧
... | ecsame         = ecsame
... | ecin-lift      = ecin-lift
... | ecsplit    div = ecsplit (divin div)
get-context-prefix (depar₂ p≐E⟦q⟧) (dcpar₂ p≐C⟦r⟧)
  with get-context-prefix p≐E⟦q⟧ p≐C⟦r⟧
... | ecsame         = ecsame
... | ecin-lift      = ecin-lift
... | ecsplit    div = ecsplit (divin div)
get-context-prefix (deloopˢ p≐E⟦q⟧)  (dcloopˢ₁ p≐C⟦r⟧)
  with get-context-prefix p≐E⟦q⟧ p≐C⟦r⟧
... | ecsame         = ecsame
... | ecin-lift      = ecin-lift
... | ecsplit    div = ecsplit (divin div)
get-context-prefix (deseq p≐E⟦q⟧)  (dcseq₁ p≐C⟦r⟧)
  with get-context-prefix p≐E⟦q⟧ p≐C⟦r⟧
... | ecsame         = ecsame
... | ecin-lift      = ecin-lift
... | ecsplit    div = ecsplit (divin div)
get-context-prefix (desuspend p≐E⟦q⟧) (dcsuspend p≐C⟦r⟧)
  with get-context-prefix p≐E⟦q⟧ p≐C⟦r⟧
... | ecsame         = ecsame
... | ecin-lift      = ecin-lift
... | ecsplit    div = ecsplit (divin div)
-- didn't directly pattern match on p≐C⟦r⟧ in order to get complete pattern matching coverage
get-context-prefix (detrap p≐E⟦q⟧) p≐trap[C⟦r⟧] with p≐trap[C⟦r⟧]
... | dchole       = ecin-lift
... | dctrap p≐C⟦r⟧ with get-context-prefix p≐E⟦q⟧ p≐C⟦r⟧
... | ecsame         = ecsame
... | ecin-lift      = ecin-lift
... | ecsplit    div = ecsplit (divin div)
