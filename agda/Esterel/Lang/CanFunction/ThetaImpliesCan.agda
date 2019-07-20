module Esterel.Lang.CanFunction.ThetaImpliesCan where
{-

This module defines Canθₛ⊆Canₛ  and  Canθₛ⊆Canₛ-[]env-negative, which prove
that the result of Canθ is always a subset of the result of Can 
(mainly by the mononicity of Can and Canθ)

Variants are also proved for Canθₖ and Canθₛₕ


-}

open import Esterel.Lang.CanFunction.Monotonic
open import Esterel.Lang.CanFunction.CanThetaVisit
  using (Canθ-visit ; Canθ-visit≡Canθ ; Canθₛ-visit ; Canθₛ-visit-rec)
open import Esterel.Lang.CanFunction
  using (Can ; Canθ ; Canₛ ; Canθₛ ; [S]-env-build ; [S]-env)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Signal.Ordering as SO
  using (_⊑_)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)
open import utility
open import Esterel.Environment as Env
  using (Env ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap ; isSig∈)
open Env.Env
open import Esterel.Lang
  using (Term)
open Term


open import Data.Sublist as SL
  using (elem ; empty ; Sublist ; sublist)
  
open import Function
  using (_$_ ; _∘_)
open import Relation.Binary.PropositionalEquality
  using (refl ; _≡_ ; subst ; cong ; sym)
open import Data.Product as Prod
  using (Σ ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_ ; ∃-syntax ; Σ-syntax)
open import Data.List as List
  using ([])
open import Level
open import Relation.Binary
  using (Rel)
open import Relation.Nullary
  using (¬_)

open import Data.List.Any.Properties as AnyP
  using (++⁻)
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ)

Canθₛ-visit⊆Canₛ-rec : ∀{off} θ θu p
  → (sl : Sublist (SigMap.keys+∈ (Env.sig θ)) off)
  → ∀ S
  → (Signal.unwrap S) ∈ Canθₛ-visit-rec (Env.sig θ) p sl θu
  → (Signal.unwrap S) ∈ Canₛ p θu
Canθₛ-visit⊆Canₛ-rec θ θu p empty = {!!}
Canθₛ-visit⊆Canₛ-rec θ θu p (elem n n<l sl) = {!!}

Canθₛ-visit-step-rec : ∀{off} θ θu p
  → (sl : Sublist (SigMap.keys+∈ (Env.sig θ)) off)
  → θ ⊑θ θu
  → ∀ S
  → (Signal.unwrap S) ∈ Canθₛ-visit-rec (Env.sig θ) p sl θu
  → (Signal.unwrap S) ∈ Canθₛ-visit-rec (Env.sig θ) p sl θ 
Canθₛ-visit-step-rec θ θu p empty s s∈ = {!!}
Canθₛ-visit-step-rec θ θu p (elem n n<l sl) s s∈ = {!!}


Canθₛ-visit-step : ∀ θ p S →
  (Signal.unwrap S) ∈ Canθₛ-visit p (Env.sig θ) Env.[]env →
  (Signal.unwrap S) ∈ Canθₛ-visit p (Env.sig θ) θ 
Canθₛ-visit-step θ p s s∈ = {!Canθₛ-visit-θ-monotonic-rec !}

Canθₛ-visit⊆Canₛ : ∀ θ p S →
  (Signal.unwrap S) ∈ Canθₛ-visit p (Env.sig θ) Env.[]env →
  (Signal.unwrap S) ∈ Canₛ p θ
Canθₛ-visit⊆Canₛ θ p S S∈
 rewrite Env.←-self-identity θ
 =  Canθₛ-visit⊆Canₛ-rec θ θ p sl S
     $ Canθₛ-visit-step θ p S S∈  
    where sl = (sublist (SigMap.keys+∈ (Env.sig θ)))

Canθₛ⊆Canₛ-[]env : ∀ θ p S →
  (Signal.unwrap S) ∈ Canθₛ (Env.sig θ) 0 p Env.[]env →
  (Signal.unwrap S) ∈ Canₛ p θ
Canθₛ⊆Canₛ-[]env θ p
  = {!canθₛ-mergeʳ (Env.sig θ) Env.[]env p θ ?  !}

Canθₛ⊆Canₛ-[]env-negative : ∀ θ p S →
  (Signal.unwrap S) ∉ Canₛ p θ →
  (Signal.unwrap S) ∉ Canθₛ (Env.sig θ) 0 p Env.[]env
Canθₛ⊆Canₛ-[]env-negative θ p S ∉f
   =  ∉f ∘ Canθₛ⊆Canₛ-[]env θ p S
