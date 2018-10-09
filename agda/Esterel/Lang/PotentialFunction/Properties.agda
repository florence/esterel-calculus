module Esterel.Lang.PotentialFunction.Properties where

{-
Note:
(0) TOOD: fix comments (all are outdated)

(1) CanThetaContinuation is excluded from the Properties file since it is not
    considered as properties of the Can[θ] functions but rather tools for
    reasoning about the Can[θ] functions. Perhaps at some point we will
    replace Canθ with a call to Canθ' though.

(2) SetSigMonotonic is re-exported through Base, not directly in this file.
-}

{-
Basic properties of the potential function and utilities used in the reasoning,
such as Can does not look at shared variables and sequential variables; Can can
only output free variables; Can will capture free emit S and s ⇐ e (and more).
-}
open import Esterel.Lang.PotentialFunction.Base hiding ([_↦_]) public

{-
The equivalent "goodness" of can w.r.t. the rmerge reduction. Specifically, here
are the main lemmas:

  can-irr : ∀ {BV} {FV} θ₁ θ₂ q →
    CorrectBinding q BV FV →
    (distinct' (proj₁ FV) (proj₁ (Dom θ₂))) →
    Can q θ₁ ≡ Can q (θ₁ ← θ₂)
  can-irr θ₁ θ₂ q cbq FV≠Domθ₂

  can-rho-irr : ∀ {BV FV} θ₁ θ₂ p E →
    CorrectBinding (E ⟦ ρ θ₂ · p ⟧e) BV FV →
    Canₖ (E ⟦ ρ θ₂ · p ⟧e) θ₁ ≡ Canₖ (E ⟦ p ⟧e) (θ₁ ← θ₂)

  canₛ-mergeˡ : ∀ {θ₁ r θ₂ p BV FV E} S →
    r ≐ E ⟦ ρ θ₂ · p  ⟧e →
    ¬ (Env.isSig∈ S θ₂) →
    CorrectBinding r BV FV →
    Signal.unwrap S ∈ Canₛ (E ⟦ p ⟧e) (θ₁ ← θ₂) →
    (Signal.unwrap S ∈ Canₛ r θ₁)

  canₛ-mergeʳ : ∀ θ θ' p →
    ∀ S →
      Signal.unwrap S ∈ Canₛ p (θ ← θ') →
      Signal.unwrap S ∈ Canₛ p θ'

  (and similar ones for Canₛₕ)

This file contains the lemma that uses "θ accumulating trick" in the proof.
-}
open import Esterel.Lang.PotentialFunction.MergePotentialRuleCan public
open import Esterel.Lang.PotentialFunction.MergePotentialRuleTheta public

{-
The subset "goodness" of can w.r.t. other ρθ-reductions. For each of the 7 non-merge
ρθ-reductions, there are two corresponding Can subset lemmas.
-}
open import Esterel.Lang.PotentialFunction.NonMergePotentialRules public

{-
The compatible closure context C⟦_⟧c respects the monotonicity of the potential
function. For example, Can is monotonic w.r.t. to _sn⟶₁_, hence also _sn⟶_ by the
lemmas in this file.
-}
open import Esterel.Lang.PotentialFunction.Plug public

open import utility

open import Esterel.Lang
  using (Term ; emit ; _⇐_)
open import Esterel.Context
  using (_≐_⟦_⟧e)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Lang.PotentialFunction
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)

open import Function
  using (_∘_)
open import Relation.Nullary
  using (¬_)

-- old lemmas; left here for backward compatibility
CanₛₕAgreesWithE : ∀{θ s e E} → (p : Term) → SharedVar.unwrap s ∉ Canₛₕ p θ → ¬ (p ≐ E ⟦ s ⇐ e ⟧e)
CanₛₕAgreesWithE {θ} p = (_∘ canₛₕ-capture-set-shared θ)

CanₛAgreesWithE : ∀{θ S E} → (p : Term) → Signal.unwrap S ∉ Canₛ p θ → ¬ (p ≐ E ⟦ emit S ⟧e)
CanₛAgreesWithE {θ} p = (_∘ canₛ-capture-emit-signal θ)
