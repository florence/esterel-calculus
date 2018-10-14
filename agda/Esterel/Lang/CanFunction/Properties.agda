module Esterel.Lang.CanFunction.Properties where

{-
Basic properties of the Can function and utilities used in the reasoning,
such as Can does not look at shared variables and sequential variables; Can can
only output free variables; Can will capture free emit S and s ⇐ e (and more).
-}
open import Esterel.Lang.CanFunction.Base hiding ([_↦_]) public

{-
The equivalent "goodness" of can w.r.t. the rmerge reduction. Specifically, here
are the main lemmas:

  can-irr : ∀ {BV} {FV} θ₁ θ₂ q →
    CorrectBinding q BV FV →
    (distinct' (proj₁ FV) (proj₁ (Dom θ₂))) →
    Can q θ₁ ≡ Can q (θ₁ ← θ₂)
  can-irr θ₁ θ₂ q cbq FV≠Domθ₂

  canθₛ-mergeˡ : ∀ {E θ' r p BV FV} sigs θ →
    CorrectBinding p BV FV →
    p ≐ E ⟦ ρ θ' · r ⟧e →
    ∀ S' →
      Signal.unwrap S' ∉ SigMap.keys (Env.sig θ') →
      Signal.unwrap S' ∈ Canθₛ (SigMap.union sigs (Env.sig θ')) 0 (E ⟦ r ⟧e) θ →
      Signal.unwrap S' ∈ Canθₛ sigs 0 p θ

  canθₛ-mergeʳ : ∀ sigs θ' r θ →
    distinct' (proj₁ (Dom θ)) (SigMap.keys sigs) →
    ∀ S' →
      Signal.unwrap S' ∈ Canθₛ (SigMap.union sigs (Env.sig θ')) 0 r θ →
      Signal.unwrap S' ∈ Canθₛ (Env.sig θ') 0 r θ

These lemma says that when updating or extending the environent,
if the program does not refer to the updated variables, then
the Can function will not change and the Canθ function will
have some sort of monotonicity.

-}
open import Esterel.Lang.CanFunction.MergePotentialRuleCan public
open import Esterel.Lang.CanFunction.MergePotentialRuleTheta public

{-
The subset "goodness" of can w.r.t. other ρθ-reductions. For each of the 7 non-merge
ρθ-reductions, there are two corresponding Can subset lemmas.
-}
open import Esterel.Lang.CanFunction.NonMergePotentialRules public

{-
The compatible closure context C⟦_⟧c respects the monotonicity of the potential
function. For example, Can is monotonic w.r.t. to _sn⟶₁_, hence also _sn⟶_ by the
lemmas in this file.
-}
open import Esterel.Lang.CanFunction.Plug public

open import utility

open import Esterel.Lang
  using (Term ; emit ; _⇐_)
open import Esterel.Context
  using (_≐_⟦_⟧e)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Lang.CanFunction
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
