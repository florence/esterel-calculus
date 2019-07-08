{-

The module CanThetaContinuation contains the continuation-passing
variant of Canθ, which is used as a tool to simplify Canθ-Can
expressions.

The lemmas are mainly about the function Canθ' defined by the equation

    unfold : ∀ sigs S'' p θ →
         Canθ sigs S'' p θ ≡ Canθ' sigs S'' (Can p) θ

The main property proved here is that the search function
Canθ is distributive over the environment:

    canθ'-←-distribute : ∀ sigs sigs' S'' r θ →
      Canθ (SigMap.union sigs sigs') S'' r θ ≡
      Canθ' sigs S'' (Canθ sigs' S'' r) θ

Other properties about how the search is performed are:

    canθ'-inner-shadowing-irr : ∀ sigs S'' sigs' p S status θ →
      S ∈ SigMap.keys sigs' →
        Canθ' sigs S'' (Canθ sigs' 0 p) (θ ← [ (S ₛ) ↦ status ]) ≡
        Canθ' sigs S'' (Canθ sigs' 0 p) θ

    canθ'-search-acc : ∀ sigs S κ θ →
      ∀ S'' status →
        S'' ∉ map (_+_ S)  (SigMap.keys sigs) →
        Canθ' sigs S  κ  (θ ← [ (S'' ₛ) ↦ status ]) ≡
        Canθ' sigs S (κ ∘ (_← [ (S'' ₛ) ↦ status ])) θ

-}
module Esterel.Lang.CanFunction.CanThetaContinuation where

open import utility

open import utility
  renaming (_U̬_ to _∪_ ; _|̌_ to _-_)

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.CanFunction
open import Esterel.Lang.CanFunction.Base
open import Esterel.Context
  using (EvaluationContext1 ; EvaluationContext ; _⟦_⟧e ; _≐_⟦_⟧e)
open import Esterel.Context.Properties
  using (plug ; unplug)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap; []env)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)

open EvaluationContext1
open _≐_⟦_⟧e

open import Data.Bool
  using (Bool ; not ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; [] ; _∷_ ; _++_ ; map ; concatMap ; foldr)
open import Data.List.Properties
  using (map-id)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using ()
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ)
open import Data.Maybe
  using (Maybe ; maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_)
open import Data.Nat.Properties.Simple
  using (+-comm)
open import Data.Product
  using (Σ ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; id ; _∋_ ; _$_)
open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; subst ; module ≡-Reasoning)

open ListSet Data.Nat._≟_
  using (set-subtract ; set-subtract-[] ; set-subtract-split ; set-subtract-merge
       ; set-subtract-notin
       ; set-remove ; set-remove-mono-∈ ; set-remove-removed ; set-remove-not-removed
       ; set-subtract-[a]≡set-remove)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open ≡-Reasoning

-- equation: Canθ sig S'' p θ = Canθ' sig S'' (Can p) θ
Canθ'   : SigMap.Map Signal.Status → ℕ →
  (Env → SigSet.ST × CodeSet.ST × ShrSet.ST) →
  Env → SigSet.ST × CodeSet.ST × ShrSet.ST
Canθ' [] S κ θ = κ θ
Canθ' (nothing             ∷ sig') S κ θ = Canθ' sig' (suc S) κ θ
Canθ' (just Signal.present ∷ sig') S κ θ = Canθ' sig' (suc S) κ (θ ← [S]-env-present (S ₛ))
Canθ' (just Signal.absent  ∷ sig') S κ θ = Canθ' sig' (suc S) κ (θ ← [S]-env-absent (S ₛ))
Canθ' (just Signal.unknown ∷ sig') S κ θ with
  any (_≟_ S) (proj₁ (Canθ' sig' (suc S) κ (θ ← [S]-env (S ₛ))))
... | yes S∈can-p-θ←[S] = Canθ' sig' (suc S) κ (θ ← [S]-env (S ₛ))
... | no  S∉can-p-θ←[S] = Canθ' sig' (suc S) κ (θ ← [S]-env-absent (S ₛ))


unfold : ∀ sigs S'' p θ → Canθ sigs S'' p θ ≡ Canθ' sigs S'' (Can p) θ
unfold [] S'' p θ = refl
unfold (nothing ∷ sigs) S'' p θ = unfold sigs (suc S'') p θ
unfold (just Signal.present ∷ sigs) S'' p θ =
  unfold sigs (suc S'') p (θ ← [S]-env-present (S'' ₛ))
unfold (just Signal.absent ∷ sigs) S'' p θ =
  unfold sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ))
unfold (just Signal.unknown ∷ sigs) S'' p θ
  with any (_≟_ S'') (proj₁ (Canθ  sigs (suc S'') p       (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (Can p) (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ-sigs-θ←[S''] | yes S''∈canθ'-sigs-θ←[S''] =
  unfold sigs (suc S'') p (θ ← [S]-env (S'' ₛ))
... | no  S''∉canθ-sigs-θ←[S''] | no  S''∉canθ'-sigs-θ←[S''] =
  unfold sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ))
... | yes S''∈canθ-sigs-θ←[S''] | no  S''∉canθ'-sigs-θ←[S'']
  rewrite unfold sigs (suc S'') p (θ ← [S]-env (S'' ₛ))
  = ⊥-elim (S''∉canθ'-sigs-θ←[S''] S''∈canθ-sigs-θ←[S''])
... | no  S''∉canθ-sigs-θ←[S''] | yes S''∈canθ'-sigs-θ←[S'']
  rewrite unfold sigs (suc S'') p (θ ← [S]-env (S'' ₛ))
  = ⊥-elim (S''∉canθ-sigs-θ←[S''] S''∈canθ'-sigs-θ←[S''])


canθ'-cong : ∀ sigs S'' κ κ' θ →
  (∀ θ* → κ θ* ≡ κ' θ*) →
  Canθ' sigs S'' κ θ ≡ Canθ' sigs S'' κ' θ
canθ'-cong [] S'' κ κ' θ κ≗κ' = κ≗κ' θ
canθ'-cong (nothing ∷ sigs) S'' κ κ' θ κ≗κ' =
  canθ'-cong sigs (suc S'') κ κ' θ κ≗κ'
canθ'-cong (just Signal.present ∷ sigs) S'' κ κ' θ κ≗κ' =
  canθ'-cong sigs (suc S'') κ κ' (θ ← [S]-env-present (S'' ₛ)) κ≗κ'
canθ'-cong (just Signal.absent ∷ sigs) S'' κ κ' θ κ≗κ' =
  canθ'-cong sigs (suc S'') κ κ' (θ ← [S]-env-absent (S'' ₛ)) κ≗κ'
canθ'-cong (just Signal.unknown ∷ sigs) S'' κ κ' θ κ≗κ'
  with any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ  (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ' (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-sigs-κ-θ←[S''] | yes S''∈canθ'-sigs-κ'-θ←[S''] =
  canθ'-cong sigs (suc S'') κ κ' (θ ← [S]-env (S'' ₛ)) κ≗κ'
... | no  S''∉canθ'-sigs-κ-θ←[S''] | no  S''∉canθ'-sigs-κ'-θ←[S''] =
  canθ'-cong sigs (suc S'') κ κ' (θ ← [S]-env-absent (S'' ₛ)) κ≗κ'
... | yes S''∈canθ'-sigs-κ-θ←[S''] | no  S''∉canθ'-sigs-κ'-θ←[S'']
  rewrite canθ'-cong sigs (suc S'') κ κ' (θ ← [S]-env (S'' ₛ)) κ≗κ'
  = ⊥-elim (S''∉canθ'-sigs-κ'-θ←[S''] S''∈canθ'-sigs-κ-θ←[S''])
... | no  S''∉canθ'-sigs-κ-θ←[S''] | yes S''∈canθ'-sigs-κ'-θ←[S'']
  rewrite canθ'-cong sigs (suc S'') κ κ' (θ ← [S]-env (S'' ₛ)) κ≗κ'
  = ⊥-elim (S''∉canθ'-sigs-κ-θ←[S''] S''∈canθ'-sigs-κ'-θ←[S''])


canθₛ'-cong : ∀ sigs S'' κ κ' θ →
  (∀ θ* → proj₁ (κ θ*) ≡ proj₁ (κ' θ*)) →
  proj₁ (Canθ' sigs S'' κ θ) ≡ proj₁ (Canθ' sigs S'' κ' θ)
canθₛ'-cong [] S'' κ κ' θ κ≗κ' = κ≗κ' θ
canθₛ'-cong (nothing ∷ sigs) S'' κ κ' θ κ≗κ' =
  canθₛ'-cong sigs (suc S'') κ κ' θ κ≗κ'
canθₛ'-cong (just Signal.present ∷ sigs) S'' κ κ' θ κ≗κ' =
  canθₛ'-cong sigs (suc S'') κ κ' (θ ← [S]-env-present (S'' ₛ)) κ≗κ'
canθₛ'-cong (just Signal.absent ∷ sigs) S'' κ κ' θ κ≗κ' =
  canθₛ'-cong sigs (suc S'') κ κ' (θ ← [S]-env-absent (S'' ₛ)) κ≗κ'
canθₛ'-cong (just Signal.unknown ∷ sigs) S'' κ κ' θ κ≗κ'
  with any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ  (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ' (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-sigs-κ-θ←[S''] | yes S''∈canθ'-sigs-κ'-θ←[S''] =
  canθₛ'-cong sigs (suc S'') κ κ' (θ ← [S]-env (S'' ₛ)) κ≗κ'
... | no  S''∉canθ'-sigs-κ-θ←[S''] | no  S''∉canθ'-sigs-κ'-θ←[S''] =
  canθₛ'-cong sigs (suc S'') κ κ' (θ ← [S]-env-absent (S'' ₛ)) κ≗κ'
... | yes S''∈canθ'-sigs-κ-θ←[S''] | no  S''∉canθ'-sigs-κ'-θ←[S'']
  rewrite canθₛ'-cong sigs (suc S'') κ κ' (θ ← [S]-env (S'' ₛ)) κ≗κ'
  = ⊥-elim (S''∉canθ'-sigs-κ'-θ←[S''] S''∈canθ'-sigs-κ-θ←[S''])
... | no  S''∉canθ'-sigs-κ-θ←[S''] | yes S''∈canθ'-sigs-κ'-θ←[S'']
  rewrite canθₛ'-cong sigs (suc S'') κ κ' (θ ← [S]-env (S'' ₛ)) κ≗κ'
  = ⊥-elim (S''∉canθ'-sigs-κ-θ←[S''] S''∈canθ'-sigs-κ'-θ←[S''])


canθ'-map-comm : ∀ f sigs S κ θ →
  Canθ' sigs S (map-second f ∘ κ) θ ≡ map-second f (Canθ' sigs S κ θ)
canθ'-map-comm f [] S κ θ = refl
canθ'-map-comm f (nothing ∷ sigs) S κ θ =
  canθ'-map-comm f sigs (suc S) κ θ
canθ'-map-comm f (just Signal.present ∷ sigs) S κ θ =
  canθ'-map-comm f sigs (suc S) κ (θ ← [S]-env-present (S ₛ))
canθ'-map-comm f (just Signal.absent ∷ sigs) S κ θ =
  canθ'-map-comm f sigs (suc S) κ (θ ← [S]-env-absent (S ₛ))
canθ'-map-comm f (just Signal.unknown ∷ sigs) S κ θ
  with any (_≟_ S) (proj₁ (Canθ' sigs (suc S) (map-second f ∘ κ) (θ ← [S]-env (S ₛ))))
     | any (_≟_ S) (proj₁ (Canθ' sigs (suc S) κ (θ ← [S]-env (S ₛ))))
... | yes S∈canθ'-sigs-f∘κ-θ←[S] | yes S∈canθ'-sigs-κ-θ←[S] =
  canθ'-map-comm f sigs (suc S) κ (θ ← [S]-env (S ₛ))
... | no  S∉canθ'-sigs-f∘κ-θ←[S] | no  S∉canθ'-sigs-κ-θ←[S] =
  canθ'-map-comm f sigs (suc S) κ (θ ← [S]-env-absent (S ₛ))
... | yes S∈canθ'-sigs-f∘κ-θ←[S] | no  S∉canθ'-sigs-κ-θ←[S]
  rewrite canθ'-map-comm f sigs (suc S) κ (θ ← [S]-env (S ₛ))
  = ⊥-elim (S∉canθ'-sigs-κ-θ←[S] S∈canθ'-sigs-f∘κ-θ←[S])
... | no  S∉canθ'-sigs-f∘κ-θ←[S] | yes S∈canθ'-sigs-κ-θ←[S]
  rewrite canθ'-map-comm f sigs (suc S) κ (θ ← [S]-env (S ₛ))
  = ⊥-elim (S∉canθ'-sigs-f∘κ-θ←[S] S∈canθ'-sigs-κ-θ←[S])


canθ'ₛ-add-sig-monotonic : ∀ sigs S'' κ θ S status →
  (∀ θ S status S' →
    S' ∈ proj₁ (κ (θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty)) →
    S' ∈ proj₁ (κ (θ ← [S]-env S))) →
  ∀ S' →
    S' ∈ proj₁ (Canθ' sigs S'' κ (θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty)) →
    S' ∈ proj₁ (Canθ' sigs S'' κ (θ ← [S]-env S))
canθ'ₛ-add-sig-monotonic [] S'' κ θ S status κ-add-sig-monotonic
  S' S'∈canθ'-sigs-p-θ←[S↦status] =
  κ-add-sig-monotonic θ S status S' S'∈canθ'-sigs-p-θ←[S↦status]
canθ'ₛ-add-sig-monotonic (nothing ∷ sigs) S'' κ θ S status
  κ-add-sig-monotonic S' S'∈canθ'-sigs-p-θ←[S↦status] =
  canθ'ₛ-add-sig-monotonic sigs (suc S'') κ θ S status
    κ-add-sig-monotonic S' S'∈canθ'-sigs-p-θ←[S↦status]
canθ'ₛ-add-sig-monotonic (just x ∷ sigs) S'' κ θ S status
  κ-add-sig-monotonic S' S'∈canθ'-sigs-p-θ←[S↦status] with Signal.unwrap S ≟ S''
canθ'ₛ-add-sig-monotonic (just Signal.present ∷ sigs) S'' κ θ S status
  κ-add-sig-monotonic S' S'∈canθ'-sigs-p-θ←[S↦status] | yes refl
  rewrite Env.sig-single-←-←-overwrite θ (S'' ₛ) Signal.unknown Signal.present
        | Env.sig-single-←-←-overwrite θ (S'' ₛ) status         Signal.present
  = S'∈canθ'-sigs-p-θ←[S↦status]
canθ'ₛ-add-sig-monotonic (just Signal.absent ∷ sigs) S'' κ θ S status
  κ-add-sig-monotonic S' S'∈canθ'-sigs-p-θ←[S↦status] | yes refl
  rewrite Env.sig-single-←-←-overwrite θ (S'' ₛ) Signal.unknown Signal.absent
        | Env.sig-single-←-←-overwrite θ (S'' ₛ) status         Signal.absent
  = S'∈canθ'-sigs-p-θ←[S↦status]
canθ'ₛ-add-sig-monotonic (just Signal.unknown ∷ sigs) S'' κ θ S status
  κ-add-sig-monotonic S' S'∈canθ'-sigs-p-θ←[S↦status] | yes refl
  with any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ ((θ ← [S]-env (S'' ₛ)) ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ ((θ ← [ (S'' ₛ) ↦ status ]) ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-sigs-κ-θ←[S''↦unknown]←[S''] | yes S''∈canθ'-sigs-κ-θ←[S''↦status]←[S'']
  rewrite Env.sig-single-←-←-overwrite θ (S'' ₛ) Signal.unknown Signal.unknown
        | Env.sig-single-←-←-overwrite θ (S'' ₛ) status         Signal.unknown
  = S'∈canθ'-sigs-p-θ←[S↦status]
... | no  S''∉canθ'-sigs-κ-θ←[S''↦unknown]←[S''] | no  S''∉canθ'-sigs-κ-θ←[S''↦status]←[S'']
  rewrite Env.sig-single-←-←-overwrite θ (S'' ₛ) Signal.unknown Signal.absent
        | Env.sig-single-←-←-overwrite θ (S'' ₛ) status         Signal.absent
  = S'∈canθ'-sigs-p-θ←[S↦status]
... | yes S''∈canθ'-sigs-κ-θ←[S''↦unknown]←[S''] | no  S''∉canθ'-sigs-κ-θ←[S''↦status]←[S'']
  rewrite Env.sig-single-←-←-overwrite θ (S'' ₛ) Signal.unknown Signal.unknown
        | Env.sig-single-←-←-overwrite θ (S'' ₛ) status         Signal.unknown
  = ⊥-elim (S''∉canθ'-sigs-κ-θ←[S''↦status]←[S'']
              S''∈canθ'-sigs-κ-θ←[S''↦unknown]←[S''])
... | no  S''∉canθ'-sigs-κ-θ←[S''↦unknown]←[S''] | yes S''∈canθ'-sigs-κ-θ←[S''↦status]←[S'']
  rewrite Env.sig-single-←-←-overwrite θ (S'' ₛ) Signal.unknown Signal.unknown
        | Env.sig-single-←-←-overwrite θ (S'' ₛ) status         Signal.unknown
  = ⊥-elim (S''∉canθ'-sigs-κ-θ←[S''↦unknown]←[S'']
              S''∈canθ'-sigs-κ-θ←[S''↦status]←[S''])
canθ'ₛ-add-sig-monotonic (just Signal.present ∷ sigs) S'' κ θ S status
  κ-add-sig-monotonic S' S'∈canθ'-sigs-p-θ←[S↦status] | no S≢S''
  rewrite Env.←-assoc-comm θ ([S]-env S) ([S]-env-present (S'' ₛ))
            (Env.sig-single-noteq-distinct S Signal.unknown
              (S'' ₛ) Signal.present S≢S'')
  = canθ'ₛ-add-sig-monotonic sigs (suc S'') κ
      (θ ← [S]-env-present (S'' ₛ)) S status κ-add-sig-monotonic S'
      (subst (S' ∈_)
        (cong (proj₁ ∘ Canθ' sigs (suc S'') κ)
          (Env.←-assoc-comm θ [ S ↦ status ] ([S]-env-present (S'' ₛ))
              (Env.sig-single-noteq-distinct S status
                (S'' ₛ) Signal.present S≢S'')))
        S'∈canθ'-sigs-p-θ←[S↦status])
canθ'ₛ-add-sig-monotonic (just Signal.absent ∷ sigs) S'' κ θ S status
  κ-add-sig-monotonic S' S'∈canθ'-sigs-p-θ←[S↦status] | no S≢S''
  rewrite Env.←-assoc-comm θ ([S]-env S) ([S]-env-absent (S'' ₛ))
            (Env.sig-single-noteq-distinct S Signal.unknown
              (S'' ₛ) Signal.absent S≢S'')
  = canθ'ₛ-add-sig-monotonic sigs (suc S'') κ
      (θ ← [S]-env-absent (S'' ₛ)) S status κ-add-sig-monotonic S'
      (subst (S' ∈_)
        (cong (proj₁ ∘ Canθ' sigs (suc S'') κ)
          (Env.←-assoc-comm θ [ S ↦ status ] ([S]-env-absent (S'' ₛ))
              (Env.sig-single-noteq-distinct S status
                (S'' ₛ) Signal.absent S≢S'')))
        S'∈canθ'-sigs-p-θ←[S↦status])
canθ'ₛ-add-sig-monotonic (just Signal.unknown ∷ sigs) S'' κ θ S status
  κ-add-sig-monotonic S' S'∈canθ'-sigs-p-θ←[S↦status] | no S≢S''
  with any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ ((θ ← [S]-env S) ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ ((θ ← [ S ↦ status ]) ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-sigs-κ-θ←[S↦unknown]←[S''] | yes S''∈canθ'-sigs-κ-θ←[S↦status]←[S'']
  rewrite Env.←-assoc-comm θ ([S]-env S) ([S]-env (S'' ₛ))
            (Env.sig-single-noteq-distinct S Signal.unknown
              (S'' ₛ) Signal.unknown S≢S'')
  = canθ'ₛ-add-sig-monotonic sigs (suc S'') κ
      (θ ← [S]-env (S'' ₛ)) S status κ-add-sig-monotonic S'
      (subst (S' ∈_)
        (cong (proj₁ ∘ Canθ' sigs (suc S'') κ)
          (Env.←-assoc-comm θ [ S ↦ status ] ([S]-env (S'' ₛ))
              (Env.sig-single-noteq-distinct S status
                (S'' ₛ) Signal.unknown S≢S'')))
        S'∈canθ'-sigs-p-θ←[S↦status])
... | no  S''∉canθ'-sigs-κ-θ←[S↦unknown]←[S''] | no  S''∉canθ'-sigs-κ-θ←[S↦status]←[S'']
  rewrite Env.←-assoc-comm θ ([S]-env S) ([S]-env-absent (S'' ₛ))
            (Env.sig-single-noteq-distinct S Signal.unknown
              (S'' ₛ) Signal.absent S≢S'')
  = canθ'ₛ-add-sig-monotonic sigs (suc S'') κ
      (θ ← [S]-env-absent (S'' ₛ)) S status κ-add-sig-monotonic S'
      (subst (S' ∈_)
        (cong (proj₁ ∘ Canθ' sigs (suc S'') κ)
          (Env.←-assoc-comm θ [ S ↦ status ] ([S]-env-absent (S'' ₛ))
              (Env.sig-single-noteq-distinct S status
                (S'' ₛ) Signal.absent S≢S'')))
        S'∈canθ'-sigs-p-θ←[S↦status])
... | yes S''∈canθ'-sigs-κ-θ←[S↦unknown]←[S''] | no  S''∉canθ'-sigs-κ-θ←[S↦status]←[S'']
  rewrite Env.←-assoc-comm θ ([S]-env S) ([S]-env (S'' ₛ))
            (Env.sig-single-noteq-distinct S Signal.unknown
              (S'' ₛ) Signal.unknown S≢S'')
  = canθ'ₛ-add-sig-monotonic sigs (suc S'') κ (θ ← [S]-env (S'' ₛ))
      S status κ-add-sig-monotonic S'
      (subst (S' ∈_)
        (cong (proj₁ ∘ Canθ' sigs (suc S'') κ)
          (Env.←-assoc-comm θ [ S ↦ status ] ([S]-env (S'' ₛ))
            (Env.sig-single-noteq-distinct S status
              (S'' ₛ) Signal.unknown S≢S'')))
        (canθ'ₛ-add-sig-monotonic sigs (suc S'') κ (θ ← [ S ↦ status ])
          (S'' ₛ) Signal.absent κ-add-sig-monotonic
            S' S'∈canθ'-sigs-p-θ←[S↦status]))
... | no  S''∉canθ'-sigs-κ-θ←[S↦unknown]←[S''] | yes S''∈canθ'-sigs-κ-θ←[S↦status]←[S'']
  rewrite Env.←-assoc-comm θ ([S]-env S) ([S]-env (S'' ₛ))
            (Env.sig-single-noteq-distinct S Signal.unknown
              (S'' ₛ) Signal.unknown S≢S'')
  = ⊥-elim
    (S''∉canθ'-sigs-κ-θ←[S↦unknown]←[S'']
      (canθ'ₛ-add-sig-monotonic sigs (suc S'') κ (θ ← [S]-env (S'' ₛ)) S
         status κ-add-sig-monotonic S''
         (subst (S'' ∈_)
           (cong (proj₁ ∘ Canθ' sigs (suc S'') κ)
             (Env.←-assoc-comm θ [ S ↦ status ] ([S]-env (S'' ₛ))
               (Env.sig-single-noteq-distinct S status
                 (S'' ₛ) Signal.unknown S≢S'')))
           S''∈canθ'-sigs-κ-θ←[S↦status]←[S''])))


canθ'ₛ-canθ-add-sig-monotonic : ∀ sigs S sigs' S' p θ S''' status →
  ∀ S'' →
    S'' ∈ proj₁ (Canθ' sigs S (Canθ sigs' S' p)
                  (θ ← Θ SigMap.[ S''' ↦ status ] ShrMap.empty VarMap.empty)) →
    S'' ∈ proj₁ (Canθ' sigs S (Canθ sigs' S' p)
                  (θ ← [S]-env S'''))
canθ'ₛ-canθ-add-sig-monotonic sigs S sigs' S' p θ S''' status
  S'' S''∈canθ'-sigs-p-θ←[S↦status] =
  canθ'ₛ-add-sig-monotonic sigs S (Canθ sigs' S' p) θ S''' status
    (canθₛ-add-sig-monotonic sigs' S' p)
    S'' S''∈canθ'-sigs-p-θ←[S↦status]


canθ'ₛ-subset-lemma : ∀ sigs S'' κ κ' θ →
  (∀ θ' S → S ∈ proj₁ (κ θ') → S ∈ proj₁ (κ' θ')) →
  (∀ θ S status S' →
    S' ∈ proj₁ (κ' (θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty)) →
    S' ∈ proj₁ (κ' (θ ← [S]-env S))) →
  ∀ S → S ∈ proj₁ (Canθ' sigs S'' κ θ) → S ∈ proj₁ (Canθ' sigs S'' κ' θ)
canθ'ₛ-subset-lemma [] S'' κ κ' θ κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ =
  κ⊆κ' θ S S∈canθ'-κ-θ
canθ'ₛ-subset-lemma (nothing ∷ sigs) S'' κ κ' θ
  κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ =
  canθ'ₛ-subset-lemma sigs (suc S'') κ κ' θ κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ
canθ'ₛ-subset-lemma (just Signal.present ∷ sigs) S'' κ κ' θ
  κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ =
  canθ'ₛ-subset-lemma sigs (suc S'') κ κ' (θ ← [S]-env-present (S'' ₛ))
    κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ
canθ'ₛ-subset-lemma (just Signal.absent ∷ sigs) S'' κ κ' θ
  κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ =
  canθ'ₛ-subset-lemma sigs (suc S'') κ κ' (θ ← [S]-env-absent (S'' ₛ)) κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ
canθ'ₛ-subset-lemma (just Signal.unknown ∷ sigs) S'' κ κ' θ
  κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ
  with any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ  (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') κ' (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-κ-θ' | yes S''∈canθ-κ'-θ' =
  canθ'ₛ-subset-lemma sigs (suc S'') κ κ' (θ ← [S]-env (S'' ₛ))
    κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ
... | no  S''∉canθ'-κ-θ' | no  S''∉canθ-q-θ' =
  canθ'ₛ-subset-lemma sigs (suc S'') κ κ' (θ ← [S]-env-absent (S'' ₛ))
    κ⊆κ' κ'-add-sig-monotonic S S∈canθ'-κ-θ
... | yes S''∈canθ'-κ-θ' | no  S''∉canθ-q-θ' =
  ⊥-elim
    (S''∉canθ-q-θ'
      (canθ'ₛ-subset-lemma sigs (suc S'') κ κ' (θ ← [S]-env (S'' ₛ)) κ⊆κ'
        κ'-add-sig-monotonic S'' S''∈canθ'-κ-θ'))
... | no  S''∉canθ'-κ-θ' | yes S''∈canθ-κ'-θ' =
  canθ'ₛ-add-sig-monotonic sigs (suc S'') κ' θ (S'' ₛ) Signal.absent
    κ'-add-sig-monotonic S
    (canθ'ₛ-subset-lemma sigs (suc S'') κ κ' (θ ← [S]-env-absent (S'' ₛ)) κ⊆κ'
      κ'-add-sig-monotonic S S∈canθ'-κ-θ)


canθ'-inner-shadowing-irr' : ∀ sigs S'' sigs' p S status θ θo →
  S ∈ SigMap.keys sigs' →
    Canθ' sigs S'' (Canθ sigs' 0 p) ((θ ← [ (S ₛ) ↦ status ]) ← θo) ≡
    Canθ' sigs S'' (Canθ sigs' 0 p) (θ ← θo)
canθ'-inner-shadowing-irr' [] S'' sigs' p S status θ θo S∈sigs'
  rewrite sym (map-id (SigMap.keys sigs'))
  = canθ-shadowing-irr' sigs' 0 p S status θ θo S∈sigs'
canθ'-inner-shadowing-irr' (nothing ∷ sigs) S'' sigs' p S status θ θo S∈sigs' = canθ'-inner-shadowing-irr' sigs (suc S'') sigs' p S status θ θo S∈sigs'
canθ'-inner-shadowing-irr' (just Signal.present ∷ sigs) S'' sigs' p S status θ θo S∈sigs'
  rewrite sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env-present (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env-present (S'' ₛ)))
  = canθ'-inner-shadowing-irr' sigs (suc S'') sigs' p S status θ (θo ← ([S]-env-present (S'' ₛ))) S∈sigs'
canθ'-inner-shadowing-irr' (just Signal.absent ∷ sigs) S'' sigs' p S status θ θo S∈sigs'
  rewrite sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env-absent (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env-absent (S'' ₛ)))
  = canθ'-inner-shadowing-irr' sigs (suc S'') sigs' p S status θ (θo ← ([S]-env-absent (S'' ₛ))) S∈sigs'
canθ'-inner-shadowing-irr' (just Signal.unknown ∷ sigs) S'' sigs' p S status θ θo S∈sigs'
  with any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (Canθ sigs' 0 p) (((θ ← [ (S ₛ) ↦ status ]) ← θo) ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (Canθ sigs' 0 p) ((θ ← θo) ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-sigs-Canθ-θ←[S]-absent←S←θo←[S''] | yes S''∈canθ'-sigs-Canθ-θ←[S]←S←θo←[S'']
  rewrite sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env (S'' ₛ)))
  = canθ'-inner-shadowing-irr' sigs (suc S'') sigs' p S status θ (θo ← ([S]-env (S'' ₛ))) S∈sigs'
... | no  S''∉canθ'-sigs-Canθ-θ←[S]-absent←S←θo←[S''] | no  S''∉canθ'-sigs-Canθ-θ←[S]←S←θo←[S'']
  rewrite sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env-absent (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env-absent (S'' ₛ)))
  = canθ'-inner-shadowing-irr' sigs (suc S'') sigs' p S status θ (θo ← ([S]-env-absent (S'' ₛ))) S∈sigs'
... | yes S''∈canθ'-sigs-Canθ-θ←[S]-absent←S←θo←[S''] | no  S''∉canθ'-sigs-Canθ-θ←[S]←S←θo←[S'']
  rewrite sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env (S'' ₛ)))
        | canθ'-inner-shadowing-irr' sigs (suc S'') sigs' p S status θ (θo ← ([S]-env (S'' ₛ))) S∈sigs'
  = ⊥-elim (S''∉canθ'-sigs-Canθ-θ←[S]←S←θo←[S'']
              S''∈canθ'-sigs-Canθ-θ←[S]-absent←S←θo←[S''])
... | no  S''∉canθ'-sigs-Canθ-θ←[S]-absent←S←θo←[S''] | yes S''∈canθ'-sigs-Canθ-θ←[S]←S←θo←[S'']
  rewrite sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env (S'' ₛ)))
        | canθ'-inner-shadowing-irr' sigs (suc S'') sigs' p S status θ (θo ← ([S]-env (S'' ₛ))) S∈sigs'
  = ⊥-elim (S''∉canθ'-sigs-Canθ-θ←[S]-absent←S←θo←[S'']
              S''∈canθ'-sigs-Canθ-θ←[S]←S←θo←[S''])


canθ'-inner-shadowing-irr : ∀ sigs S'' sigs' p S status θ →
  S ∈ SigMap.keys sigs' →
    Canθ' sigs S'' (Canθ sigs' 0 p) (θ ← [ (S ₛ) ↦ status ]) ≡
    Canθ' sigs S'' (Canθ sigs' 0 p) θ
canθ'-inner-shadowing-irr sigs S'' sigs' p S status θ S∈sigs'
  rewrite cong (Canθ' sigs S'' (Canθ sigs' 0 p))
            (Env.←-comm Env.[]env θ distinct-empty-left)
        | cong (Canθ' sigs S'' (Canθ sigs' 0 p))
            (Env.←-comm Env.[]env (θ ← [ (S ₛ) ↦ status ]) distinct-empty-left)
  = canθ'-inner-shadowing-irr' sigs S'' sigs' p S status θ Env.[]env S∈sigs'


canθ'-search-acc : ∀ sigs S κ θ →
  ∀ S'' status →
    S'' ∉ map (_+_ S)  (SigMap.keys sigs) →
    Canθ' sigs S  κ  (θ ← [ (S'' ₛ) ↦ status ]) ≡
    Canθ' sigs S (κ ∘ (_← [ (S'' ₛ) ↦ status ])) θ
canθ'-search-acc [] S κ θ S'' status S''∉map-+-S-sigs =
  refl
canθ'-search-acc (nothing ∷ sigs) S κ θ S'' status S''∉map-+-S-sigs
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  = canθ'-search-acc sigs (suc S) κ θ S'' status S''∉map-+-S-sigs
canθ'-search-acc (just Signal.present ∷ sigs) S κ θ S'' status S''∉map-+-S-sigs
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env-present (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.present (S''∉map-+-S-sigs ∘ here))
  = canθ'-search-acc sigs (suc S) κ (θ ← [S]-env-present (S ₛ)) S'' status
      (S''∉map-+-S-sigs ∘ there)
canθ'-search-acc (just Signal.absent ∷ sigs) S κ θ S'' status S''∉map-+-S-sigs
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env-absent (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.absent (S''∉map-+-S-sigs ∘ here))
  = canθ'-search-acc sigs (suc S) κ (θ ← [S]-env-absent (S ₛ)) S'' status
      (S''∉map-+-S-sigs ∘ there)
canθ'-search-acc (just Signal.unknown ∷ sigs) S κ θ S'' status S''∉map-+-S-sigs
  with any (_≟_ S) (proj₁ (Canθ' sigs (suc S) (λ θ* → κ (θ* ← [ (S'' ₛ) ↦ status ])) (θ ← [S]-env (S ₛ))))
     | any (_≟_ S) (proj₁ (Canθ' sigs (suc S) κ ((θ ← [ (S'' ₛ) ↦ status ]) ← [S]-env (S ₛ))))
... | yes S∈canθ'-⟨canθ-←[S'']⟩-θ←[S] | yes S∈canθ'-canθ-θ←[S'']←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.unknown (S''∉map-+-S-sigs ∘ here))
  = canθ'-search-acc sigs (suc S) κ (θ ← [S]-env (S ₛ)) S'' status
      (S''∉map-+-S-sigs ∘ there)
... | no  S∉canθ'-⟨canθ-←[S'']⟩-θ←[S] | no  S∉canθ'-canθ-θ←[S'']←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env-absent (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.absent (S''∉map-+-S-sigs ∘ here))
  = canθ'-search-acc sigs (suc S) κ (θ ← [S]-env-absent (S ₛ)) S'' status
      (S''∉map-+-S-sigs ∘ there)
... | yes S∈canθ'-⟨canθ-←[S'']⟩-θ←[S] | no  S∉canθ'-canθ-θ←[S'']←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.unknown (S''∉map-+-S-sigs ∘ here))
        | canθ'-search-acc sigs (suc S) κ (θ ← [S]-env (S ₛ)) S'' status
            (S''∉map-+-S-sigs ∘ there)
  = ⊥-elim (S∉canθ'-canθ-θ←[S'']←[S] S∈canθ'-⟨canθ-←[S'']⟩-θ←[S])
... | no  S∉canθ'-⟨canθ-←[S'']⟩-θ←[S] | yes S∈canθ'-canθ-θ←[S'']←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.unknown (S''∉map-+-S-sigs ∘ here))
        | canθ'-search-acc sigs (suc S) κ (θ ← [S]-env (S ₛ)) S'' status
            (S''∉map-+-S-sigs ∘ there)
  = ⊥-elim (S∉canθ'-⟨canθ-←[S'']⟩-θ←[S] S∈canθ'-canθ-θ←[S'']←[S])


canθ'-search-acc-set-irr : ∀ sigs S κ θ →
  ∀ S'' status status' →
    S'' ∉ map (_+_ S)  (SigMap.keys sigs) →
    Canθ' sigs S κ (θ ← [ (S'' ₛ) ↦ status ]) ≡
    Canθ' sigs S (κ ∘ (_← [ (S'' ₛ) ↦ status ])) (θ ← [ (S'' ₛ) ↦ status' ])
canθ'-search-acc-set-irr [] S κ θ S'' status status' S''∉map-+-S-sigs
  rewrite sym (Env.←-assoc θ [ (S'' ₛ) ↦ status' ] [ (S'' ₛ) ↦ status ])
        | cong (θ ←_) (Env.←-single-overwrite-sig (S'' ₛ) status' [ (S'' ₛ) ↦ status ]
            (Env.sig-∈-single (S'' ₛ) status))
  = refl
canθ'-search-acc-set-irr (nothing ∷ sigs) S κ θ S'' status status' S''∉map-+-S-sigs
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  = canθ'-search-acc-set-irr sigs (suc S) κ θ S'' status status' S''∉map-+-S-sigs
canθ'-search-acc-set-irr (just Signal.present ∷ sigs) S κ θ S'' status status' S''∉map-+-S-sigs
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env-present (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.present (S''∉map-+-S-sigs ∘ here))
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status' ] ([S]-env-present (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status' (S ₛ) Signal.present (S''∉map-+-S-sigs ∘ here))
  = canθ'-search-acc-set-irr sigs (suc S) κ (θ ← [S]-env-present (S ₛ)) S'' status status'
      (S''∉map-+-S-sigs ∘ there)
canθ'-search-acc-set-irr (just Signal.absent ∷ sigs) S κ θ S'' status status' S''∉map-+-S-sigs
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env-absent (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.absent (S''∉map-+-S-sigs ∘ here))
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status' ] ([S]-env-absent (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status' (S ₛ) Signal.absent (S''∉map-+-S-sigs ∘ here))
  = canθ'-search-acc-set-irr sigs (suc S) κ (θ ← [S]-env-absent (S ₛ)) S'' status status'
      (S''∉map-+-S-sigs ∘ there)
canθ'-search-acc-set-irr (just Signal.unknown ∷ sigs) S κ θ S'' status status' S''∉map-+-S-sigs
  with any (_≟_ S) (proj₁ (Canθ' sigs (suc S) (λ θ* → κ (θ* ← [ (S'' ₛ) ↦ status ])) ((θ ← [ (S'' ₛ) ↦ status' ]) ← [S]-env (S ₛ))))
     | any (_≟_ S) (proj₁ (Canθ' sigs (suc S) κ ((θ ← [ (S'' ₛ) ↦ status ]) ← [S]-env (S ₛ))))
... | yes S∈canθ'-⟨canθ-←[S'']⟩-θ←[S'']←[S] | yes S∈canθ'-canθ-θ←[S'']←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.unknown (S''∉map-+-S-sigs ∘ here))
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status' ] ([S]-env (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status' (S ₛ) Signal.unknown (S''∉map-+-S-sigs ∘ here))
  = canθ'-search-acc-set-irr sigs (suc S) κ (θ ← [S]-env (S ₛ)) S'' status status'
      (S''∉map-+-S-sigs ∘ there)
... | no  S∉canθ'-⟨canθ-←[S'']⟩-θ←[S'']←[S] | no  S∉canθ'-canθ-θ←[S'']←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env-absent (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.absent (S''∉map-+-S-sigs ∘ here))
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status' ] ([S]-env-absent (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status' (S ₛ) Signal.absent (S''∉map-+-S-sigs ∘ here))
  = canθ'-search-acc-set-irr sigs (suc S) κ (θ ← [S]-env-absent (S ₛ)) S'' status status'
      (S''∉map-+-S-sigs ∘ there)
... | yes S∈canθ'-⟨canθ-←[S'']⟩-θ←[S'']←[S] | no  S∉canθ'-canθ-θ←[S'']←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.unknown (S''∉map-+-S-sigs ∘ here))
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status' ] ([S]-env (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status' (S ₛ) Signal.unknown (S''∉map-+-S-sigs ∘ here))
        | canθ'-search-acc-set-irr sigs (suc S) κ (θ ← [S]-env (S ₛ)) S'' status status'
            (S''∉map-+-S-sigs ∘ there)
  = ⊥-elim (S∉canθ'-canθ-θ←[S'']←[S] S∈canθ'-⟨canθ-←[S'']⟩-θ←[S'']←[S])
... | no  S∉canθ'-⟨canθ-←[S'']⟩-θ←[S'']←[S] | yes S∈canθ'-canθ-θ←[S'']←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
        | +-comm S 0
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status ] ([S]-env (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status (S ₛ) Signal.unknown (S''∉map-+-S-sigs ∘ here))
        | Env.←-assoc-comm θ [ (S'' ₛ) ↦ status' ] ([S]-env (S ₛ))
            (Env.sig-single-noteq-distinct (S'' ₛ) status' (S ₛ) Signal.unknown (S''∉map-+-S-sigs ∘ here))
        | canθ'-search-acc-set-irr sigs (suc S) κ (θ ← [S]-env (S ₛ)) S'' status status'
            (S''∉map-+-S-sigs ∘ there)
  = ⊥-elim (S∉canθ'-⟨canθ-←[S'']⟩-θ←[S'']←[S] S∈canθ'-canθ-θ←[S'']←[S])


canθ'-canθ-propagate-up-in : ∀ sigs S r θ →
  ∀ sigs' S' S'' →
    S' ∈ proj₁ (Canθ' sigs S (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ))) θ) →
    S'' ∈ proj₁ (Canθ' sigs S (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ))) θ) →
    S'' ∈ proj₁ (Canθ' sigs S (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r θ*) θ)
canθ'-canθ-propagate-up-in [] S r θ sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
  with any (_≟_ S') (Canθₛ sigs' (suc S') r (θ ← [S]-env (S' ₛ)))
... | yes S'∈canθ-sigs'-r-θ*←[S'] =
  S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
... | no  S'∉canθ-sigs'-r-θ*←[S'] =
  ⊥-elim (S'∉canθ-sigs'-r-θ*←[S'] S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩)
canθ'-canθ-propagate-up-in (nothing ∷ sigs) S r θ sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ =
  canθ'-canθ-propagate-up-in sigs (suc S) r θ sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
canθ'-canθ-propagate-up-in (just Signal.present ∷ sigs) S r θ sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ =
  canθ'-canθ-propagate-up-in sigs (suc S) r (θ ← [S]-env-present (S ₛ)) sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
canθ'-canθ-propagate-up-in (just Signal.absent ∷ sigs) S r θ sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ =
  canθ'-canθ-propagate-up-in sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
canθ'-canθ-propagate-up-in (just Signal.unknown ∷ sigs) S r θ sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
  with any (_≟_ S)
         (proj₁
           (Canθ' sigs (suc S) (Canθ (just Signal.unknown ∷ sigs') S' r) (θ ← [S]-env (S ₛ))))
     | any (_≟_ S)
         (proj₁
           (Canθ' sigs (suc S) (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ))) (θ ← [S]-env (S ₛ))))
... | yes S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | yes S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  canθ'-canθ-propagate-up-in sigs (suc S) r (θ ← [S]-env (S ₛ)) sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
... | no  S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | no  S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  canθ'-canθ-propagate-up-in sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
... | yes S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | no  S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  canθ'ₛ-canθ-add-sig-monotonic sigs (suc S) (just Signal.unknown ∷ sigs') S' r θ
    (S ₛ) Signal.absent S''
    (canθ'-canθ-propagate-up-in sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) sigs' S' S''
      S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
      S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩)
... | no  S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | yes S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  ⊥-elim
    (S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S]
      (canθ'-canθ-propagate-up-in sigs (suc S) r (θ ← [S]-env (S ₛ)) sigs' S' S
        S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
        S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]))


canθₛ-a∷s⊆canθₛ-u∷s : ∀ sigs r S' θ S →
  S ∈ Canθₛ (just Signal.absent ∷ sigs) S' r θ →
  S ∈ Canθₛ (just Signal.unknown ∷ sigs) S' r θ
canθₛ-a∷s⊆canθₛ-u∷s sigs r S' θ S S∈can-sigs-r-θ←[S↦absent]
  with any (_≟_ S') (Canθₛ sigs (suc S') r (θ ← [S]-env (S' ₛ)))
... | yes a = canθₛ-add-sig-monotonic sigs (suc S') r θ (S' ₛ) Signal.absent S
                S∈can-sigs-r-θ←[S↦absent]
... | no na = S∈can-sigs-r-θ←[S↦absent]


canθ'-canθ-propagate-down-not-in : ∀ sigs S r θ →
  ∀ S' sigs' →
    S' ∉ proj₁ (Canθ' sigs S (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r θ*) θ) →
    Canθ' sigs S (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r θ*) θ ≡
    Canθ' sigs S (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env-absent (S' ₛ))) θ
canθ'-canθ-propagate-down-not-in [] S r θ S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
  with any (_≟_ S') (Canθₛ sigs' (suc S') r (θ ← [S]-env (S' ₛ)))
... | yes S'∈canθ-sigs'-r-θ←[S'] =
  ⊥-elim (S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ S'∈canθ-sigs'-r-θ←[S'])
... | no  S'∉canθ-sigs'-r-θ←[S'] = refl
canθ'-canθ-propagate-down-not-in (nothing ∷ sigs) S r θ S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ =
  canθ'-canθ-propagate-down-not-in sigs (suc S) r θ S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
canθ'-canθ-propagate-down-not-in (just Signal.present ∷ sigs) S r θ S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ =
  canθ'-canθ-propagate-down-not-in sigs (suc S) r (θ ← [S]-env-present (S ₛ)) S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
canθ'-canθ-propagate-down-not-in (just Signal.absent ∷ sigs) S r θ S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ =
  canθ'-canθ-propagate-down-not-in sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
canθ'-canθ-propagate-down-not-in (just Signal.unknown ∷ sigs) S r θ S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
  with any (_≟_ S)
          (proj₁
            (Canθ' sigs (suc S)
              (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r θ*)
              (θ ← [S]-env (S ₛ))))
     | any (_≟_ S)
          (proj₁
            (Canθ' sigs (suc S)
              (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env-absent (S' ₛ)))
              (θ ← [S]-env (S ₛ))))
... | yes a | yes b =
  canθ'-canθ-propagate-down-not-in sigs (suc S) r (θ ← [S]-env (S ₛ)) S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
... | no na | no nb =
  canθ'-canθ-propagate-down-not-in sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
... | yes a | no nb
  rewrite sym (canθ'-canθ-propagate-down-not-in sigs (suc S) r (θ ← [S]-env (S ₛ)) S' sigs' S'∉canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩)
  = ⊥-elim (nb a)
... | no na | yes b
  = ⊥-elim (na (canθ'ₛ-subset-lemma sigs (suc S) (Canθ (just Signal.absent ∷ sigs') S' r) (Canθ (just Signal.unknown ∷ sigs') S' r) (θ ← [S]-env (S ₛ)) (canθₛ-a∷s⊆canθₛ-u∷s sigs' r S') (canθₛ-add-sig-monotonic (just Signal.unknown ∷ sigs') S' r) S b))


canθ'-canθ-propagate-down-in : ∀ sigs S r θ →
  ∀ S' sigs' →
    S' ∈ proj₁ (Canθ' sigs S (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r θ*) θ) →
    Canθ' sigs S (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r θ*) θ ≡
    Canθ' sigs S (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ))) θ
canθ'-canθ-propagate-down-in [] S r θ S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
  with any (_≟_ S') (Canθₛ sigs' (suc S') r (θ ← [S]-env (S' ₛ)))
... | yes S'∈canθ-sigs'-r-θ←[S'] = refl
... | no  S'∉canθ-sigs'-r-θ←[S'] =
  ⊥-elim
    (S'∉canθ-sigs'-r-θ←[S']
      (canθₛ-add-sig-monotonic sigs' (suc S') r θ (S' ₛ) Signal.absent S'
         S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩))
canθ'-canθ-propagate-down-in (nothing ∷ sigs) S r θ S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ =
  canθ'-canθ-propagate-down-in sigs (suc S) r θ S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
canθ'-canθ-propagate-down-in (just Signal.present ∷ sigs) S r θ S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ =
  canθ'-canθ-propagate-down-in sigs (suc S) r (θ ← [S]-env-present (S ₛ)) S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
canθ'-canθ-propagate-down-in (just Signal.absent ∷ sigs) S r θ S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ =
  canθ'-canθ-propagate-down-in sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
canθ'-canθ-propagate-down-in (just Signal.unknown ∷ sigs) S r θ S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
  with any (_≟_ S)
         (proj₁
           (Canθ' sigs (suc S)
             (Canθ (just Signal.unknown ∷ sigs') S' r)
             (θ ← [S]-env (S ₛ))))
     | any (_≟_ S)
         (proj₁
           (Canθ' sigs (suc S)
             (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ)))
             (θ ← [S]-env (S ₛ))))
... | yes S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | yes S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  canθ'-canθ-propagate-down-in sigs (suc S) r (θ ← [S]-env (S ₛ)) S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
... | no  S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | no  S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  canθ'-canθ-propagate-down-in sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
... | yes S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | no  S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]
  = ⊥-elim
      (S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]
        (subst (S ∈_)
          (cong proj₁
            (canθ'-canθ-propagate-down-in sigs (suc S) r (θ ← [S]-env (S ₛ)) S' sigs'
              S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩))
          S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S]))
... | no  S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | yes S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]
  = ⊥-elim
    (S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S]
      (subst (S ∈_)
        (cong proj₁
          (sym (canθ'-canθ-propagate-down-in sigs (suc S) r (θ ← [S]-env (S ₛ)) S' sigs'
            (canθ'ₛ-canθ-add-sig-monotonic sigs (suc S) (just Signal.unknown ∷ sigs') S'
              r θ (S ₛ) Signal.absent S'
              S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩))))
        S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]))



canθ'-canθ-propagate-up-in-set-irr : ∀ sigs S r θ status →
  ∀ sigs' S' S'' →
    S' ∈ proj₁ (Canθ' sigs S (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ))) θ) →
    S'' ∈ proj₁ (Canθ' sigs S (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ))) θ) →
    S'' ∈ proj₁ (Canθ' sigs S (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r (θ* ← [ (S' ₛ) ↦ status ])) θ)
canθ'-canθ-propagate-up-in-set-irr [] S r θ status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
  with any (_≟_ S') (Canθₛ sigs' (suc S') r ((θ ← [ (S' ₛ) ↦ status ]) ← [S]-env (S' ₛ)))
... | yes S'∈canθ-sigs'-r-θ*←[S']
  rewrite Env.sig-single-←-←-overwrite θ (S' ₛ) status Signal.unknown
  = S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
... | no  S'∉canθ-sigs'-r-θ*←[S']
  rewrite Env.sig-single-←-←-overwrite θ (S' ₛ) status Signal.unknown 
  = ⊥-elim (S'∉canθ-sigs'-r-θ*←[S'] S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩)
canθ'-canθ-propagate-up-in-set-irr (nothing ∷ sigs) S r θ status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ =
  canθ'-canθ-propagate-up-in-set-irr sigs (suc S) r θ status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
canθ'-canθ-propagate-up-in-set-irr (just Signal.present ∷ sigs) S r θ status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ =
  canθ'-canθ-propagate-up-in-set-irr sigs (suc S) r (θ ← [S]-env-present (S ₛ)) status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
canθ'-canθ-propagate-up-in-set-irr (just Signal.absent ∷ sigs) S r θ status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ =
  canθ'-canθ-propagate-up-in-set-irr sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
canθ'-canθ-propagate-up-in-set-irr (just Signal.unknown ∷ sigs) S r θ status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
  with any (_≟_ S)
         (proj₁
           (Canθ' sigs (suc S) (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r (θ* ← [ (S' ₛ) ↦ status ])) (θ ← [S]-env (S ₛ))))
     | any (_≟_ S)
         (proj₁
           (Canθ' sigs (suc S) (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ))) (θ ← [S]-env (S ₛ))))
... | yes S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | yes S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  canθ'-canθ-propagate-up-in-set-irr sigs (suc S) r (θ ← [S]-env (S ₛ)) status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
... | no  S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | no  S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  canθ'-canθ-propagate-up-in-set-irr sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) status sigs' S' S'' S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩ S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
... | yes S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | no  S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]
  = canθ'ₛ-add-sig-monotonic sigs (suc S)
       (Canθ (just Signal.unknown ∷ sigs') S' r ∘ (_← [ (S' ₛ) ↦ status ]))
       θ (S ₛ) Signal.absent
       (λ θ* S* status* S'' S''∈ →
         canθₛ-cong-←-add-sig-monotonic (just Signal.unknown ∷ sigs') S' r
         θ* [ (S' ₛ) ↦ status ] S* status* S'' S''∈) S''
       (canθ'-canθ-propagate-up-in-set-irr sigs (suc S) r (θ ← [S]-env-absent (S ₛ))
         status sigs' S' S''
         S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
         S''∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩)
... | no  S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | yes S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  ⊥-elim
    (S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S]
      (canθ'-canθ-propagate-up-in-set-irr sigs (suc S) r (θ ← [S]-env (S ₛ)) status sigs' S' S
        S'∈canθ'-sigs-⟨canθ-sigs'-r-θ*←[S']⟩
        S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]))


canθ'-canθ-propagate-down-in-set-irr : ∀ sigs S r θ status →
  ∀ S' sigs' →
    S' ∈ proj₁ (Canθ' sigs S (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r (θ* ← [ (S' ₛ) ↦ status ])) θ) →
    Canθ' sigs S (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r (θ* ← [ (S' ₛ) ↦ status ])) θ ≡
    Canθ' sigs S (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ))) θ
canθ'-canθ-propagate-down-in-set-irr [] S r θ status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
  with any (_≟_ S') (Canθₛ sigs' (suc S') r ((θ ← [ (S' ₛ) ↦ status ]) ← [S]-env (S' ₛ)))
... | yes S'∈canθ-sigs'-r-θ←[S'] rewrite Env.sig-single-←-←-overwrite θ (S' ₛ) status Signal.unknown = refl
... | no  S'∉canθ-sigs'-r-θ←[S'] =
  ⊥-elim
    (S'∉canθ-sigs'-r-θ←[S']
      (canθₛ-add-sig-monotonic sigs' (suc S') r (θ ← [ (S' ₛ) ↦ status ]) (S' ₛ) Signal.absent S'
         S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩))
canθ'-canθ-propagate-down-in-set-irr (nothing ∷ sigs) S r θ status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ =
  canθ'-canθ-propagate-down-in-set-irr sigs (suc S) r θ status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
canθ'-canθ-propagate-down-in-set-irr (just Signal.present ∷ sigs) S r θ status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ =
  canθ'-canθ-propagate-down-in-set-irr sigs (suc S) r (θ ← [S]-env-present (S ₛ)) status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
canθ'-canθ-propagate-down-in-set-irr (just Signal.absent ∷ sigs) S r θ status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩ =
  canθ'-canθ-propagate-down-in-set-irr sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
canθ'-canθ-propagate-down-in-set-irr (just Signal.unknown ∷ sigs) S r θ status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
  with any (_≟_ S)
         (proj₁
           (Canθ' sigs (suc S)
             (λ θ* → Canθ (just Signal.unknown ∷ sigs') S' r (θ* ← [ (S' ₛ) ↦ status ]))
             (θ ← [S]-env (S ₛ))))
     | any (_≟_ S)
         (proj₁
           (Canθ' sigs (suc S)
             (λ θ* → Canθ sigs' (suc S') r (θ* ← [S]-env (S' ₛ)))
             (θ ← [S]-env (S ₛ))))
... | yes S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | yes S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  canθ'-canθ-propagate-down-in-set-irr sigs (suc S) r (θ ← [S]-env (S ₛ)) status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
... | no  S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | no  S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S] =
  canθ'-canθ-propagate-down-in-set-irr sigs (suc S) r (θ ← [S]-env-absent (S ₛ)) status S' sigs' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩
... | yes S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | no  S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]
  = ⊥-elim
      (S∉canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]
        (subst (S ∈_)
          (cong proj₁
            (canθ'-canθ-propagate-down-in-set-irr sigs (suc S) r (θ ← [S]-env (S ₛ)) status S' sigs'
              S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩))
          S∈canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S]))
... | no  S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S] | yes S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]
  = ⊥-elim
    (S∉canθ'-sigs-⟨canθ-u∷sigs'-r⟩-θ←[S]
      (subst (S ∈_)
        (cong proj₁
          (sym (canθ'-canθ-propagate-down-in-set-irr sigs (suc S) r (θ ← [S]-env (S ₛ)) status S' sigs'
            (canθ'ₛ-add-sig-monotonic sigs (suc S)
               (Canθ (just Signal.unknown ∷ sigs') S' r ∘
                (λ section → section ← [ (S' ₛ) ↦ status ]))
               θ (S ₛ) Signal.absent
               (λ θ* S* status* →
                 canθₛ-cong-←-add-sig-monotonic (just Signal.unknown ∷ sigs') S' r
                   θ* [ (S' ₛ) ↦ status ] S* status*)
               S' S'∈canθ'-sigs-⟨Canθ-u∷sigs'-θ*⟩))))
        S∈canθ'-sigs-⟨canθ-sigs'-θ*←[S']⟩-θ←[S]))


canθ'-←-distribute : ∀ sigs sigs' S'' r θ →
  Canθ (SigMap.union sigs sigs') S'' r θ ≡
  Canθ' sigs S'' (Canθ sigs' S'' r) θ
canθ'-←-distribute [] sigs' S'' r θ = refl
canθ'-←-distribute sigs [] S'' r θ
  rewrite SigMap.union-comm sigs SigMap.empty (λ _ _ ())
        | unfold sigs S'' r θ
  = refl
canθ'-←-distribute (nothing ∷ sigs) (nothing ∷ sigs') S'' r θ =
  canθ'-←-distribute sigs sigs' (suc S'') r θ
canθ'-←-distribute (just Signal.present ∷ sigs) (nothing ∷ sigs') S'' r θ =
  canθ'-←-distribute sigs sigs' (suc S'') r
    (θ ← [S]-env-present (S'' ₛ))
canθ'-←-distribute (just Signal.absent ∷ sigs) (nothing ∷ sigs') S'' r θ =
  canθ'-←-distribute sigs sigs' (suc S'') r
    (θ ← [S]-env-absent (S'' ₛ))
canθ'-←-distribute (just Signal.unknown ∷ sigs) (nothing ∷ sigs') S'' r θ
  with any (_≟_ S'') (proj₁ (Canθ (SigMap.union sigs sigs') (suc S'') r (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (Canθ sigs' (suc S'') r) (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨canθ-sigs'⟩-θ←[S''] =
  canθ'-←-distribute sigs sigs' (suc S'') r
    (θ ← [S]-env (S'' ₛ))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨canθ-sigs'⟩-θ←[S''] =
  canθ'-←-distribute sigs sigs' (suc S'') r
    (θ ← [S]-env-absent (S'' ₛ))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨canθ-sigs'⟩-θ←[S'']
  rewrite canθ'-←-distribute sigs sigs' (suc S'') r (θ ← [S]-env (S'' ₛ))
  = ⊥-elim (S''∉canθ'-sigs-⟨canθ-sigs'⟩-θ←[S''] S''∈canθ'-sigs←sigs'-r-θ←[S''])
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨canθ-sigs'⟩-θ←[S'']
  rewrite canθ'-←-distribute sigs sigs' (suc S'') r (θ ← [S]-env (S'' ₛ))
  = ⊥-elim (S''∉canθ'-sigs←sigs'-r-θ←[S''] S''∈canθ'-sigs-⟨canθ-sigs'⟩-θ←[S''])
canθ'-←-distribute (nothing ∷ sigs) (just Signal.present ∷ sigs') S'' r θ =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-present (S'' ₛ)))
    (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.present
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
canθ'-←-distribute (nothing ∷ sigs) (just Signal.absent ∷ sigs') S'' r θ =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-absent (S'' ₛ)))
    (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
canθ'-←-distribute (nothing ∷ sigs) (just Signal.unknown ∷ sigs') S'' r θ
  with any (_≟_ S'') (proj₁ (Canθ (SigMap.union sigs sigs') (suc S'') r (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) θ))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-in sigs (suc S'') r θ S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env (S'' ₛ)))
      (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-not-in sigs (suc S'') r θ S'' sigs' S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env-absent (S'' ₛ)))
      (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
  = ⊥-elim
      (S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
        (canθ'-canθ-propagate-up-in sigs (suc S'') r θ sigs' S'' S'' S''∈canθ'-sigs←sigs'-r-θ←[S''] S''∈canθ'-sigs←sigs'-r-θ←[S'']))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
  = ⊥-elim
      (S''∉canθ'-sigs←sigs'-r-θ←[S'']
        (subst (S'' ∈_)
          (cong proj₁
            (canθ'-canθ-propagate-down-in sigs (suc S'') r θ S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
          S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
canθ'-←-distribute (just Signal.present ∷ sigs) (just Signal.present ∷ sigs') S'' r θ =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-present (S'' ₛ)))
    (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.present Signal.present
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
canθ'-←-distribute (just Signal.absent ∷ sigs)  (just Signal.present ∷ sigs') S'' r θ =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-present (S'' ₛ)))
    (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.present Signal.absent
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
canθ'-←-distribute (just Signal.unknown ∷ sigs) (just Signal.present ∷ sigs') S'' r θ
  with any (_≟_ S'')
         (proj₁
           (Canθ' sigs (suc S'')
             (λ θ* → Canθ sigs' (suc S'') r (θ* ← [S]-env-present (S'' ₛ)))
             (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-sigs-⟨Canθ-sigs'-r-θ*←[S'']⟩-θ←[S''] =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-present (S'' ₛ)))
    (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.present Signal.unknown
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | no  S''∉canθ'-sigs-⟨Canθ-sigs'-r-θ*←[S'']⟩-θ←[S''] =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-present (S'' ₛ)))
    (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.present Signal.absent
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
canθ'-←-distribute (just Signal.present ∷ sigs) (just Signal.absent ∷ sigs') S'' r θ =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-absent (S'' ₛ)))
    (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent Signal.present
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
canθ'-←-distribute (just Signal.absent ∷ sigs)  (just Signal.absent ∷ sigs') S'' r θ =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-absent (S'' ₛ)))
    (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent Signal.absent
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
canθ'-←-distribute (just Signal.unknown ∷ sigs) (just Signal.absent ∷ sigs') S'' r θ
  with any (_≟_ S'')
         (proj₁
           (Canθ' sigs (suc S'')
             (λ θ* → Canθ sigs' (suc S'') r (θ* ← [S]-env-absent (S'' ₛ)))
             (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-sigs-⟨Canθ-sigs'-r-θ*←[S'']⟩-θ←[S''] =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-absent (S'' ₛ)))
    (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent Signal.unknown
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | no  S''∉canθ'-sigs-⟨Canθ-sigs'-r-θ*←[S'']⟩-θ←[S''] =
  trans
    (canθ'-←-distribute sigs sigs' (suc S'') r
     (θ ← [S]-env-absent (S'' ₛ)))
    (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent Signal.absent
      (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
canθ'-←-distribute (just Signal.present ∷ sigs) (just Signal.unknown ∷ sigs') S'' r θ
  with any (_≟_ S'') (proj₁ (Canθ (SigMap.union sigs sigs') (suc S'') r (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) (θ ← [S]-env-present (S'' ₛ))))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-in sigs (suc S'') r (θ ← [S]-env-present (S'' ₛ)) S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env (S'' ₛ)))
      (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown Signal.present
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-not-in sigs (suc S'') r (θ ← [S]-env-present (S'' ₛ)) S'' sigs' S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env-absent (S'' ₛ)))
      (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent Signal.present
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
  = ⊥-elim
      (S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
        (subst (S'' ∈_)
          (sym
            (cong proj₁
              (canθ'-search-acc sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) θ
                S'' Signal.present
                (n∉map-suc-n-+ S'' (SigMap.keys sigs)))))
          (canθ'-canθ-propagate-up-in-set-irr sigs (suc S'') r θ Signal.present sigs' S'' S'' S''∈canθ'-sigs←sigs'-r-θ←[S''] S''∈canθ'-sigs←sigs'-r-θ←[S''])))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
        | canθ'-search-acc sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) θ
                S'' Signal.present
                (n∉map-suc-n-+ S'' (SigMap.keys sigs))
  = ⊥-elim
      (S''∉canθ'-sigs←sigs'-r-θ←[S'']
        (subst (S'' ∈_)
          (cong proj₁
            (canθ'-canθ-propagate-down-in-set-irr sigs (suc S'') r θ Signal.present S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
          S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
canθ'-←-distribute (just Signal.absent ∷ sigs)  (just Signal.unknown ∷ sigs') S'' r θ
  with any (_≟_ S'') (proj₁ (Canθ (SigMap.union sigs sigs') (suc S'') r (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) (θ ← [S]-env-absent (S'' ₛ))))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-in sigs (suc S'') r (θ ← [S]-env-absent (S'' ₛ)) S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env (S'' ₛ)))
      (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown Signal.absent
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-not-in sigs (suc S'') r (θ ← [S]-env-absent (S'' ₛ)) S'' sigs' S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env-absent (S'' ₛ)))
      (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent Signal.absent
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
  = ⊥-elim
      (S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
        (subst (S'' ∈_)
          (sym
            (cong proj₁
              (canθ'-search-acc sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) θ
                S'' Signal.absent
                (n∉map-suc-n-+ S'' (SigMap.keys sigs)))))
          (canθ'-canθ-propagate-up-in-set-irr sigs (suc S'') r θ Signal.absent sigs' S'' S'' S''∈canθ'-sigs←sigs'-r-θ←[S''] S''∈canθ'-sigs←sigs'-r-θ←[S''])))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
        | canθ'-search-acc sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) θ
                S'' Signal.absent
                (n∉map-suc-n-+ S'' (SigMap.keys sigs))
  = ⊥-elim
      (S''∉canθ'-sigs←sigs'-r-θ←[S'']
        (subst (S'' ∈_)
          (cong proj₁
            (canθ'-canθ-propagate-down-in-set-irr sigs (suc S'') r θ Signal.absent S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
          S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
canθ'-←-distribute (just Signal.unknown ∷ sigs) (just Signal.unknown ∷ sigs') S'' r θ
  with any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (λ θ* → Canθ (just Signal.unknown ∷ sigs') S'' r θ*) (θ ← [S]-env (S'' ₛ))))
canθ'-←-distribute (just Signal.unknown ∷ sigs) (just Signal.unknown ∷ sigs') S'' r θ | yes p
  with any (_≟_ S'') (proj₁ (Canθ (SigMap.union sigs sigs') (suc S'') r (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-in sigs (suc S'') r (θ ← [S]-env (S'' ₛ)) S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env (S'' ₛ)))
      (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown Signal.unknown
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-not-in sigs (suc S'') r (θ ← [S]-env (S'' ₛ)) S'' sigs' S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env-absent (S'' ₛ)))
      (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent Signal.unknown
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
  = ⊥-elim
      (S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
        (subst (S'' ∈_)
          (sym
            (cong proj₁
              (canθ'-search-acc sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) θ
                S'' Signal.unknown
                (n∉map-suc-n-+ S'' (SigMap.keys sigs)))))
          (canθ'-canθ-propagate-up-in-set-irr sigs (suc S'') r θ Signal.unknown sigs' S'' S'' S''∈canθ'-sigs←sigs'-r-θ←[S''] S''∈canθ'-sigs←sigs'-r-θ←[S''])))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
        | canθ'-search-acc sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) θ
                S'' Signal.unknown
                (n∉map-suc-n-+ S'' (SigMap.keys sigs))
  = ⊥-elim
      (S''∉canθ'-sigs←sigs'-r-θ←[S'']
        (subst (S'' ∈_)
          (cong proj₁
            (canθ'-canθ-propagate-down-in-set-irr sigs (suc S'') r θ Signal.unknown S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
          S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
canθ'-←-distribute (just Signal.unknown ∷ sigs) (just Signal.unknown ∷ sigs') S'' r θ | no ¬p
  with any (_≟_ S'') (proj₁ (Canθ (SigMap.union sigs sigs') (suc S'') r (θ ← [S]-env (S'' ₛ))))
     | any (_≟_ S'') (proj₁ (Canθ' sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) (θ ← [S]-env-absent (S'' ₛ))))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-in sigs (suc S'') r (θ ← [S]-env-absent (S'' ₛ)) S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env (S'' ₛ)))
      (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown Signal.absent
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite canθ'-canθ-propagate-down-not-in sigs (suc S'') r (θ ← [S]-env-absent (S'' ₛ)) S'' sigs' S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  = trans
      (canθ'-←-distribute sigs sigs' (suc S'') r
       (θ ← [S]-env-absent (S'' ₛ)))
      (canθ'-search-acc-set-irr sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.absent Signal.absent
        (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
... | yes S''∈canθ'-sigs←sigs'-r-θ←[S''] | no  S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
  = ⊥-elim
      (S''∉canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
        (subst (S'' ∈_)
          (sym
            (cong proj₁
              (canθ'-search-acc sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) θ
                S'' Signal.absent
                (n∉map-suc-n-+ S'' (SigMap.keys sigs)))))
          (canθ'-canθ-propagate-up-in-set-irr sigs (suc S'') r θ Signal.absent sigs' S'' S'' S''∈canθ'-sigs←sigs'-r-θ←[S''] S''∈canθ'-sigs←sigs'-r-θ←[S''])))
... | no  S''∉canθ'-sigs←sigs'-r-θ←[S''] | yes S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩
  rewrite trans
            (canθ'-←-distribute sigs sigs' (suc S'') r
              (θ ← [S]-env (S'' ₛ)))
            (canθ'-search-acc sigs (suc S'') (Canθ sigs' (suc S'') r) θ S'' Signal.unknown
              (n∉map-suc-n-+ S'' (SigMap.keys sigs)))
        | canθ'-search-acc sigs (suc S'') (Canθ (just Signal.unknown ∷ sigs') S'' r) θ
                S'' Signal.absent
                (n∉map-suc-n-+ S'' (SigMap.keys sigs))
  = ⊥-elim
      (S''∉canθ'-sigs←sigs'-r-θ←[S'']
        (subst (S'' ∈_)
          (cong proj₁
            (canθ'-canθ-propagate-down-in-set-irr sigs (suc S'') r θ Signal.absent S'' sigs' S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
          S''∈canθ'-sigs-⟨Canθ-u∷sigs'-r-θ⟩))
