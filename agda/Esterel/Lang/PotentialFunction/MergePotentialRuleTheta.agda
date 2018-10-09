{-
The equivalent "goodness" of can w.r.t. the rmerge reduction.
-}
module Esterel.Lang.PotentialFunction.MergePotentialRuleTheta where

open import utility
  renaming (_U̬_ to _∪_ ; _|̌_ to _-_)

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.PotentialFunction
open import Esterel.Lang.PotentialFunction.Base
open import Esterel.Lang.PotentialFunction.CanThetaContinuation
open import Esterel.Lang.PotentialFunction.MergePotentialRuleLeftInductive
open import Esterel.Lang.PotentialFunction.NonMergePotentialRules
open import Esterel.Context
  using (EvaluationContext1 ; EvaluationContext ; _⟦_⟧e ; _≐_⟦_⟧e)
open import Esterel.Context.Properties
  using (plug ; unplug)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
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
  using (++ˡ ; ++ʳ)
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
  using (_∘_ ; id ; _∋_)
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


canθₖ-mergeˡ : ∀ {E θ' r p BV FV} sigs θ →
  CorrectBinding p BV FV →
  p ≐ E ⟦ ρ θ' · r ⟧e →
  ∀ k →
    k ∈ Canθₖ (SigMap.union sigs (Env.sig θ')) 0 (E ⟦ r ⟧e) θ →
    k ∈ Canθₖ sigs 0 p θ
canθₖ-mergeˡ {E} {θ'} {r} sigs θ cb p≐E⟦ρθ'r⟧ k k∈canθ-sigs←θ'-E⟦r⟧-θ
  rewrite sym (unplug p≐E⟦ρθ'r⟧)
  with binding-extract cb (((E ⟦ ρ θ' · r ⟧e) ≐ E ⟦ ρ θ' · r ⟧e) ∋ plug refl)
... | (BVp , FVp) , (BVp⊆BV , FVp⊆FV) , cbρθ'r@(CBρ cbp)
  with binding-subst cb (((E ⟦ ρ θ' · r ⟧e) ≐ E ⟦ ρ θ' · r ⟧e) ∋ plug refl) cbρθ'r
                     ((λ _ ()) ,′ (λ _ ()) ,′ (λ _ ()))
                     ((λ _ ()) ,′ (λ _ ()) ,′ (λ _ ()))
                     CBnothing
... | (BV' , FV') , (BVnothin⊆BV , FVnothin⊆FV) , cbnothin
  rewrite canθ'-←-distribute sigs (Env.sig θ') 0 (E ⟦ r ⟧e) θ =
  canθₖ-mergeˡ-sigs-induction sigs 0 (Env.sig θ') (Env.shr θ') (Env.var θ') r θ
    ((E ⟦ nothin ⟧e ≐ E ⟦ nothin ⟧e) ∋ plug refl) cbnothin
    (distinct'-sym
      (dist'++ˡ
        (distinct'-sym
          (proj₁
            (distinct-term-context-help (ρ θ' · r) E cb cbρθ'r BVp⊆BV cbnothin)))))
    k k∈canθ-sigs←θ'-E⟦r⟧-θ


canθₛ-mergeˡ : ∀ {E θ' r p BV FV} sigs θ →
  CorrectBinding p BV FV →
  p ≐ E ⟦ ρ θ' · r ⟧e →
  ∀ S' →
    Signal.unwrap S' ∉ SigMap.keys (Env.sig θ') →
    Signal.unwrap S' ∈ Canθₛ (SigMap.union sigs (Env.sig θ')) 0 (E ⟦ r ⟧e) θ →
    Signal.unwrap S' ∈ Canθₛ sigs 0 p θ
canθₛ-mergeˡ {E} {θ'} {r} sigs θ cb p≐E⟦ρθ'r⟧ S' S'∉Domθ' S'∈canθ-sigs←θ'-E⟦r⟧-θ
  rewrite sym (unplug p≐E⟦ρθ'r⟧)
  with binding-extract cb (((E ⟦ ρ θ' · r ⟧e) ≐ E ⟦ ρ θ' · r ⟧e) ∋ plug refl)
... | (BVp , FVp) , (BVp⊆BV , FVp⊆FV) , cbρθ'r@(CBρ cbp)
  with binding-subst cb (((E ⟦ ρ θ' · r ⟧e) ≐ E ⟦ ρ θ' · r ⟧e) ∋ plug refl) cbρθ'r
                     ((λ _ ()) ,′ (λ _ ()) ,′ (λ _ ()))
                     ((λ _ ()) ,′ (λ _ ()) ,′ (λ _ ()))
                     CBnothing
... | (BV' , FV') , (BVnothin⊆BV , FVnothin⊆FV) , cbnothin
  rewrite canθ'-←-distribute sigs (Env.sig θ') 0 (E ⟦ r ⟧e) θ =
  canθₛ-mergeˡ-sigs-induction sigs 0 (Env.sig θ') (Env.shr θ') (Env.var θ') r θ
    ((E ⟦ nothin ⟧e ≐ E ⟦ nothin ⟧e) ∋ plug refl) cbnothin
    (distinct'-sym
      (dist'++ˡ
        (distinct'-sym
          (proj₁
            (distinct-term-context-help (ρ θ' · r) E cb cbρθ'r BVp⊆BV cbnothin)))))
    (Signal.unwrap S')
    S'∉Domθ' S'∈canθ-sigs←θ'-E⟦r⟧-θ


canθₛₕ-mergeˡ : ∀ {E θ' r p BV FV} sigs θ →
  CorrectBinding p BV FV →
  p ≐ E ⟦ ρ θ' · r ⟧e →
  ∀ s' →
    SharedVar.unwrap s' ∉ ShrMap.keys (Env.shr θ') →
    SharedVar.unwrap s' ∈ Canθₛₕ (SigMap.union sigs (Env.sig θ')) 0 (E ⟦ r ⟧e) θ →
    SharedVar.unwrap s' ∈ Canθₛₕ sigs 0 p θ
canθₛₕ-mergeˡ {E} {θ'} {r} sigs θ cb p≐E⟦ρθ'r⟧ s' s'∉Domθ' s'∈canθ-sigs←θ'-E⟦r⟧-θ
  rewrite sym (unplug p≐E⟦ρθ'r⟧)
  with binding-extract cb (((E ⟦ ρ θ' · r ⟧e) ≐ E ⟦ ρ θ' · r ⟧e) ∋ plug refl)
... | (BVp , FVp) , (BVp⊆BV , FVp⊆FV) , cbρθ'r@(CBρ cbp)
  with binding-subst cb (((E ⟦ ρ θ' · r ⟧e) ≐ E ⟦ ρ θ' · r ⟧e) ∋ plug refl) cbρθ'r
                     ((λ _ ()) ,′ (λ _ ()) ,′ (λ _ ()))
                     ((λ _ ()) ,′ (λ _ ()) ,′ (λ _ ()))
                     CBnothing
... | (BV' , FV') , (BVnothin⊆BV , FVnothin⊆FV) , cbnothin
  rewrite canθ'-←-distribute sigs (Env.sig θ') 0 (E ⟦ r ⟧e) θ =
  canθₛₕ-mergeˡ-sigs-induction sigs 0 (Env.sig θ') (Env.shr θ') (Env.var θ') r θ
    ((E ⟦ nothin ⟧e ≐ E ⟦ nothin ⟧e) ∋ plug refl) cbnothin
    (distinct'-sym
      (dist'++ˡ
        (distinct'-sym
          (proj₁
            (distinct-term-context-help (ρ θ' · r) E cb cbρθ'r BVp⊆BV cbnothin)))))
    (SharedVar.unwrap s')
    s'∉Domθ' s'∈canθ-sigs←θ'-E⟦r⟧-θ


canθₛ-mergeʳ-add-sig-notin : ∀ sigs' r θ S status →
  S ∉ proj₁ (Dom θ) →
  S ∉ SigMap.keys sigs' →
  ∀ S'' →
    S'' ∈ Canθₛ sigs' 0 r (θ ← [ (S ₛ) ↦ status ]) →
    S'' ∈ Canθₛ sigs' 0 r θ
canθₛ-mergeʳ-add-sig-notin sigs' r θ S status S∉Domθ S∉sigs'
  S'' S''∈canθ-sigs'-r-θ←[S]
  rewrite canθ-is-unknown-lemma sigs' 0 r θ (S ₛ) S∉Domθ
            (subst (S ∉_)
               (sym (map-id (SigMap.keys sigs')))
               S∉sigs')
  = canθₛ-add-sig-monotonic sigs' 0 r θ (S ₛ) status
      S'' S''∈canθ-sigs'-r-θ←[S]


canθₛ-mergeʳ-sigs-induction : ∀ sigs S sigs' r θ →
  distinct' (proj₁ (Dom θ)) (map (_+_ S) (SigMap.keys sigs)) →
  ∀ S'' →
    S'' ∈ proj₁ (Canθ' sigs S (Canθ sigs' 0 r) θ) →
    S'' ∈ proj₁               (Canθ sigs' 0 r θ)
canθₛ-mergeʳ-sigs-induction [] S sigs' r θ θ≠sigs
  S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
  = S''∈canθ'-sigs-canθ-sigs'-r-θ
canθₛ-mergeʳ-sigs-induction (nothing ∷ sigs) S sigs' r θ θ≠sigs
  S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  = canθₛ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ θ≠sigs
      S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
canθₛ-mergeʳ-sigs-induction (just Signal.present ∷ sigs) S sigs' r θ θ≠sigs
  S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs'
  rewrite  canθ'-inner-shadowing-irr sigs (suc S) sigs' r S Signal.present θ S∈sigs'
  = canθₛ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ
      (dist'++ʳ {V2 = S + 0 ∷ []} θ≠sigs) S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
... | no  S∉sigs'
  rewrite +-comm S 0
  = canθₛ-mergeʳ-add-sig-notin sigs' r θ S Signal.present
      (λ S∈Domθ → θ≠sigs S S∈Domθ (here refl)) S∉sigs' S''
      (canθₛ-mergeʳ-sigs-induction sigs (suc S) sigs' r (θ ← [S]-env-present (S ₛ))
        (λ S'' S''∈Domθ←[S] S''∈map-+-suc-S-sigs → -- TODO: should make this a function
          Data.Sum.[ (λ S''∈Domθ → θ≠sigs S'' S''∈Domθ (there S''∈map-+-suc-S-sigs)) ,
                     (λ S''∈[S] →
                       subst (_∉ _)
                         (sym (Env.sig-single-∈-eq (S'' ₛ) (S ₛ) Signal.present S''∈[S]))
                         (n∉map-suc-n-+ S (SigMap.keys sigs))
                       S''∈map-+-suc-S-sigs) ]
            (Env.sig-←⁻ {θ} {[S]-env-present (S ₛ)} (S'' ₛ) S''∈Domθ←[S]))
        S'' S''∈canθ'-sigs-canθ-sigs'-r-θ)
canθₛ-mergeʳ-sigs-induction (just Signal.absent ∷ sigs) S sigs' r θ θ≠sigs
  S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs'
  rewrite  canθ'-inner-shadowing-irr sigs (suc S) sigs' r S Signal.absent θ S∈sigs'
  = canθₛ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ
      (dist'++ʳ {V2 = S + 0 ∷ []} θ≠sigs) S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
... | no  S∉sigs'
  rewrite +-comm S 0
  = canθₛ-mergeʳ-add-sig-notin sigs' r θ S Signal.absent
      (λ S∈Domθ → θ≠sigs S S∈Domθ (here refl)) S∉sigs' S''
      (canθₛ-mergeʳ-sigs-induction sigs (suc S) sigs' r (θ ← [S]-env-absent (S ₛ))
        (λ S'' S''∈Domθ←[S] S''∈map-+-suc-S-sigs → -- TODO: should make this a function
          Data.Sum.[ (λ S''∈Domθ → θ≠sigs S'' S''∈Domθ (there S''∈map-+-suc-S-sigs)) ,
                     (λ S''∈[S] →
                       subst (_∉ _)
                         (sym (Env.sig-single-∈-eq (S'' ₛ) (S ₛ) Signal.absent S''∈[S]))
                         (n∉map-suc-n-+ S (SigMap.keys sigs))
                       S''∈map-+-suc-S-sigs) ]
            (Env.sig-←⁻ {θ} {[S]-env-absent (S ₛ)} (S'' ₛ) S''∈Domθ←[S]))
        S'' S''∈canθ'-sigs-canθ-sigs'-r-θ)
canθₛ-mergeʳ-sigs-induction (just Signal.unknown ∷ sigs) S sigs' r θ θ≠sigs
  S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
  with any (_≟_ S) (proj₁ (Canθ' sigs (suc S) (Canθ sigs' 0 r) (θ ← [S]-env (S ₛ))))
canθₛ-mergeʳ-sigs-induction (just Signal.unknown ∷ sigs) S sigs' r θ θ≠sigs
  S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
  | yes S∈canθ'-sigs-canθ-sigs'-r-θ←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs'
  rewrite  canθ'-inner-shadowing-irr sigs (suc S) sigs' r S Signal.unknown θ S∈sigs'
  = canθₛ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ
      (dist'++ʳ {V2 = S + 0 ∷ []} θ≠sigs) S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
... | no  S∉sigs'
  rewrite +-comm S 0
  = canθₛ-mergeʳ-add-sig-notin sigs' r θ S Signal.unknown
      (λ S∈Domθ → θ≠sigs S S∈Domθ (here refl)) S∉sigs' S''
      (canθₛ-mergeʳ-sigs-induction sigs (suc S) sigs' r (θ ← [S]-env (S ₛ))
        (λ S'' S''∈Domθ←[S] S''∈map-+-suc-S-sigs → -- TODO: should make this a function
          Data.Sum.[ (λ S''∈Domθ → θ≠sigs S'' S''∈Domθ (there S''∈map-+-suc-S-sigs)) ,
                     (λ S''∈[S] →
                       subst (_∉ _)
                         (sym (Env.sig-single-∈-eq (S'' ₛ) (S ₛ) Signal.unknown S''∈[S]))
                         (n∉map-suc-n-+ S (SigMap.keys sigs))
                       S''∈map-+-suc-S-sigs) ]
            (Env.sig-←⁻ {θ} {[S]-env (S ₛ)} (S'' ₛ) S''∈Domθ←[S]))
        S'' S''∈canθ'-sigs-canθ-sigs'-r-θ)
canθₛ-mergeʳ-sigs-induction (just Signal.unknown ∷ sigs) S sigs' r θ θ≠sigs
  S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
  | no  S∉canθ'-sigs-canθ-sigs'-r-θ←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs'
  rewrite  canθ'-inner-shadowing-irr sigs (suc S) sigs' r S Signal.absent θ S∈sigs'
  = canθₛ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ
      (dist'++ʳ {V2 = S + 0 ∷ []} θ≠sigs) S'' S''∈canθ'-sigs-canθ-sigs'-r-θ
... | no  S∉sigs'
  rewrite +-comm S 0
  = canθₛ-mergeʳ-add-sig-notin sigs' r θ S Signal.absent
      (λ S∈Domθ → θ≠sigs S S∈Domθ (here refl)) S∉sigs' S''
      (canθₛ-mergeʳ-sigs-induction sigs (suc S) sigs' r (θ ← [S]-env-absent (S ₛ))
        (λ S'' S''∈Domθ←[S] S''∈map-+-suc-S-sigs → -- TODO: should make this a function
          Data.Sum.[ (λ S''∈Domθ → θ≠sigs S'' S''∈Domθ (there S''∈map-+-suc-S-sigs)) ,
                     (λ S''∈[S] →
                       subst (_∉ _)
                         (sym (Env.sig-single-∈-eq (S'' ₛ) (S ₛ) Signal.absent S''∈[S]))
                         (n∉map-suc-n-+ S (SigMap.keys sigs))
                       S''∈map-+-suc-S-sigs) ]
            (Env.sig-←⁻ {θ} {[S]-env-absent (S ₛ)} (S'' ₛ) S''∈Domθ←[S]))
        S'' S''∈canθ'-sigs-canθ-sigs'-r-θ)


canθₛ-mergeʳ : ∀ sigs θ' r θ →
  distinct' (proj₁ (Dom θ)) (SigMap.keys sigs) →
  ∀ S' →
    Signal.unwrap S' ∈ Canθₛ (SigMap.union sigs (Env.sig θ')) 0 r θ →
    Signal.unwrap S' ∈ Canθₛ (Env.sig θ') 0 r θ
canθₛ-mergeʳ sigs θ' r θ θ≠sigs S' S'∈canθ-sigs←θ'-r-θ
  rewrite canθ'-←-distribute sigs (Env.sig θ') 0 r θ
  = canθₛ-mergeʳ-sigs-induction sigs 0 (Env.sig θ') r θ
      (subst (distinct' _) (sym (map-id (SigMap.keys sigs))) θ≠sigs)
      (Signal.unwrap S') S'∈canθ-sigs←θ'-r-θ


canθₛₕ-mergeʳ-add-sig-notin : ∀ sigs' r θ S status →
  S ∉ proj₁ (Dom θ) →
  S ∉ SigMap.keys sigs' →
  ∀ s'' →
    s'' ∈ Canθₛₕ sigs' 0 r (θ ← [ (S ₛ) ↦ status ]) →
    s'' ∈ Canθₛₕ sigs' 0 r θ
canθₛₕ-mergeʳ-add-sig-notin sigs' r θ S status S∉Domθ S∉sigs'
  s'' s''∈canθ-sigs'-r-θ←[S]
  rewrite canθ-is-unknown-lemma sigs' 0 r θ (S ₛ) S∉Domθ
            (subst (S ∉_)
               (sym (map-id (SigMap.keys sigs')))
               S∉sigs')
  = canθₛₕ-add-sig-monotonic sigs' 0 r θ (S ₛ) status
      s'' s''∈canθ-sigs'-r-θ←[S]


canθₛₕ-mergeʳ-sigs-induction : ∀ sigs S sigs' r θ →
  distinct' (proj₁ (Dom θ)) (map (_+_ S) (SigMap.keys sigs)) →
  ∀ s'' →
    s'' ∈ proj₂ (proj₂ (Canθ' sigs S (Canθ sigs' 0 r) θ)) →
    s'' ∈ proj₂ (proj₂               (Canθ sigs' 0 r θ))
canθₛₕ-mergeʳ-sigs-induction [] S sigs' r θ θ≠sigs
  s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
  = s''∈canθ'-sigs-canθ-sigs'-r-θ
canθₛₕ-mergeʳ-sigs-induction (nothing ∷ sigs) S sigs' r θ θ≠sigs
  s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  = canθₛₕ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ θ≠sigs
      s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
canθₛₕ-mergeʳ-sigs-induction (just Signal.present ∷ sigs) S sigs' r θ θ≠sigs
  s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs'
  rewrite  canθ'-inner-shadowing-irr sigs (suc S) sigs' r S Signal.present θ S∈sigs'
  = canθₛₕ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ
      (dist'++ʳ {V2 = S + 0 ∷ []} θ≠sigs) s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
... | no  S∉sigs'
  rewrite +-comm S 0
  = canθₛₕ-mergeʳ-add-sig-notin sigs' r θ S Signal.present
      (λ S∈Domθ → θ≠sigs S S∈Domθ (here refl)) S∉sigs' s''
      (canθₛₕ-mergeʳ-sigs-induction sigs (suc S) sigs' r (θ ← [S]-env-present (S ₛ))
        (λ S'' S''∈Domθ←[S] S''∈map-+-suc-S-sigs → -- TODO: should make this a function
          Data.Sum.[ (λ S''∈Domθ → θ≠sigs S'' S''∈Domθ (there S''∈map-+-suc-S-sigs)) ,
                     (λ S''∈[S] →
                       subst (_∉ _)
                         (sym (Env.sig-single-∈-eq (S'' ₛ) (S ₛ) Signal.present S''∈[S]))
                         (n∉map-suc-n-+ S (SigMap.keys sigs))
                       S''∈map-+-suc-S-sigs) ]
            (Env.sig-←⁻ {θ} {[S]-env-present (S ₛ)} (S'' ₛ) S''∈Domθ←[S]))
        s'' s''∈canθ'-sigs-canθ-sigs'-r-θ)
canθₛₕ-mergeʳ-sigs-induction (just Signal.absent ∷ sigs) S sigs' r θ θ≠sigs
  s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs'
  rewrite  canθ'-inner-shadowing-irr sigs (suc S) sigs' r S Signal.absent θ S∈sigs'
  = canθₛₕ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ
      (dist'++ʳ {V2 = S + 0 ∷ []} θ≠sigs) s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
... | no  S∉sigs'
  rewrite +-comm S 0
  = canθₛₕ-mergeʳ-add-sig-notin sigs' r θ S Signal.absent
      (λ S∈Domθ → θ≠sigs S S∈Domθ (here refl)) S∉sigs' s''
      (canθₛₕ-mergeʳ-sigs-induction sigs (suc S) sigs' r (θ ← [S]-env-absent (S ₛ))
        (λ S'' S''∈Domθ←[S] S''∈map-+-suc-S-sigs → -- TODO: should make this a function
          Data.Sum.[ (λ S''∈Domθ → θ≠sigs S'' S''∈Domθ (there S''∈map-+-suc-S-sigs)) ,
                     (λ S''∈[S] →
                       subst (_∉ _)
                         (sym (Env.sig-single-∈-eq (S'' ₛ) (S ₛ) Signal.absent S''∈[S]))
                         (n∉map-suc-n-+ S (SigMap.keys sigs))
                       S''∈map-+-suc-S-sigs) ]
            (Env.sig-←⁻ {θ} {[S]-env-absent (S ₛ)} (S'' ₛ) S''∈Domθ←[S]))
        s'' s''∈canθ'-sigs-canθ-sigs'-r-θ)
canθₛₕ-mergeʳ-sigs-induction (just Signal.unknown ∷ sigs) S sigs' r θ θ≠sigs
  s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
  with any (_≟_ S) (proj₁ (Canθ' sigs (suc S) (Canθ sigs' 0 r) (θ ← [S]-env (S ₛ))))
canθₛₕ-mergeʳ-sigs-induction (just Signal.unknown ∷ sigs) S sigs' r θ θ≠sigs
  s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
  | yes S∈canθ'-sigs-canθ-sigs'-r-θ←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs'
  rewrite  canθ'-inner-shadowing-irr sigs (suc S) sigs' r S Signal.unknown θ S∈sigs'
  = canθₛₕ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ
      (dist'++ʳ {V2 = S + 0 ∷ []} θ≠sigs) s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
... | no  S∉sigs'
  rewrite +-comm S 0
  = canθₛₕ-mergeʳ-add-sig-notin sigs' r θ S Signal.unknown
      (λ S∈Domθ → θ≠sigs S S∈Domθ (here refl)) S∉sigs' s''
      (canθₛₕ-mergeʳ-sigs-induction sigs (suc S) sigs' r (θ ← [S]-env (S ₛ))
        (λ S'' S''∈Domθ←[S] S''∈map-+-suc-S-sigs → -- TODO: should make this a function
          Data.Sum.[ (λ S''∈Domθ → θ≠sigs S'' S''∈Domθ (there S''∈map-+-suc-S-sigs)) ,
                     (λ S''∈[S] →
                       subst (_∉ _)
                         (sym (Env.sig-single-∈-eq (S'' ₛ) (S ₛ) Signal.unknown S''∈[S]))
                         (n∉map-suc-n-+ S (SigMap.keys sigs))
                       S''∈map-+-suc-S-sigs) ]
            (Env.sig-←⁻ {θ} {[S]-env (S ₛ)} (S'' ₛ) S''∈Domθ←[S]))
        s'' s''∈canθ'-sigs-canθ-sigs'-r-θ)
canθₛₕ-mergeʳ-sigs-induction (just Signal.unknown ∷ sigs) S sigs' r θ θ≠sigs
  s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
  | no  S∉canθ'-sigs-canθ-sigs'-r-θ←[S]
  rewrite map-+-compose-suc S (SigMap.keys sigs)
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs'
  rewrite  canθ'-inner-shadowing-irr sigs (suc S) sigs' r S Signal.absent θ S∈sigs'
  = canθₛₕ-mergeʳ-sigs-induction sigs (suc S) sigs' r θ
      (dist'++ʳ {V2 = S + 0 ∷ []} θ≠sigs) s'' s''∈canθ'-sigs-canθ-sigs'-r-θ
... | no  S∉sigs'
  rewrite +-comm S 0
  = canθₛₕ-mergeʳ-add-sig-notin sigs' r θ S Signal.absent
      (λ S∈Domθ → θ≠sigs S S∈Domθ (here refl)) S∉sigs' s''
      (canθₛₕ-mergeʳ-sigs-induction sigs (suc S) sigs' r (θ ← [S]-env-absent (S ₛ))
        (λ S'' S''∈Domθ←[S] S''∈map-+-suc-S-sigs → -- TODO: should make this a function
          Data.Sum.[ (λ S''∈Domθ → θ≠sigs S'' S''∈Domθ (there S''∈map-+-suc-S-sigs)) ,
                     (λ S''∈[S] →
                       subst (_∉ _)
                         (sym (Env.sig-single-∈-eq (S'' ₛ) (S ₛ) Signal.absent S''∈[S]))
                         (n∉map-suc-n-+ S (SigMap.keys sigs))
                       S''∈map-+-suc-S-sigs) ]
            (Env.sig-←⁻ {θ} {[S]-env-absent (S ₛ)} (S'' ₛ) S''∈Domθ←[S]))
        s'' s''∈canθ'-sigs-canθ-sigs'-r-θ)


canθₛₕ-mergeʳ : ∀ sigs θ' r θ →
  distinct' (proj₁ (Dom θ)) (SigMap.keys sigs) →
  ∀ s' →
    SharedVar.unwrap s' ∈ Canθₛₕ (SigMap.union sigs (Env.sig θ')) 0 r θ →
    SharedVar.unwrap s' ∈ Canθₛₕ (Env.sig θ') 0 r θ
canθₛₕ-mergeʳ sigs θ' r θ θ≠sigs s' s'∈canθ-sigs←θ'-r-θ
  rewrite canθ'-←-distribute sigs (Env.sig θ') 0 r θ
  = canθₛₕ-mergeʳ-sigs-induction sigs 0 (Env.sig θ') r θ
      (subst (distinct' _) (sym (map-id (SigMap.keys sigs))) θ≠sigs)
      (SharedVar.unwrap s') s'∈canθ-sigs←θ'-r-θ
