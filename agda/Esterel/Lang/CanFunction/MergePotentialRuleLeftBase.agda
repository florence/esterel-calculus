module Esterel.Lang.CanFunction.MergePotentialRuleLeftBase where

open import utility
  renaming (_U̬_ to _∪_ ; _|̌_ to _-_)

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.CanFunction
open import Esterel.Lang.CanFunction.Base
open import Esterel.Lang.CanFunction.CanThetaContinuation
open import Esterel.Lang.CanFunction.MergePotentialRuleCan
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
  using (++⁻)
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


distinct'-S∷Ss⇒[S] : ∀ {xs S Ss} status →
  distinct' xs (S ∷ Ss) →
  distinct' xs (proj₁ (Dom [ (S ₛ) ↦ status ] ))
distinct'-S∷Ss⇒[S] {xs} {S} {Ss} status xs≠S∷Ss S' S'∈xs S'∈[S]
  rewrite Env.sig-single-∈-eq (S' ₛ) (S ₛ) status S'∈[S]
  = xs≠S∷Ss S S'∈xs (here refl)


canθₖ-mergeˡ-E-induction-base-par₁ : ∀ {E q E⟦nothin⟧∥q BV FV} sigs' S' r θ →
  E⟦nothin⟧∥q ≐ (epar₁ q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧∥q BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
    Canθₖ sigs' S' ((E ⟦ r ⟧e) ∥ q) θ ≡
    concatMap (λ k → map (Code._⊔_ k) (Canₖ q θ)) (Canθₖ sigs' S' (E ⟦ r ⟧e) θ)
canθₖ-mergeˡ-E-induction-base-par₁ [] S' r θ
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  = refl
canθₖ-mergeˡ-E-induction-base-par₁ (nothing ∷ sigs') S' r θ
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
  = canθₖ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ (depar₁ E⟦nothin⟧) cb FV≠sigs'
canθₖ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.present ∷ sigs') S' r θ
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env-present (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.present FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r
            (θ ← [S]-env-present (S' ₛ)) (depar₁ E⟦nothin⟧)
            cb (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')
        = refl
canθₖ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.absent ∷ sigs') S' r θ
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r
            (θ ← [S]-env-absent (S' ₛ)) (depar₁ E⟦nothin⟧)
            cb (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')
        = refl
canθₖ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  with any (_≟_ S') (Canθₛ sigs' (suc S') ((E ⟦ r ⟧e) ∥ q) (θ ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) (θ ← [S]-env (S' ₛ)))
... | yes S'∈canθ-sigs'-E⟦r⟧∥q-θ←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.unknown FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r
            (θ ← [S]-env (S' ₛ)) (depar₁ E⟦nothin⟧)
            cb (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')
        = refl
... | no  S'∉canθ-sigs'-E⟦r⟧∥q-θ←[S'] | no  S'∉canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r
            (θ ← [S]-env-absent (S' ₛ)) (depar₁ E⟦nothin⟧)
            cb (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')
        = refl
... | yes S'∈canθ-sigs'-E⟦r⟧∥q-θ←[S'] | no  S'∉canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←[S']
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← [S]-env (S' ₛ))
          (depar₁ dehole) (CBpar CBnothing cbq distinct-empty-left distinct-empty-left
                                               distinct-empty-left (λ _ ()))
          (dist'++ʳ {V2 = proj₁ FVp} (distinct'-sym (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')))
          (S' ₛ) (λ S'∈FVq → FV≠sigs' S' (++ʳ (proj₁ FVp) S'∈FVq) (here refl))
          S'∈canθ-sigs'-E⟦r⟧∥q-θ←[S']))
... | no  S'∉canθ-sigs'-E⟦r⟧∥q-θ←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←[S'] =
  ⊥-elim
    (S'∉canθ-sigs'-E⟦r⟧∥q-θ←[S']
      (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← [S]-env (S' ₛ))
        (epar₁ q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←[S']))


canθₖ-mergeˡ-E-induction-base-par₂ : ∀ {E q q∥E⟦nothin⟧ BV FV} sigs' S' r θ →
  q∥E⟦nothin⟧ ≐ (epar₂ q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding q∥E⟦nothin⟧ BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
    Canθₖ sigs' S' (q ∥ (E ⟦ r ⟧e)) θ ≡
    concatMap (λ k → map (Code._⊔_ k) (Canθₖ sigs' S' (E ⟦ r ⟧e) θ)) (Canₖ q θ)
canθₖ-mergeˡ-E-induction-base-par₂ [] S' r θ
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbq _ _ _ _ _) FV≠sigs'
  = refl
canθₖ-mergeˡ-E-induction-base-par₂ (nothing ∷ sigs') S' r θ
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbq _ _ _ _ _) FV≠sigs'
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
  = canθₖ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ (depar₂ E⟦nothin⟧) cb FV≠sigs'
canθₖ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.present ∷ sigs') S' r θ
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbq _ _ _ _ _) FV≠sigs'
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env-present (S' ₛ)) q cbq
            (distinct'-to-left dist'++ˡ
              (distinct'-S∷Ss⇒[S] Signal.present FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r
            (θ ← [S]-env-present (S' ₛ)) (depar₂ E⟦nothin⟧)
            cb (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')
        = refl
canθₖ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.absent ∷ sigs') S' r θ
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbq _ _ _ _ _) FV≠sigs'
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left dist'++ˡ
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r
            (θ ← [S]-env-absent (S' ₛ)) (depar₂ E⟦nothin⟧)
            cb (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')
        = refl
canθₖ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbq _ _ _ _ _) FV≠sigs'
  with any (_≟_ S') (Canθₛ sigs' (suc S') (q ∥ (E ⟦ r ⟧e)) (θ ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) (θ ← [S]-env (S' ₛ)))
... | yes S'∈canθ-sigs'-q∥E⟦r⟧-θ←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env (S' ₛ)) q cbq
            (distinct'-to-left dist'++ˡ
              (distinct'-S∷Ss⇒[S] Signal.unknown FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r
            (θ ← [S]-env (S' ₛ)) (depar₂ E⟦nothin⟧)
            cb (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')
        = refl
... | no  S'∉canθ-sigs'-q∥E⟦r⟧-θ←[S'] | no  S'∉canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left dist'++ˡ
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r
            (θ ← [S]-env-absent (S' ₛ)) (depar₂ E⟦nothin⟧)
            cb (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')
        = refl
... | yes S'∈canθ-sigs'-q∥E⟦r⟧-θ←[S'] | no  S'∉canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←[S']
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← [S]-env (S' ₛ))
          (depar₂ dehole) (CBpar cbq CBnothing distinct-empty-right distinct-empty-right
                                               distinct-empty-right (λ _ _ ()))
          (λ S' S'∈map-+-suc-S'-sigs' S'∈FVq++[] →
            FV≠sigs' S' (++ˡ (x∈xs++[]→x∈xs {xs = proj₁ FVp} S'∈FVq++[]))
              (there S'∈map-+-suc-S'-sigs'))
          (S' ₛ)
          (λ S'∈FVq++[] →
            FV≠sigs' S' (++ˡ (x∈xs++[]→x∈xs {xs = proj₁ FVp} S'∈FVq++[])) (here refl))
          S'∈canθ-sigs'-q∥E⟦r⟧-θ←[S']))
... | no  S'∉canθ-sigs'-q∥E⟦r⟧-θ←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←[S'] =
  ⊥-elim
    (S'∉canθ-sigs'-q∥E⟦r⟧-θ←[S']
      (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← [S]-env (S' ₛ))
        (epar₂ q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←[S']))


canθₖ-mergeˡ-E-induction-base-seq-notin : ∀ {E q E⟦nothin⟧>>q BV FV} sigs' S' r θ →
  E⟦nothin⟧>>q ≐ (eseq q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧>>q BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
  Code.nothin ∉ Canθₖ sigs' S' (E ⟦ r ⟧e) θ →
    Canθₖ sigs' S' ((E ⟦ r ⟧e) >> q) θ ≡
    Canθₖ sigs' S' (E ⟦ r ⟧e) θ
canθₖ-mergeˡ-E-induction-base-seq-notin {E} [] S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∉canθ-sigs'-E⟦r⟧-θ
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r ⟧e) θ)
... | no  nothin∉can-E⟦r⟧-θ = refl
... | yes nothin∈can-E⟦r⟧-θ = ⊥-elim (nothin∉canθ-sigs'-E⟦r⟧-θ nothin∈can-E⟦r⟧-θ)
canθₖ-mergeˡ-E-induction-base-seq-notin (nothing ∷ sigs') S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∉canθ-sigs'-E⟦r⟧-θ
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | canθₖ-mergeˡ-E-induction-base-seq-notin sigs' (suc S') r
            θ (deseq E⟦nothin⟧) cb FV≠sigs' nothin∉canθ-sigs'-E⟦r⟧-θ
  = refl
canθₖ-mergeˡ-E-induction-base-seq-notin {E} (just Signal.present ∷ sigs') S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∉canθ-sigs'-E⟦r⟧-θ
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | canθₖ-mergeˡ-E-induction-base-seq-notin sigs' (suc S') r
            (θ ← [S]-env-present (S' ₛ)) (deseq E⟦nothin⟧) cb
            (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs') nothin∉canθ-sigs'-E⟦r⟧-θ
  = refl
canθₖ-mergeˡ-E-induction-base-seq-notin {E} (just Signal.absent ∷ sigs') S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∉canθ-sigs'-E⟦r⟧-θ
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | canθₖ-mergeˡ-E-induction-base-seq-notin sigs' (suc S') r
            (θ ← [S]-env-absent (S' ₛ)) (deseq E⟦nothin⟧) cb
            (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs') nothin∉canθ-sigs'-E⟦r⟧-θ
  = refl
canθₖ-mergeˡ-E-induction-base-seq-notin {E} {q} (just Signal.unknown ∷ sigs') S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∉canθ-sigs'-E⟦r⟧-θ
  with any (_≟_ S') (Canθₛ sigs' (suc S') ((E ⟦ r ⟧e) >> q) (θ ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) (θ ← [S]-env (S' ₛ)))
... | yes S'∈canθ-sigs'-E⟦r⟧>>q-θ←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | canθₖ-mergeˡ-E-induction-base-seq-notin sigs' (suc S') r
            (θ ← [S]-env (S' ₛ)) (deseq E⟦nothin⟧) cb
            (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs') nothin∉canθ-sigs'-E⟦r⟧-θ
  = refl
... | no  S'∉canθ-sigs'-E⟦r⟧>>q-θ←[S'] | no  S'∉canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | canθₖ-mergeˡ-E-induction-base-seq-notin sigs' (suc S') r
            (θ ← [S]-env-absent (S' ₛ)) (deseq E⟦nothin⟧) cb
            (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs') nothin∉canθ-sigs'-E⟦r⟧-θ
  = refl
... | yes S'∈canθ-sigs'-E⟦r⟧>>q-θ←[S'] | no  S'∉canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←[S']
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← [S]-env (S' ₛ))
          (deseq dehole) (CBseq CBnothing cbq distinct-empty-left)
          (dist'++ʳ {V2 = proj₁ FVp} (distinct'-sym (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')))
          (S' ₛ) (λ S'∈FVq → FV≠sigs' S' (++ʳ (proj₁ FVp) S'∈FVq) (here refl))
          S'∈canθ-sigs'-E⟦r⟧>>q-θ←[S']))
... | no  S'∉canθ-sigs'-E⟦r⟧>>q-θ←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←[S'] =
  ⊥-elim
    (S'∉canθ-sigs'-E⟦r⟧>>q-θ←[S']
      (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← [S]-env (S' ₛ))
        (eseq q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←[S']))


canθₖ-mergeˡ-E-induction-base-seq-in : ∀ {E q E⟦nothin⟧>>q BV FV} sigs' S' r θ →
  E⟦nothin⟧>>q ≐ (eseq q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧>>q BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
  Code.nothin ∈ Canθₖ sigs' S' (E ⟦ r ⟧e) θ →
    Canθₖ sigs' S' ((E ⟦ r ⟧e) >> q) θ ≡
    CodeSet.set-remove (Canθₖ sigs' S' (E ⟦ r ⟧e) θ) Code.nothin ++ Canₖ q θ
canθₖ-mergeˡ-E-induction-base-seq-in {E} [] S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∈canθ-sigs'-E⟦r⟧-θ
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r ⟧e) θ)
... | no  nothin∉can-E⟦r⟧-θ = ⊥-elim (nothin∉can-E⟦r⟧-θ nothin∈canθ-sigs'-E⟦r⟧-θ)
... | yes nothin∈can-E⟦r⟧-θ = refl
canθₖ-mergeˡ-E-induction-base-seq-in (nothing ∷ sigs') S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∈canθ-sigs'-E⟦r⟧-θ
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | canθₖ-mergeˡ-E-induction-base-seq-in sigs' (suc S') r
            θ (deseq E⟦nothin⟧) cb FV≠sigs' nothin∈canθ-sigs'-E⟦r⟧-θ
  = refl
canθₖ-mergeˡ-E-induction-base-seq-in {E} {q} (just Signal.present ∷ sigs') S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∈canθ-sigs'-E⟦r⟧-θ
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env-present (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.present FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-seq-in sigs' (suc S') r
            (θ ← [S]-env-present (S' ₛ)) (deseq E⟦nothin⟧) cb
            (dist'++ʳ {V2 = S' ∷ []} FV≠sigs') nothin∈canθ-sigs'-E⟦r⟧-θ
  = refl
canθₖ-mergeˡ-E-induction-base-seq-in {E} {q} (just Signal.absent ∷ sigs') S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∈canθ-sigs'-E⟦r⟧-θ
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-seq-in sigs' (suc S') r
            (θ ← [S]-env-absent (S' ₛ)) (deseq E⟦nothin⟧) cb
            (dist'++ʳ {V2 = S' ∷ []} FV≠sigs') nothin∈canθ-sigs'-E⟦r⟧-θ
  = refl
canθₖ-mergeˡ-E-induction-base-seq-in {E} {q} (just Signal.unknown ∷ sigs') S' r θ
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _) FV≠sigs' nothin∈canθ-sigs'-E⟦r⟧-θ
  with any (_≟_ S') (Canθₛ sigs' (suc S') ((E ⟦ r ⟧e) >> q) (θ ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) (θ ← [S]-env (S' ₛ)))
... | yes S'∈canθ-sigs'-E⟦r⟧>>q-θ←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.unknown FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-seq-in sigs' (suc S') r
            (θ ← [S]-env (S' ₛ)) (deseq E⟦nothin⟧) cb
            (dist'++ʳ {V2 = S' ∷ []} FV≠sigs') nothin∈canθ-sigs'-E⟦r⟧-θ
  = refl
... | no  S'∉canθ-sigs'-E⟦r⟧>>q-θ←[S'] | no  S'∉canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | can-irr θ ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | canθₖ-mergeˡ-E-induction-base-seq-in sigs' (suc S') r
            (θ ← [S]-env-absent (S' ₛ)) (deseq E⟦nothin⟧) cb
            (dist'++ʳ {V2 = S' ∷ []} FV≠sigs') nothin∈canθ-sigs'-E⟦r⟧-θ
  = refl
... | yes S'∈canθ-sigs'-E⟦r⟧>>q-θ←[S'] | no  S'∉canθ-sigs'-E⟦r⟧-θ←[S']
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←[S']
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← [S]-env (S' ₛ))
          (deseq dehole) (CBseq CBnothing cbq distinct-empty-left)
          (dist'++ʳ {V2 = proj₁ FVp} (distinct'-sym (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')))
          (S' ₛ) (λ S'∈FVq → FV≠sigs' S' (++ʳ (proj₁ FVp) S'∈FVq) (here refl))
          S'∈canθ-sigs'-E⟦r⟧>>q-θ←[S']))
... | no  S'∉canθ-sigs'-E⟦r⟧>>q-θ←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←[S'] =
  ⊥-elim
    (S'∉canθ-sigs'-E⟦r⟧>>q-θ←[S']
      (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← [S]-env (S' ₛ))
        (eseq q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←[S']))


canθₛ-mergeˡ-E-induction-base-par₁ : ∀ {E q E⟦nothin⟧∥q BV FV} sigs' S' r θ θo →
  E⟦nothin⟧∥q ≐ (epar₁ q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧∥q BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
  ∀ S'' →
    S'' ∈ Canθₛ sigs' S' ((E ⟦ r ⟧e) ∥ q) (θ ← θo) →
    S'' ∈ Canθₛ sigs' S' (E ⟦ r ⟧e) (θ ← θo) ⊎ S'' ∈ Canₛ q (θ ← θo)
canθₛ-mergeˡ-E-induction-base-par₁ {E} [] S' r θ θo
  E⟦nothin⟧∥q cb FV≠sigs' S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  with ++⁻ (Canₛ (E ⟦ r ⟧e) (θ ← θo)) S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ S''∈can-E⟦r⟧-θ←θo = inj₁ S''∈can-E⟦r⟧-θ←θo
... | inj₂ S''∈can-q-θ←θo = inj₂ S''∈can-q-θ←θo
canθₛ-mergeˡ-E-induction-base-par₁ (nothing ∷ sigs') S' r θ θo
  E⟦nothin⟧∥q cb FV≠sigs' S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
  = canθₛ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ θo E⟦nothin⟧∥q cb
      FV≠sigs' S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
canθₛ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.present ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-present (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ (θo ← [S]-env-present (S' ₛ))
         (depar₁ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present]
... | inj₂ S''∈can-q-θ←θo←[S'↦present]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-present (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.present FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-present (S' ₛ))
  = inj₂ S''∈can-q-θ←θo←[S'↦present]
canθₛ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.absent ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (depar₁ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ S''∈can-q-θ←θo←[S'↦absent]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ S''∈can-q-θ←θo←[S'↦absent]
canθₛ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb FV≠sigs' S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  with any (_≟_ S') (Canθₛ sigs' (suc S') ((E ⟦ r ⟧e) ∥ q) ((θ ← θo) ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) ((θ ← θo) ← [S]-env (S' ₛ)))
canθₛ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  | yes S'∈canθ-sigs'-E⟦r⟧∥q-θ←θo←[S] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ (θo ← [S]-env (S' ₛ))
         (depar₁ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown]
... | inj₂ S''∈can-q-θ←θo←[S'↦unknown]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.unknown FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env (S' ₛ))
  = inj₂ S''∈can-q-θ←θo←[S'↦unknown]
canθₛ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  | no  S'∉canθ-sigs'-E⟦r⟧∥q-θ←θo←[S] | no  S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (depar₁ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ S''∈can-q-θ←θo←[S'↦absent]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ S''∈can-q-θ←θo←[S'↦absent]
canθₛ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  | no  S'∉canθ-sigs'-E⟦r⟧∥q-θ←θo←[S] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧∥q-θ←θo←[S]
        (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (epar₁ q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]))
canθₛ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbp cbq _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  | yes S'∈canθ-sigs'-E⟦r⟧∥q-θ←θo←[S] | no  S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (depar₁ dehole) (CBpar CBnothing cbq distinct-empty-left distinct-empty-left
                                               distinct-empty-left (λ _ ()))
          (dist'++ʳ {V2 = proj₁ FVp} (distinct'-sym (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')))
          (S' ₛ) (λ S'∈FVq → FV≠sigs' S' (++ʳ (proj₁ FVp) S'∈FVq) (here refl))
          S'∈canθ-sigs'-E⟦r⟧∥q-θ←θo←[S]))


canθₛ-mergeˡ-E-induction-base-par₂ : ∀ {E q q∥E⟦nothin⟧ BV FV} sigs' S' r θ θo →
  q∥E⟦nothin⟧ ≐ (epar₂ q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding q∥E⟦nothin⟧ BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
  ∀ S'' →
    S'' ∈ Canθₛ sigs' S' (q ∥ (E ⟦ r ⟧e)) (θ ← θo) →
    S'' ∈ Canθₛ sigs' S' (E ⟦ r ⟧e) (θ ← θo) ⊎ S'' ∈ Canₛ q (θ ← θo)
canθₛ-mergeˡ-E-induction-base-par₂ {E} {q} [] S' r θ θo
  q∥E⟦nothin⟧ cb FV≠sigs' S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  with ++⁻ (Canₛ q (θ ← θo)) S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₂ S''∈can-E⟦r⟧-θ←θo = inj₁ S''∈can-E⟦r⟧-θ←θo
... | inj₁ S''∈can-q-θ←θo = inj₂ S''∈can-q-θ←θo
canθₛ-mergeˡ-E-induction-base-par₂ (nothing ∷ sigs') S' r θ θo
  q∥E⟦nothin⟧ cb FV≠sigs' S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
  = canθₛ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ θo q∥E⟦nothin⟧ cb
      FV≠sigs' S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
canθₛ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.present ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-present (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ (θo ← [S]-env-present (S' ₛ))
         (depar₂ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present]
... | inj₂ S''∈can-q-θ←θo←[S'↦present]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-present (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ˡ)
              (distinct'-S∷Ss⇒[S] Signal.present FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-present (S' ₛ))
  = inj₂ S''∈can-q-θ←θo←[S'↦present]
canθₛ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.absent ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (depar₂ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ S''∈can-q-θ←θo←[S'↦absent]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ˡ)
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ S''∈can-q-θ←θo←[S'↦absent]
canθₛ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb FV≠sigs' S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  with any (_≟_ S') (Canθₛ sigs' (suc S') (q ∥ (E ⟦ r ⟧e)) ((θ ← θo) ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) ((θ ← θo) ← [S]-env (S' ₛ)))
canθₛ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  | yes S'∈canθ-sigs'-q∥E⟦r⟧-θ←θo←[S] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ (θo ← [S]-env (S' ₛ))
         (depar₂ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown]
... | inj₂ S''∈can-q-θ←θo←[S'↦unknown]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ˡ)
              (distinct'-S∷Ss⇒[S] Signal.unknown FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env (S' ₛ))
  = inj₂ S''∈can-q-θ←θo←[S'↦unknown]
canθₛ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  | no  S'∉canθ-sigs'-q∥E⟦r⟧-θ←θo←[S] | no  S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (depar₂ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ S''∈can-q-θ←θo←[S'↦absent]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ˡ)
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ S''∈can-q-θ←θo←[S'↦absent]
canθₛ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  | no  S'∉canθ-sigs'-q∥E⟦r⟧-θ←θo←[S] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
  = ⊥-elim
      (S'∉canθ-sigs'-q∥E⟦r⟧-θ←θo←[S]
        (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (epar₂ q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]))
canθₛ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbq _ _ _ _ _) FV≠sigs'
  S'' S''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  | yes S'∈canθ-sigs'-q∥E⟦r⟧-θ←θo←[S] | no  S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (depar₂ dehole) (CBpar cbq CBnothing distinct-empty-right distinct-empty-right
                                               distinct-empty-right (λ _ _ ()))
          (λ S''' S'''∈map-+-suc-S'-sigs' S'''∈FVq++[] →
            FV≠sigs' S''' (++ˡ (x∈xs++[]→x∈xs {xs = proj₁ FVp} S'''∈FVq++[]))
              (there S'''∈map-+-suc-S'-sigs'))
          (S' ₛ) (λ S'∈FVq++[] → FV≠sigs' S' (++ˡ (x∈xs++[]→x∈xs {xs = proj₁ FVp} S'∈FVq++[])) (here refl))
          S'∈canθ-sigs'-q∥E⟦r⟧-θ←θo←[S]))


canθₛ-mergeˡ-E-induction-base-seq : ∀ {E q E⟦nothin⟧>>q BV FV} sigs' S' r θ θo →
  E⟦nothin⟧>>q ≐ (eseq q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧>>q BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
  ∀ S'' →
    S'' ∈ Canθₛ sigs' S' ((E ⟦ r ⟧e) >> q) (θ ← θo) →
      S'' ∈ Canθₛ sigs' S' (E ⟦ r ⟧e) (θ ← θo) ⊎
      (S'' ∈ Canₛ q (θ ← θo) × Code.nothin ∈ Canθₖ sigs' S' (E ⟦ r ⟧e) (θ ← θo))
canθₛ-mergeˡ-E-induction-base-seq {E} {q} [] S' r θ θo
  E⟦nothin⟧>>q cb FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r ⟧e) (θ ← θo))
... | no  nothin∉can-E⟦r⟧-θ←θo = inj₁ S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | yes nothin∈can-E⟦r⟧-θ←θo
  with ++⁻ (Canₛ (E ⟦ r ⟧e) (θ ← θo)) S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ S''∈can-E⟦r⟧-θ←θo = inj₁ S''∈can-E⟦r⟧-θ←θo
... | inj₂ S''∈can-q-θ←θo = inj₂ (S''∈can-q-θ←θo ,′ nothin∈can-E⟦r⟧-θ←θo)
canθₛ-mergeˡ-E-induction-base-seq {E} {q} (nothing ∷ sigs') S' r θ θo E⟦nothin⟧>>q
  cb FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
  = canθₛ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ θo
      E⟦nothin⟧>>q cb FV≠sigs' S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
canθₛ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.present ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-present (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ (θo ← [S]-env-present (S' ₛ))
         (deseq E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present]
... | inj₂ (S''∈can-q-θ←θo←[S'↦present] , nothin∈can-E⟦r⟧-θ←θo←[S'↦present])
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-present (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.present FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-present (S' ₛ))
  = inj₂ (S''∈can-q-θ←θo←[S'↦present] , nothin∈can-E⟦r⟧-θ←θo←[S'↦present])
canθₛ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.absent ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (deseq E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ (S''∈can-q-θ←θo←[S'↦absent] , nothin∈can-E⟦r⟧-θ←θo←[S'↦absent])
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ (S''∈can-q-θ←θo←[S'↦absent] , nothin∈can-E⟦r⟧-θ←θo←[S'↦absent])
canθₛ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  with any (_≟_ S') (Canθₛ sigs' (suc S') ((E ⟦ r ⟧e) >> q) ((θ ← θo) ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) ((θ ← θo) ← [S]-env (S' ₛ)))
canθₛ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  | yes S'∈canθ-sigs'-E⟦r⟧>>q-θ←θo←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S']
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ (θo ← [S]-env (S' ₛ))
         (deseq E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown]
... | inj₂ (S''∈can-q-θ←θo←[S'↦unknown] , nothin∈can-E⟦r⟧-θ←θo←[S'↦unknown])
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.unknown FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env (S' ₛ))
  = inj₂ (S''∈can-q-θ←θo←[S'↦unknown] , nothin∈can-E⟦r⟧-θ←θo←[S'↦unknown])
canθₛ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  | no S'∉canθ-sigs'-E⟦r⟧>>q-θ←θo←[S'] | no S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S']
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (deseq E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ S''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ (S''∈can-q-θ←θo←[S'↦absent] , nothin∈can-E⟦r⟧-θ←θo←[S'↦absent])
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ (S''∈can-q-θ←θo←[S'↦absent] , nothin∈can-E⟦r⟧-θ←θo←[S'↦absent])
canθₛ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  | no S'∉canθ-sigs'-E⟦r⟧>>q-θ←θo←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S']
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧>>q-θ←θo←[S']
        (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (eseq q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S']))
canθₛ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  S'' S''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  | yes S'∈canθ-sigs'-E⟦r⟧>>q-θ←θo←[S'] | no S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S']
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S']
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (deseq dehole) (CBseq CBnothing cbq distinct-empty-left)
          (dist'++ʳ {V2 = proj₁ FVp} (distinct'-sym (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')))
          (S' ₛ) (λ S'∈FVq → FV≠sigs' S' (++ʳ (proj₁ FVp) S'∈FVq) (here refl))
          S'∈canθ-sigs'-E⟦r⟧>>q-θ←θo←[S']))


canθₛₕ-mergeˡ-E-induction-base-par₁ : ∀ {E q E⟦nothin⟧∥q BV FV} sigs' S' r θ θo →
  E⟦nothin⟧∥q ≐ (epar₁ q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧∥q BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
  ∀ s'' →
    s'' ∈ Canθₛₕ sigs' S' ((E ⟦ r ⟧e) ∥ q) (θ ← θo) →
    s'' ∈ Canθₛₕ sigs' S' (E ⟦ r ⟧e) (θ ← θo) ⊎ s'' ∈ Canₛₕ q (θ ← θo)
canθₛₕ-mergeˡ-E-induction-base-par₁ {E} [] S' r θ θo
  E⟦nothin⟧∥q cb FV≠sigs' s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  with ++⁻ (Canₛₕ (E ⟦ r ⟧e) (θ ← θo)) s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ s''∈can-E⟦r⟧-θ←θo = inj₁ s''∈can-E⟦r⟧-θ←θo
... | inj₂ s''∈can-q-θ←θo = inj₂ s''∈can-q-θ←θo
canθₛₕ-mergeˡ-E-induction-base-par₁ (nothing ∷ sigs') S' r θ θo
  E⟦nothin⟧∥q cb FV≠sigs' s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
  = canθₛₕ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ θo E⟦nothin⟧∥q cb
      FV≠sigs' s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
canθₛₕ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.present ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-present (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ (θo ← [S]-env-present (S' ₛ))
         (depar₁ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present]
... | inj₂ s''∈can-q-θ←θo←[S'↦present]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-present (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.present FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-present (S' ₛ))
  = inj₂ s''∈can-q-θ←θo←[S'↦present]
canθₛₕ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.absent ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (depar₁ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ s''∈can-q-θ←θo←[S'↦absent]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ s''∈can-q-θ←θo←[S'↦absent]
canθₛₕ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb FV≠sigs' s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  with any (_≟_ S') (Canθₛ sigs' (suc S') ((E ⟦ r ⟧e) ∥ q) ((θ ← θo) ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) ((θ ← θo) ← [S]-env (S' ₛ)))
canθₛₕ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  | yes S'∈canθ-sigs'-E⟦r⟧∥q-θ←θo←[S] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ (θo ← [S]-env (S' ₛ))
         (depar₁ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown]
... | inj₂ s''∈can-q-θ←θo←[S'↦unknown]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.unknown FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env (S' ₛ))
  = inj₂ s''∈can-q-θ←θo←[S'↦unknown]
canθₛₕ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  | no  S'∉canθ-sigs'-E⟦r⟧∥q-θ←θo←[S] | no  S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-par₁ sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (depar₁ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ s''∈can-q-θ←θo←[S'↦absent]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ s''∈can-q-θ←θo←[S'↦absent]
canθₛₕ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  | no  S'∉canθ-sigs'-E⟦r⟧∥q-θ←θo←[S] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧∥q-θ←θo←[S]
        (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (epar₁ q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]))
canθₛₕ-mergeˡ-E-induction-base-par₁ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₁ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbp cbq _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧∥q-θ←θo
  | yes S'∈canθ-sigs'-E⟦r⟧∥q-θ←θo←[S] | no  S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (depar₁ dehole) (CBpar CBnothing cbq distinct-empty-left distinct-empty-left
                                               distinct-empty-left (λ _ ()))
          (dist'++ʳ {V2 = proj₁ FVp} (distinct'-sym (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')))
          (S' ₛ) (λ S'∈FVq → FV≠sigs' S' (++ʳ (proj₁ FVp) S'∈FVq) (here refl))
          S'∈canθ-sigs'-E⟦r⟧∥q-θ←θo←[S]))


canθₛₕ-mergeˡ-E-induction-base-par₂ : ∀ {E q q∥E⟦nothin⟧ BV FV} sigs' S' r θ θo →
  q∥E⟦nothin⟧ ≐ (epar₂ q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding q∥E⟦nothin⟧ BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
  ∀ s'' →
    s'' ∈ Canθₛₕ sigs' S' (q ∥ (E ⟦ r ⟧e)) (θ ← θo) →
    s'' ∈ Canθₛₕ sigs' S' (E ⟦ r ⟧e) (θ ← θo) ⊎ s'' ∈ Canₛₕ q (θ ← θo)
canθₛₕ-mergeˡ-E-induction-base-par₂ {E} {q} [] S' r θ θo
  q∥E⟦nothin⟧ cb FV≠sigs' s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  with ++⁻ (Canₛₕ q (θ ← θo)) s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₂ s''∈can-E⟦r⟧-θ←θo = inj₁ s''∈can-E⟦r⟧-θ←θo
... | inj₁ s''∈can-q-θ←θo = inj₂ s''∈can-q-θ←θo
canθₛₕ-mergeˡ-E-induction-base-par₂ (nothing ∷ sigs') S' r θ θo
  q∥E⟦nothin⟧ cb FV≠sigs' s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
  = canθₛₕ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ θo q∥E⟦nothin⟧ cb
      FV≠sigs' s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
canθₛₕ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.present ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-present (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ (θo ← [S]-env-present (S' ₛ))
         (depar₂ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present]
... | inj₂ s''∈can-q-θ←θo←[S'↦present]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-present (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ˡ)
              (distinct'-S∷Ss⇒[S] Signal.present FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-present (S' ₛ))
  = inj₂ s''∈can-q-θ←θo←[S'↦present]
canθₛₕ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.absent ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (depar₂ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ s''∈can-q-θ←θo←[S'↦absent]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ˡ)
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ s''∈can-q-θ←θo←[S'↦absent]
canθₛₕ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb FV≠sigs' s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  with any (_≟_ S') (Canθₛ sigs' (suc S') (q ∥ (E ⟦ r ⟧e)) ((θ ← θo) ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) ((θ ← θo) ← [S]-env (S' ₛ)))
canθₛₕ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  | yes S'∈canθ-sigs'-q∥E⟦r⟧-θ←θo←[S] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ (θo ← [S]-env (S' ₛ))
         (depar₂ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown]
... | inj₂ s''∈can-q-θ←θo←[S'↦unknown]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ˡ)
              (distinct'-S∷Ss⇒[S] Signal.unknown FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env (S' ₛ))
  = inj₂ s''∈can-q-θ←θo←[S'↦unknown]
canθₛₕ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  | no  S'∉canθ-sigs'-q∥E⟦r⟧-θ←θo←[S] | no  S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-par₂ sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (depar₂ E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ s''∈can-q-θ←θo←[S'↦absent]
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ˡ)
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ s''∈can-q-θ←θo←[S'↦absent]
canθₛₕ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar cbq _ _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  | no  S'∉canθ-sigs'-q∥E⟦r⟧-θ←θo←[S] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
  = ⊥-elim
      (S'∉canθ-sigs'-q∥E⟦r⟧-θ←θo←[S]
        (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (epar₂ q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S]))
canθₛₕ-mergeˡ-E-induction-base-par₂ {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbq _ _ _ _ _) FV≠sigs'
  s'' s''∈canθ-sigs'-q∥E⟦r⟧-θ←θo
  | yes S'∈canθ-sigs'-q∥E⟦r⟧-θ←θo←[S] | no  S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S]
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (depar₂ dehole) (CBpar cbq CBnothing distinct-empty-right distinct-empty-right
                                               distinct-empty-right (λ _ _ ()))
          (λ s''' s'''∈map-+-suc-S'-sigs' s'''∈FVq++[] →
            FV≠sigs' s''' (++ˡ (x∈xs++[]→x∈xs {xs = proj₁ FVp} s'''∈FVq++[]))
              (there s'''∈map-+-suc-S'-sigs'))
          (S' ₛ) (λ S'∈FVq++[] → FV≠sigs' S' (++ˡ (x∈xs++[]→x∈xs {xs = proj₁ FVp} S'∈FVq++[])) (here refl))
          S'∈canθ-sigs'-q∥E⟦r⟧-θ←θo←[S]))


canθₛₕ-mergeˡ-E-induction-base-seq : ∀ {E q E⟦nothin⟧>>q BV FV} sigs' S' r θ θo →
  E⟦nothin⟧>>q ≐ (eseq q ∷ E) ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧>>q BV FV →
  distinct' (proj₁ FV) (map (_+_ S') (SigMap.keys sigs')) →
  ∀ s'' →
    s'' ∈ Canθₛₕ sigs' S' ((E ⟦ r ⟧e) >> q) (θ ← θo) →
      s'' ∈ Canθₛₕ sigs' S' (E ⟦ r ⟧e) (θ ← θo) ⊎
      (s'' ∈ Canₛₕ q (θ ← θo) × Code.nothin ∈ Canθₖ sigs' S' (E ⟦ r ⟧e) (θ ← θo))
canθₛₕ-mergeˡ-E-induction-base-seq {E} {q} [] S' r θ θo
  E⟦nothin⟧>>q cb FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r ⟧e) (θ ← θo))
... | no  nothin∉can-E⟦r⟧-θ←θo = inj₁ s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | yes nothin∈can-E⟦r⟧-θ←θo
  with ++⁻ (Canₛₕ (E ⟦ r ⟧e) (θ ← θo)) s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ s''∈can-E⟦r⟧-θ←θo = inj₁ s''∈can-E⟦r⟧-θ←θo
... | inj₂ s''∈can-q-θ←θo = inj₂ (s''∈can-q-θ←θo ,′ nothin∈can-E⟦r⟧-θ←θo)
canθₛₕ-mergeˡ-E-induction-base-seq {E} {q} (nothing ∷ sigs') S' r θ θo E⟦nothin⟧>>q
  cb FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
  = canθₛₕ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ θo
      E⟦nothin⟧>>q cb FV≠sigs' s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
canθₛₕ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.present ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-present (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ (θo ← [S]-env-present (S' ₛ))
         (deseq E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦present]
... | inj₂ (s''∈can-q-θ←θo←[S'↦present] , nothin∈can-E⟦r⟧-θ←θo←[S'↦present])
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-present (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.present FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-present (S' ₛ))
  = inj₂ (s''∈can-q-θ←θo←[S'↦present] , nothin∈can-E⟦r⟧-θ←θo←[S'↦present])
canθₛₕ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.absent ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (deseq E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ (s''∈can-q-θ←θo←[S'↦absent] , nothin∈can-E⟦r⟧-θ←θo←[S'↦absent])
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ (s''∈can-q-θ←θo←[S'↦absent] , nothin∈can-E⟦r⟧-θ←θo←[S'↦absent])
canθₛₕ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  with any (_≟_ S') (Canθₛ sigs' (suc S') ((E ⟦ r ⟧e) >> q) ((θ ← θo) ← [S]-env (S' ₛ)))
     | any (_≟_ S') (Canθₛ sigs' (suc S') (E ⟦ r ⟧e) ((θ ← θo) ← [S]-env (S' ₛ)))
canθₛₕ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  | yes S'∈canθ-sigs'-E⟦r⟧>>q-θ←θo←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S']
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ (θo ← [S]-env (S' ₛ))
         (deseq E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦unknown]
... | inj₂ (s''∈can-q-θ←θo←[S'↦unknown] , nothin∈can-E⟦r⟧-θ←θo←[S'↦unknown])
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.unknown FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env (S' ₛ))
  = inj₂ (s''∈can-q-θ←θo←[S'↦unknown] , nothin∈can-E⟦r⟧-θ←θo←[S'↦unknown])
canθₛₕ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  | no S'∉canθ-sigs'-E⟦r⟧>>q-θ←θo←[S'] | no S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S']
  rewrite sym (Env.←-assoc θ θo ([S]-env-absent (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
  with canθₛₕ-mergeˡ-E-induction-base-seq sigs' (suc S') r θ (θo ← [S]-env-absent (S' ₛ))
         (deseq E⟦nothin⟧) cb (dist'++ʳ {V2 = S' + 0 ∷ []} FV≠sigs')
         s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
... | inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent] =
  inj₁ s''∈canθ-sigs'-E⟦r⟧-θ←θo←[S'↦absent]
... | inj₂ (s''∈can-q-θ←θo←[S'↦absent] , nothin∈can-E⟦r⟧-θ←θo←[S'↦absent])
  rewrite +-comm S' 0
        | can-irr (θ ← θo) ([S]-env-absent (S' ₛ)) q cbq
            (distinct'-to-left (dist'++ʳ {V2 = proj₁ FVp})
              (distinct'-S∷Ss⇒[S] Signal.absent FV≠sigs'))
        | Env.←-assoc θ θo ([S]-env-absent (S' ₛ))
  = inj₂ (s''∈can-q-θ←θo←[S'↦absent] , nothin∈can-E⟦r⟧-θ←θo←[S'↦absent])
canθₛₕ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  | no S'∉canθ-sigs'-E⟦r⟧>>q-θ←θo←[S'] | yes S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S']
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧>>q-θ←θo←[S']
        (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (eseq q) (E ⟦ r ⟧e) (S' ₛ) S'∈canθ-sigs'-E⟦r⟧-θ←θo←[S']))
canθₛₕ-mergeˡ-E-induction-base-seq {E} {q} (just Signal.unknown ∷ sigs') S' r θ θo
  (deseq E⟦nothin⟧) cb@(CBseq {FVp = FVp} _ cbq _) FV≠sigs'
  s'' s''∈canθ-sigs'-E⟦r⟧>>q-θ←θo
  | yes S'∈canθ-sigs'-E⟦r⟧>>q-θ←θo←[S'] | no S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S']
  rewrite sym (Env.←-assoc θ θo ([S]-env (S' ₛ)))
        | map-+-compose-suc S' (SigMap.keys sigs')
        | +-comm S' 0
  = ⊥-elim
      (S'∉canθ-sigs'-E⟦r⟧-θ←θo←[S']
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs' (suc S') (θ ← (θo ← [S]-env (S' ₛ)))
          (deseq dehole) (CBseq CBnothing cbq distinct-empty-left)
          (dist'++ʳ {V2 = proj₁ FVp} (distinct'-sym (dist'++ʳ {V2 = S' ∷ []} FV≠sigs')))
          (S' ₛ) (λ S'∈FVq → FV≠sigs' S' (++ʳ (proj₁ FVp) S'∈FVq) (here refl))
          S'∈canθ-sigs'-E⟦r⟧>>q-θ←θo←[S']))
