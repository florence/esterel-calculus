module Esterel.Lang.PotentialFunction.MergePotentialRuleLeftInductive where

open import utility
  renaming (_U̬_ to _∪_ ; _|̌_ to _-_)

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.PotentialFunction
open import Esterel.Lang.PotentialFunction.Base
open import Esterel.Lang.PotentialFunction.CanThetaContinuation
open import Esterel.Lang.PotentialFunction.MergePotentialRuleCan
open import Esterel.Lang.PotentialFunction.MergePotentialRuleLeftBase
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


canθₖ-mergeˡ-E-induction : ∀ {E E⟦nothin⟧ BV FV} sigs' shrs' vars' r θ →
  E⟦nothin⟧ ≐ E ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧ BV FV →
  distinct' (SigMap.keys sigs') (proj₁ FV) →
    Canθₖ sigs' 0 (E ⟦ r ⟧e) θ ≡
    Canₖ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ


canθₖ-mergeˡ-sigs-induction : ∀ {E E⟦nothin⟧ BV FV} sigs S sigs' shrs' vars' r θ →
  E⟦nothin⟧ ≐ E ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧ BV FV →
  distinct' (SigMap.keys sigs') (proj₁ FV) →
  ∀ k →
    k ∈ proj₁ (proj₂ (Canθ' sigs S (Canθ sigs' 0 (E ⟦ r ⟧e)) θ)) →
    k ∈ Canθₖ sigs S (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ


canθₛ-mergeˡ-E-induction : ∀ {E E⟦nothin⟧ BV FV} sigs' shrs' vars' r θ →
  E⟦nothin⟧ ≐ E ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧ BV FV →
  distinct' (SigMap.keys sigs') (proj₁ FV) →
  ∀ S' →
    S' ∉ SigMap.keys sigs' →
    S' ∈ Canθₛ sigs' 0 (E ⟦ r ⟧e) θ →
    S' ∈ Canₛ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ
canθₛ-mergeˡ-E-induction {[]} sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV
  S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ =
    set-subtract-notin S'∈canθ-sigs'-E⟦r⟧-θ S'∉sigs'
canθₛ-mergeˡ-E-induction {epar₁ q ∷ E} sigs' shrs' vars' r θ
  (depar₁ E⟦nothin⟧) cb@(CBpar cbp _ _ _ _ _) sigs'≠FV
  S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
  rewrite Env.←-comm Env.[]env θ distinct-empty-left
  with canθₛ-mergeˡ-E-induction-base-par₁ sigs' 0 r θ Env.[]env (depar₁ E⟦nothin⟧) cb
         (subst (distinct' _)
           (sym (map-id (SigMap.keys sigs')))
           (distinct'-sym sigs'≠FV))
         S' S'∈canθ-sigs'-E⟦r⟧-θ
... | inj₁ S'∈canθ'-sigs'-E⟦r⟧-θ←[] =
  ++ˡ (canθₛ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
        E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV)
        S' S'∉sigs' S'∈canθ'-sigs'-E⟦r⟧-θ←[])
... | inj₂ S'∈can-q-θ←[] =
  ++ʳ (Canₛ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) (θ ← Env.[]env))
    S'∈can-q-θ←[]
canθₛ-mergeˡ-E-induction {epar₂ p ∷ E} sigs' shrs' vars' r θ
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) sigs'≠FV
  S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
  rewrite Env.←-comm Env.[]env θ distinct-empty-left
  with canθₛ-mergeˡ-E-induction-base-par₂ sigs' 0 r θ Env.[]env (depar₂ E⟦nothin⟧) cb
         (subst (distinct' _)
           (sym (map-id (SigMap.keys sigs')))
           (distinct'-sym sigs'≠FV))
         S' S'∈canθ-sigs'-E⟦r⟧-θ
... | inj₁ S'∈canθ'-sigs'-E⟦r⟧-θ←[] =
  ++ʳ (Canₛ p (θ ← Env.[]env))
      (canθₛ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
        E⟦nothin⟧ cbq (dist'++ʳ {V2 = proj₁ FVp} sigs'≠FV)
        S' S'∉sigs' S'∈canθ'-sigs'-E⟦r⟧-θ←[])
... | inj₂ S'∈can-q-θ←[] =
  ++ˡ S'∈can-q-θ←[]
canθₛ-mergeˡ-E-induction {eseq q ∷ E} sigs' shrs' vars' r θ
  (deseq E⟦nothin⟧) cb@(CBseq cbp _ _) sigs'≠FV
  S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
  rewrite Env.←-comm Env.[]env θ distinct-empty-left
  with canθₛ-mergeˡ-E-induction-base-seq sigs' 0 r θ Env.[]env (deseq E⟦nothin⟧) cb
         (subst (distinct' _)
           (sym (map-id (SigMap.keys sigs')))
           (distinct'-sym sigs'≠FV))
         S' S'∈canθ-sigs'-E⟦r⟧-θ
canθₛ-mergeˡ-E-induction {eseq q ∷ E} sigs' shrs' vars' r θ
  (deseq E⟦nothin⟧) cb@(CBseq cbp _ _) sigs'≠FV
  S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
  | inj₁ S'∈canθ'-sigs'-E⟦r⟧-θ←[]
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) (θ ← Env.[]env))
... | yes nothin∈can-E⟦ρΘ⟧-θ←[] =
  ++ˡ (canθₛ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
        E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV)
        S' S'∉sigs' S'∈canθ'-sigs'-E⟦r⟧-θ←[])
... | no  nothin∉can-E⟦ρΘ⟧-θ←[] =
  canθₛ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
    E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV)
    S' S'∉sigs' S'∈canθ'-sigs'-E⟦r⟧-θ←[]
canθₛ-mergeˡ-E-induction {eseq q ∷ E} sigs' shrs' vars' r θ
  (deseq E⟦nothin⟧) cb@(CBseq cbp _ _) sigs'≠FV
  S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
  | inj₂ (S'∈can-q-θ←[] , nothin∈canθ-sigs'-E⟦r⟧-θ←[])
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) (θ ← Env.[]env))
... | yes nothin∈can-E⟦ρΘ⟧-θ←[] =
  ++ʳ (Canₛ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) (θ ← Env.[]env))
    S'∈can-q-θ←[]
... | no  nothin∉can-E⟦ρΘ⟧-θ←[]
  rewrite canθₖ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
            E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV)
  = ⊥-elim (nothin∉can-E⟦ρΘ⟧-θ←[] nothin∈canθ-sigs'-E⟦r⟧-θ←[])
canθₛ-mergeˡ-E-induction {eloopˢ q ∷ E} sigs' shrs' vars' r θ
  (deloopˢ E⟦nothin⟧) cb@(CBloopˢ cbp cbq _ _) sigs'≠FV
  S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
  rewrite unfold sigs' 0 (loopˢ (E ⟦ r ⟧e) q) θ
        | sym (unfold sigs' 0 (E ⟦ r ⟧e) θ)
  = canθₛ-mergeˡ-E-induction sigs' shrs' vars' r θ E⟦nothin⟧ cbp
      (dist'++ˡ sigs'≠FV)
      S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
canθₛ-mergeˡ-E-induction {esuspend S ∷ E} sigs' shrs' vars' r θ
  (desuspend E⟦nothin⟧) cb@(CBsusp cb' _) sigs'≠FV
  S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
  rewrite unfold sigs' 0 (suspend (E ⟦ r ⟧e) S) θ
        | sym (unfold sigs' 0 (E ⟦ r ⟧e) θ)
  = canθₛ-mergeˡ-E-induction sigs' shrs' vars' r θ E⟦nothin⟧ cb'
      (dist'++ʳ {V2 = Signal.unwrap S ∷ []} sigs'≠FV)
      S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
canθₛ-mergeˡ-E-induction {etrap ∷ E} sigs' shrs' vars' r θ
  (detrap E⟦nothin⟧) cb@(CBtrap cb') sigs'≠FV
  S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ
  rewrite unfold sigs' 0 (trap (E ⟦ r ⟧e)) θ
        | canθ'-map-comm (map Code.↓*) sigs' 0 (Can (E ⟦ r ⟧e)) θ
        | sym (unfold sigs' 0 (E ⟦ r ⟧e) θ)
  = canθₛ-mergeˡ-E-induction sigs' shrs' vars' r θ E⟦nothin⟧ cb' sigs'≠FV
      S' S'∉sigs' S'∈canθ-sigs'-E⟦r⟧-θ


canθₛ-mergeˡ-sigs-induction : ∀ {E E⟦nothin⟧ BV FV} sigs S sigs' shrs' vars' r θ →
  E⟦nothin⟧ ≐ E ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧ BV FV →
  distinct' (SigMap.keys sigs') (proj₁ FV) →
  ∀ S' →
    S' ∉ SigMap.keys sigs' →
    S' ∈ proj₁ (Canθ' sigs S (Canθ sigs' 0 (E ⟦ r ⟧e)) θ) →
    S' ∈ Canθₛ sigs S (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ
canθₛ-mergeˡ-sigs-induction [] S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₛ-mergeˡ-E-induction sigs' shrs' vars'
      r θ E⟦nothin⟧ cb sigs'≠FV
      S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₛ-mergeˡ-sigs-induction (nothing ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r θ E⟦nothin⟧ cb sigs'≠FV
      S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₛ-mergeˡ-sigs-induction (just Signal.present ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r (θ ← [S]-env-present (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
      S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₛ-mergeˡ-sigs-induction (just Signal.absent ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
      S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₛ-mergeˡ-sigs-induction {E} (just Signal.unknown ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
  with any (_≟_ S) (proj₁
                     (Canθ' sigs (suc S) (Canθ sigs' 0 (E ⟦ r ⟧e))
                       (θ ← [S]-env (S ₛ))))
     | any (_≟_ S) (proj₁
                     (Canθ sigs (suc S) (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e)
                       (θ ← [S]-env (S ₛ))))
... | yes S∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | yes S∈canθ-sigs-E⟦ρΘsigs'⟧-θ←[S] =
  canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
    r (θ ← [S]-env (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
    S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
... | no  S∉canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | no  S∉canθ-sigs-E⟦ρΘsigs'⟧-θ←[S] =
  canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
    r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
    S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
... | no  S∉canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | yes S∈canθ-sigs-E⟦ρΘsigs'⟧-θ←[S] =
  canθₛ-add-sig-monotonic sigs (suc S) (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ
    (S ₛ) Signal.absent S'
    (canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
      S' S'∉sigs' S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ)
... | yes S∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | no  S∉canθ-sigs-E⟦ρΘsigs'⟧-θ←[S]
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs' =
  canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
    r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
    S' S'∉sigs'
    (subst (S' ∈_)
      (cong proj₁
        (trans
          (canθ'-inner-shadowing-irr sigs (suc S) sigs' (E ⟦ r ⟧e)
            S Signal.unknown θ S∈sigs')
          (sym (canθ'-inner-shadowing-irr sigs (suc S) sigs' (E ⟦ r ⟧e)
                 S Signal.absent θ S∈sigs'))))
      S'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ)
... | no  S∉sigs' =
  ⊥-elim
    (S∉canθ-sigs-E⟦ρΘsigs'⟧-θ←[S]
      (canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
        r (θ ← [S]-env (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
        S S∉sigs' S∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S]))


canθₛₕ-mergeˡ-E-induction : ∀ {E E⟦nothin⟧ BV FV} sigs' shrs' vars' r θ →
  E⟦nothin⟧ ≐ E ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧ BV FV →
  distinct' (SigMap.keys sigs') (proj₁ FV) →
  ∀ s' →
    s' ∉ ShrMap.keys shrs' →
    s' ∈ Canθₛₕ sigs' 0 (E ⟦ r ⟧e) θ →
    s' ∈ Canₛₕ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ
canθₛₕ-mergeˡ-E-induction {[]} sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV
  s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ =
    set-subtract-notin s'∈canθ-sigs'-E⟦r⟧-θ s'∉shrs'
canθₛₕ-mergeˡ-E-induction {epar₁ q ∷ E} sigs' shrs' vars' r θ
  (depar₁ E⟦nothin⟧) cb@(CBpar cbp _ _ _ _ _) sigs'≠FV
  s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
  rewrite Env.←-comm Env.[]env θ distinct-empty-left
  with canθₛₕ-mergeˡ-E-induction-base-par₁ sigs' 0 r θ Env.[]env (depar₁ E⟦nothin⟧) cb
         (subst (distinct' _)
           (sym (map-id (SigMap.keys sigs')))
           (distinct'-sym sigs'≠FV))
         s' s'∈canθ-sigs'-E⟦r⟧-θ
... | inj₁ s'∈canθ'-sigs'-E⟦r⟧-θ←[] =
  ++ˡ (canθₛₕ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
        E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV)
        s' s'∉shrs' s'∈canθ'-sigs'-E⟦r⟧-θ←[])
... | inj₂ s'∈can-q-θ←[] =
  ++ʳ (Canₛₕ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) (θ ← Env.[]env))
    s'∈can-q-θ←[]
canθₛₕ-mergeˡ-E-induction {epar₂ p ∷ E} sigs' shrs' vars' r θ
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} _ cbq _ _ _ _) sigs'≠FV
  s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
  rewrite Env.←-comm Env.[]env θ distinct-empty-left
  with canθₛₕ-mergeˡ-E-induction-base-par₂ sigs' 0 r θ Env.[]env (depar₂ E⟦nothin⟧) cb
         (subst (distinct' _)
           (sym (map-id (SigMap.keys sigs')))
           (distinct'-sym sigs'≠FV))
         s' s'∈canθ-sigs'-E⟦r⟧-θ
... | inj₁ s'∈canθ'-sigs'-E⟦r⟧-θ←[] =
  ++ʳ (Canₛₕ p (θ ← Env.[]env))
      (canθₛₕ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
        E⟦nothin⟧ cbq (dist'++ʳ {V2 = proj₁ FVp} sigs'≠FV)
        s' s'∉shrs' s'∈canθ'-sigs'-E⟦r⟧-θ←[])
... | inj₂ s'∈can-q-θ←[] =
  ++ˡ s'∈can-q-θ←[]
canθₛₕ-mergeˡ-E-induction {eseq q ∷ E} sigs' shrs' vars' r θ
  (deseq E⟦nothin⟧) cb@(CBseq cbp _ _) sigs'≠FV
  s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
  rewrite Env.←-comm Env.[]env θ distinct-empty-left
  with canθₛₕ-mergeˡ-E-induction-base-seq sigs' 0 r θ Env.[]env (deseq E⟦nothin⟧) cb
         (subst (distinct' _)
           (sym (map-id (SigMap.keys sigs')))
           (distinct'-sym sigs'≠FV))
         s' s'∈canθ-sigs'-E⟦r⟧-θ
canθₛₕ-mergeˡ-E-induction {eseq q ∷ E} sigs' shrs' vars' r θ
  (deseq E⟦nothin⟧) cb@(CBseq cbp _ _) sigs'≠FV
  s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
  | inj₁ s'∈canθ'-sigs'-E⟦r⟧-θ←[]
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) (θ ← Env.[]env))
... | yes nothin∈can-E⟦ρΘ⟧-θ←[] =
  ++ˡ (canθₛₕ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
        E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV)
        s' s'∉shrs' s'∈canθ'-sigs'-E⟦r⟧-θ←[])
... | no  nothin∉can-E⟦ρΘ⟧-θ←[] =
  canθₛₕ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
    E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV)
    s' s'∉shrs' s'∈canθ'-sigs'-E⟦r⟧-θ←[]
canθₛₕ-mergeˡ-E-induction {eseq q ∷ E} sigs' shrs' vars' r θ
  (deseq E⟦nothin⟧) cb@(CBseq cbp _ _) sigs'≠FV
  s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
  | inj₂ (s'∈can-q-θ←[] , nothin∈canθ-sigs'-E⟦r⟧-θ←[])
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) (θ ← Env.[]env))
... | yes nothin∈can-E⟦ρΘ⟧-θ←[] =
  ++ʳ (Canₛₕ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) (θ ← Env.[]env))
    s'∈can-q-θ←[]
... | no  nothin∉can-E⟦ρΘ⟧-θ←[]
  rewrite canθₖ-mergeˡ-E-induction sigs' shrs' vars' r (θ ← Env.[]env)
            E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV)
  = ⊥-elim (nothin∉can-E⟦ρΘ⟧-θ←[] nothin∈canθ-sigs'-E⟦r⟧-θ←[])
canθₛₕ-mergeˡ-E-induction {eloopˢ q ∷ E} sigs' shrs' vars' r θ
  (deloopˢ E⟦nothin⟧) cb@(CBloopˢ cbp cbq _ _) sigs'≠FV
  s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
  rewrite unfold sigs' 0 (loopˢ (E ⟦ r ⟧e) q) θ
        | sym (unfold sigs' 0 (E ⟦ r ⟧e) θ)
  = canθₛₕ-mergeˡ-E-induction sigs' shrs' vars' r θ E⟦nothin⟧ cbp
      (dist'++ˡ sigs'≠FV)
      s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
canθₛₕ-mergeˡ-E-induction {esuspend S ∷ E} sigs' shrs' vars' r θ
  (desuspend E⟦nothin⟧) cb@(CBsusp cb' _) sigs'≠FV
  s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
  rewrite unfold sigs' 0 (suspend (E ⟦ r ⟧e) S) θ
        | sym (unfold sigs' 0 (E ⟦ r ⟧e) θ)
  = canθₛₕ-mergeˡ-E-induction sigs' shrs' vars' r θ E⟦nothin⟧ cb'
      (dist'++ʳ {V2 = Signal.unwrap S ∷ []} sigs'≠FV)
      s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
canθₛₕ-mergeˡ-E-induction {etrap ∷ E} sigs' shrs' vars' r θ
  (detrap E⟦nothin⟧) cb@(CBtrap cb') sigs'≠FV
  s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ
  rewrite unfold sigs' 0 (trap (E ⟦ r ⟧e)) θ
        | canθ'-map-comm (map Code.↓*) sigs' 0 (Can (E ⟦ r ⟧e)) θ
        | sym (unfold sigs' 0 (E ⟦ r ⟧e) θ)
  = canθₛₕ-mergeˡ-E-induction sigs' shrs' vars' r θ E⟦nothin⟧ cb' sigs'≠FV
      s' s'∉shrs' s'∈canθ-sigs'-E⟦r⟧-θ


canθₛₕ-mergeˡ-sigs-induction : ∀ {E E⟦nothin⟧ BV FV} sigs S sigs' shrs' vars' r θ →
  E⟦nothin⟧ ≐ E ⟦ nothin ⟧e →
  CorrectBinding E⟦nothin⟧ BV FV →
  distinct' (SigMap.keys sigs') (proj₁ FV) →
  ∀ s' →
    s' ∉ ShrMap.keys shrs' →
    s' ∈ proj₂ (proj₂ (Canθ' sigs S (Canθ sigs' 0 (E ⟦ r ⟧e)) θ)) →
    s' ∈ Canθₛₕ sigs S (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ
canθₛₕ-mergeˡ-sigs-induction [] S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₛₕ-mergeˡ-E-induction sigs' shrs' vars'
      r θ E⟦nothin⟧ cb sigs'≠FV
      s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₛₕ-mergeˡ-sigs-induction (nothing ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₛₕ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r θ E⟦nothin⟧ cb sigs'≠FV
      s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₛₕ-mergeˡ-sigs-induction (just Signal.present ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₛₕ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r (θ ← [S]-env-present (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
      s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₛₕ-mergeˡ-sigs-induction (just Signal.absent ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₛₕ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
      s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₛₕ-mergeˡ-sigs-induction {E} (just Signal.unknown ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
  with any (_≟_ S) (proj₁
                     (Canθ' sigs (suc S) (Canθ sigs' 0 (E ⟦ r ⟧e))
                       (θ ← [S]-env (S ₛ))))
     | any (_≟_ S) (proj₁
                     (Canθ sigs (suc S) (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e)
                       (θ ← [S]-env (S ₛ))))
... | yes S∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | yes S∈canθ-sigs-E⟦ρΘsigs'⟧-θ←[S] =
  canθₛₕ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
    r (θ ← [S]-env (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
    s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
... | no  S∉canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | no  S∉canθ-sigs-E⟦ρΘsigs'⟧-θ←[S] =
  canθₛₕ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
    r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
    s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
... | no  S∉canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | yes S∈canθ-sigs-E⟦ρΘsigs'⟧-θ←[S] =
  canθₛₕ-add-sig-monotonic sigs (suc S) (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ
    (S ₛ) Signal.absent s'
    (canθₛₕ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
      s' s'∉shrs' s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ)
... | yes S∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | no  S∉canθ-sigs-E⟦ρΘsigs'⟧-θ←[S]
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs' =
  canθₛₕ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
    r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
    s' s'∉shrs'
    (subst (s' ∈_)
      (cong (proj₂ ∘ proj₂)
        (trans
          (canθ'-inner-shadowing-irr sigs (suc S) sigs' (E ⟦ r ⟧e)
            S Signal.unknown θ S∈sigs')
          (sym (canθ'-inner-shadowing-irr sigs (suc S) sigs' (E ⟦ r ⟧e)
                 S Signal.absent θ S∈sigs'))))
      s'∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ)
... | no  S∉sigs' =
  ⊥-elim
    (S∉canθ-sigs-E⟦ρΘsigs'⟧-θ←[S]
      (canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
        r (θ ← [S]-env (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
        S S∉sigs' S∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S]))


canθₖ-mergeˡ-E-induction {[]} sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV =
    refl
canθₖ-mergeˡ-E-induction {epar₁ q ∷ E} sigs' shrs' vars' r θ
  (depar₁ E⟦nothin⟧) cb@(CBpar cbp cbq _ _ _ _) sigs'≠FV
  rewrite canθₖ-mergeˡ-E-induction-base-par₁ sigs' 0 r θ
            (depar₁ E⟦nothin⟧) cb
            (subst (distinct' _)
              (sym (map-id (SigMap.keys sigs')))
              (distinct'-sym sigs'≠FV))
        | canθₖ-mergeˡ-E-induction sigs' shrs' vars' r θ
            E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV)
  = refl
canθₖ-mergeˡ-E-induction {epar₂ p ∷ E} sigs' shrs' vars' r θ
  (depar₂ E⟦nothin⟧) cb@(CBpar {FVp = FVp} cbp cbq _ _ _ _) sigs'≠FV
  rewrite canθₖ-mergeˡ-E-induction-base-par₂ sigs' 0 r θ
            (depar₂ E⟦nothin⟧) cb
            (subst (distinct' _)
              (sym (map-id (SigMap.keys sigs')))
              (distinct'-sym sigs'≠FV))
        | canθₖ-mergeˡ-E-induction sigs' shrs' vars' r θ
            E⟦nothin⟧ cbq (dist'++ʳ {V2 = proj₁ FVp} sigs'≠FV)
  = refl
canθₖ-mergeˡ-E-induction {eseq q ∷ E} sigs' shrs' vars' r θ
  (deseq E⟦nothin⟧) cb@(CBseq cbp cbq _) sigs'≠FV
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ)
... | no nothin∉can-E⟦ρΘ⟧-θ
  rewrite sym (canθₖ-mergeˡ-E-induction sigs' shrs' vars' r θ
                E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV))
        | canθₖ-mergeˡ-E-induction-base-seq-notin sigs' 0 r θ
            (deseq E⟦nothin⟧) cb
            (subst (distinct' _)
              (sym (map-id (SigMap.keys sigs')))
              (distinct'-sym sigs'≠FV))
            nothin∉can-E⟦ρΘ⟧-θ
  = refl
... | yes nothin∈can-E⟦ρΘ⟧-θ
  rewrite sym (canθₖ-mergeˡ-E-induction sigs' shrs' vars' r θ
                E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV))
        | canθₖ-mergeˡ-E-induction-base-seq-in sigs' 0 r θ
            (deseq E⟦nothin⟧) cb
            (subst (distinct' _)
              (sym (map-id (SigMap.keys sigs')))
              (distinct'-sym sigs'≠FV))
            nothin∈can-E⟦ρΘ⟧-θ
  = refl
canθₖ-mergeˡ-E-induction {eloopˢ q ∷ E} sigs' shrs' vars' r θ
  (deloopˢ E⟦nothin⟧) cb@(CBloopˢ cbp cbq _ _) sigs'≠FV
  rewrite sym (canθₖ-mergeˡ-E-induction sigs' shrs' vars' r θ
                E⟦nothin⟧ cbp (dist'++ˡ sigs'≠FV))
        | unfold sigs' 0 (loopˢ (E ⟦ r ⟧e) q) θ
        | unfold sigs' 0 (E ⟦ r ⟧e) θ
  = refl
canθₖ-mergeˡ-E-induction {esuspend S ∷ E} sigs' shrs' vars' r θ
  (desuspend E⟦nothin⟧) cb@(CBsusp cb' _) sigs'≠FV
  rewrite sym (canθₖ-mergeˡ-E-induction sigs' shrs' vars' r θ
                E⟦nothin⟧ cb' (dist'++ʳ {V2 = Signal.unwrap S ∷ []} sigs'≠FV))
        | unfold sigs' 0 (suspend (E ⟦ r ⟧e) S) θ
        | unfold sigs' 0 (E ⟦ r ⟧e) θ
  = refl
canθₖ-mergeˡ-E-induction {etrap ∷ E} sigs' shrs' vars' r θ
  (detrap E⟦nothin⟧) cb@(CBtrap cb') sigs'≠FV
  rewrite sym (canθₖ-mergeˡ-E-induction sigs' shrs' vars' r θ E⟦nothin⟧ cb' sigs'≠FV)
        | unfold sigs' 0 (trap (E ⟦ r ⟧e)) θ
        | unfold sigs' 0 (E ⟦ r ⟧e) θ
        | canθ'-map-comm (map Code.↓*) sigs' 0 (Can (E ⟦ r ⟧e)) θ
  = refl


canθₖ-mergeˡ-sigs-induction [] S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
  rewrite canθₖ-mergeˡ-E-induction sigs' shrs' vars'
            r θ E⟦nothin⟧ cb sigs'≠FV
  = k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₖ-mergeˡ-sigs-induction (nothing ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₖ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r θ E⟦nothin⟧ cb sigs'≠FV
      k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₖ-mergeˡ-sigs-induction (just Signal.present ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₖ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r (θ ← [S]-env-present (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
      k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₖ-mergeˡ-sigs-induction (just Signal.absent ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ =
    canθₖ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
      k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
canθₖ-mergeˡ-sigs-induction {E} (just Signal.unknown ∷ sigs) S sigs' shrs' vars' r θ
  E⟦nothin⟧ cb sigs'≠FV k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
  with any (_≟_ S) (proj₁
                     (Canθ' sigs (suc S) (Canθ sigs' 0 (E ⟦ r ⟧e))
                       (θ ← [S]-env (S ₛ))))
     | any (_≟_ S) (proj₁
                     (Canθ sigs (suc S) (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e)
                       (θ ← [S]-env (S ₛ))))
... | yes S∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | yes S∈canθ-sigs-E⟦ρΘsigs'⟧-θ←[S] =
  canθₖ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
    r (θ ← [S]-env (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
    k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
... | no  S∉canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | no  S∉canθ-sigs-E⟦ρΘsigs'⟧-θ←[S] =
  canθₖ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
    r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
    k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ
... | no  S∉canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | yes S∈canθ-sigs-E⟦ρΘsigs'⟧-θ←[S] =
  canθₖ-add-sig-monotonic sigs (suc S) (E ⟦ ρ Θ sigs' shrs' vars' · r ⟧e) θ
    (S ₛ) Signal.absent k
    (canθₖ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
      r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
      k k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ)
... | yes S∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S] | no  S∉canθ-sigs-E⟦ρΘsigs'⟧-θ←[S]
  with any (_≟_ S) (SigMap.keys sigs')
... | yes S∈sigs' =
  canθₖ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
    r (θ ← [S]-env-absent (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
    k
    (subst (k ∈_)
      (cong (proj₁ ∘ proj₂)
        (trans
          (canθ'-inner-shadowing-irr sigs (suc S) sigs' (E ⟦ r ⟧e)
            S Signal.unknown θ S∈sigs')
          (sym (canθ'-inner-shadowing-irr sigs (suc S) sigs' (E ⟦ r ⟧e)
                 S Signal.absent θ S∈sigs'))))
      k∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ)
... | no  S∉sigs' =
  ⊥-elim
    (S∉canθ-sigs-E⟦ρΘsigs'⟧-θ←[S]
      (canθₛ-mergeˡ-sigs-induction sigs (suc S) sigs' shrs' vars'
        r (θ ← [S]-env (S ₛ)) E⟦nothin⟧ cb sigs'≠FV
        S S∉sigs' S∈canθ'-sigs-canθ-sigs'-E⟦r⟧-θ←[S]))
