{-
The equivalent "goodness" of can w.r.t. the rmerge reduction.
The lemma proved in this file is

    can-irr : ∀ {BV} {FV} θ₁ θ₂ q →
      CorrectBinding q BV FV →
      (distinct' (proj₁ FV) (proj₁ (Dom θ₂))) →
       Can q θ₁ ≡ Can q (θ₁ ← θ₂)

That is, the result of the Can function will not change
provided that the program does not refer to any variables
in the new environment.

-}
module Esterel.Lang.CanFunction.MergePotentialRuleCan where

open import utility

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.CanFunction
open import Esterel.Lang.CanFunction.Base
open import Esterel.Context
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

open import Data.Bool
  using (Bool ; true ; false ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.List.Properties
  using (map-id)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using ()
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_)
open import Data.Nat.Properties.Simple
  using (+-comm)
open import Data.Product
  using (Σ ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; _∋_ ; id)
open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; sym ; cong ; subst)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open ListSet Data.Nat._≟_
  using (set-subtract ; set-subtract-[] ; set-subtract-split ; set-subtract-merge
       ; set-subtract-notin
       ; set-remove-mono-∈ ; set-remove-removed ; set-remove-not-removed)

can-new-irr : ∀ {BV} {FV} θ₁ θ₂ θo q →
  CorrectBinding q BV FV →
  (∀ S' → S' ∈ (proj₁ FV) → (S' ∉ proj₁ (Dom θ₂)) ⊎ (S' ∈ proj₁ (Dom θo))) →
  Can q (θ₁ ← θo) ≡ Can q ((θ₁ ← θ₂) ← θo)

canθ-new-irr : ∀ {BV} {FV} sigs S θ₁ θ₂ θo q →
  CorrectBinding q BV FV →
  (∀ S' → S' ∈ (proj₁ FV) →
    ((S' ∉ proj₁ (Dom θ₂)) ⊎ (S' ∈ proj₁ (Dom θo))) ⊎
    S' ∈ map (_+_ S) (SigMap.keys sigs)) →
  Canθ sigs S q (θ₁ ← θo) ≡ Canθ sigs S q ((θ₁ ← θ₂) ← θo)

can-new-irr θ₁ θ₂ θo nothin CBnothing S-prop = refl
can-new-irr θ₁ θ₂ θo pause CBpause S-prop = refl
can-new-irr θ₁ θ₂ θo (signl S q) (CBsig cbq) S-prop
  rewrite canθ-new-irr (Env.sig ([S]-env S)) 0 θ₁ θ₂ θo q cbq
            (λ S' S'∈FV →
              Data.Sum.map
                (S-prop S')
                (subst (S' ∈_) (sym (map-id (proj₁ (Dom ([S]-env S))))) ∘
                 (λ S'∈[S] →
                   subst (_∈ proj₁ (Dom ([S]-env S)))
                     (sym (∈:: S'∈[S]))
                     (Env.sig-∈-single S Signal.unknown)))
                (set-subtract-split {ys = Signal.unwrap S ∷ []} S'∈FV))
  = refl
can-new-irr θ₁ θ₂ θo (present S ∣⇒ p ∣⇒ q) (CBpresent {FVp = FVp} cbp cbq) S-prop
  with S-prop (Signal.unwrap S) (here refl)| Env.Sig∈ S (θ₁ ← θo) | Env.Sig∈ S ((θ₁ ← θ₂) ← θo)
... | inj₂ S∈Domθo | no  S∉domθ₁←θo | S∈domθ₁←θ₂←θo? =
  ⊥-elim (S∉domθ₁←θo (Env.sig-←-monoʳ S θo θ₁ S∈Domθo))
... | inj₂ S∈Domθo | yes S∈domθ₁←θo | no  S∉domθ₁←θ₂←θo =
  ⊥-elim (S∉domθ₁←θ₂←θo (Env.sig-←-monoʳ S θo (θ₁ ← θ₂) S∈Domθo))
... | inj₂ S∈Domθo | yes S∈domθ₁←θo | yes S∈domθ₁←θ₂←θo
  rewrite SigMap.∈-get-U-irr-m S (Env.sig θ₁) (Env.sig (θ₁ ← θ₂)) (Env.sig θo)
          S∈domθ₁←θo S∈domθ₁←θ₂←θo S∈Domθo
  with Env.sig-stats {S} ((θ₁ ← θ₂) ← θo) S∈domθ₁←θ₂←θo
... | Signal.present = can-new-irr θ₁ θ₂ θo p cbp
                         (λ S' S'∈FVp → S-prop S' (++ʳ (Signal.unwrap S ∷ []) (++ˡ S'∈FVp)))
... | Signal.absent  = can-new-irr θ₁ θ₂ θo q cbq
                         (λ S' S'∈FVq → S-prop S' (++ʳ (Signal.unwrap S ∷ proj₁ FVp) S'∈FVq))
... | Signal.unknown
  rewrite can-new-irr θ₁ θ₂ θo p cbp
            (λ S' S'∈FVp → S-prop S' (++ʳ (Signal.unwrap S ∷ []) (++ˡ S'∈FVp)))
        | can-new-irr θ₁ θ₂ θo q cbq
            (λ S' S'∈FVq → S-prop S' (++ʳ (Signal.unwrap S ∷ proj₁ FVp) S'∈FVq))
  = refl
can-new-irr θ₁ θ₂ θo (present S ∣⇒ p ∣⇒ q) (CBpresent {FVp = FVp} cbp cbq) S-prop
  | inj₁ S∉Domθ₂ | yes S∈domθ₁←θo | yes S∈domθ₁←θ₂←θo
  with Env.sig-←⁻ {θ₁} {θo} S S∈domθ₁←θo
... | inj₂ S∈Domθo
  rewrite SigMap.∈-get-U-irr-m S (Env.sig θ₁) (Env.sig (θ₁ ← θ₂)) (Env.sig θo)
          S∈domθ₁←θo S∈domθ₁←θ₂←θo S∈Domθo
  with Env.sig-stats {S} ((θ₁ ← θ₂) ← θo) S∈domθ₁←θ₂←θo
... | Signal.present = can-new-irr θ₁ θ₂ θo p cbp
                         (λ S' S'∈FVp → S-prop S' (++ʳ (Signal.unwrap S ∷ []) (++ˡ S'∈FVp)))
... | Signal.absent  = can-new-irr θ₁ θ₂ θo q cbq
                         (λ S' S'∈FVq → S-prop S' (++ʳ (Signal.unwrap S ∷ proj₁ FVp) S'∈FVq))
... | Signal.unknown
  rewrite can-new-irr θ₁ θ₂ θo p cbp
            (λ S' S'∈FVp → S-prop S' (++ʳ (Signal.unwrap S ∷ []) (++ˡ S'∈FVp)))
        | can-new-irr θ₁ θ₂ θo q cbq
            (λ S' S'∈FVq → S-prop S' (++ʳ (Signal.unwrap S ∷ proj₁ FVp) S'∈FVq))
  = refl
can-new-irr θ₁ θ₂ θo (present S ∣⇒ p ∣⇒ q) (CBpresent {FVp = FVp} cbp cbq) S-prop
  | inj₁ S∉Domθ₂ | yes S∈domθ₁←θo | yes S∈domθ₁←θ₂←θo
  | inj₁ S∈domθ₁ with Env.sig-←-irr-get {θ₁} {θ₂} {S} S∈domθ₁ S∉Domθ₂
... | a , b rewrite SigMap.get-U-both-irr-m S (Env.sig θ₁) (Env.sig (θ₁ ← θ₂)) (Env.sig θo) S∈domθ₁ a S∈domθ₁←θo S∈domθ₁←θ₂←θo b
  with Env.sig-stats {S} ((θ₁ ← θ₂) ← θo) S∈domθ₁←θ₂←θo
... | Signal.present = can-new-irr θ₁ θ₂ θo p cbp
                         (λ S' S'∈FVp → S-prop S' (++ʳ (Signal.unwrap S ∷ []) (++ˡ S'∈FVp)))
... | Signal.absent  = can-new-irr θ₁ θ₂ θo q cbq
                         (λ S' S'∈FVq → S-prop S' (++ʳ (Signal.unwrap S ∷ proj₁ FVp) S'∈FVq))
... | Signal.unknown
  rewrite can-new-irr θ₁ θ₂ θo p cbp
            (λ S' S'∈FVp → S-prop S' (++ʳ (Signal.unwrap S ∷ []) (++ˡ S'∈FVp)))
        | can-new-irr θ₁ θ₂ θo q cbq
            (λ S' S'∈FVq → S-prop S' (++ʳ (Signal.unwrap S ∷ proj₁ FVp) S'∈FVq))
  = refl
can-new-irr θ₁ θ₂ θo (present S ∣⇒ p ∣⇒ q) (CBpresent cbp cbq) S-prop
  | inj₁ S∉Domθ₂ | yes S∈domθ₁←θo | no  S∉domθ₁←θ₂←θo
  rewrite SigMap.keys-assoc-comm (Env.sig θ₁) (Env.sig θ₂) (Env.sig θo)
  = ⊥-elim (S∉domθ₁←θ₂←θo (SigMap.U-mono {m = Env.sig (θ₁ ← θo)} {k = S} S∈domθ₁←θo))
can-new-irr θ₁ θ₂ θo (present S ∣⇒ p ∣⇒ q) (CBpresent cbp cbq) S-prop
  | inj₁ S∉Domθ₂ | no  S∉domθ₁←θo | yes S∈domθ₁←θ₂←θo
  with Env.sig-←⁻ {θ₁ ← θo} {θ₂} S
                  (subst (Signal.unwrap S ∈_)
                    (SigMap.keys-assoc-comm (Env.sig θ₁) (Env.sig θ₂) (Env.sig θo))
                    S∈domθ₁←θ₂←θo)
... | (inj₁ S∈Domθ₁←θo) = ⊥-elim (S∉domθ₁←θo S∈Domθ₁←θo)
... | (inj₂ S∈Domθ₂) = ⊥-elim (S∉Domθ₂ S∈Domθ₂)
can-new-irr θ₁ θ₂ θo (present S ∣⇒ p ∣⇒ q) (CBpresent {FVp = FVp} cbp cbq) S-prop
  | inj₁ S∉Domθ₂ | no  S∉domθ₁←θo | no  S∉domθ₁←θ₂←θo
  rewrite can-new-irr θ₁ θ₂ θo p cbp
            (λ S' S'∈FVp → S-prop S' (++ʳ (Signal.unwrap S ∷ []) (++ˡ S'∈FVp)))
        | can-new-irr θ₁ θ₂ θo q cbq
            (λ S' S'∈FVq → S-prop S' (++ʳ (Signal.unwrap S ∷ proj₁ FVp) S'∈FVq))
  = refl
can-new-irr θ₁ θ₂ θo (emit S) CBemit S-prop = refl
can-new-irr θ₁ θ₂ θo (p ∥ q) (CBpar {FVp = FVp} cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) S-prop
  rewrite can-new-irr θ₁ θ₂ θo p cbp (λ S' S'∈FVp → S-prop S' (++ˡ S'∈FVp))
        | can-new-irr θ₁ θ₂ θo q cbq (λ S' S'∈FVq → S-prop S' (++ʳ (proj₁ FVp) S'∈FVq))
  = refl
can-new-irr θ₁ θ₂ θo (loop q) (CBloop cbq BV≠FV) S-prop =
  can-new-irr θ₁ θ₂ θo q cbq S-prop
can-new-irr θ₁ θ₂ θo (loopˢ p q) (CBloopˢ {BVp = BVp} {FVp = FVp} CBp CBq BVp≠FVq BVq≠FVq) S-prop
  rewrite can-new-irr θ₁ θ₂ θo p CBp (λ S' S'∈FVp → S-prop S' (++ˡ S'∈FVp))
        | can-new-irr θ₁ θ₂ θo q CBq (λ S' S'∈FVq → S-prop S' (++ʳ (proj₁ FVp) S'∈FVq))
 = refl
can-new-irr θ₁ θ₂ θo (p >> q) (CBseq {BVp = BVp} {FVp = FVp} cbp cbq BVp≠FVq) S-prop
  with can-new-irr θ₁ θ₂ θo p cbp (λ S' S'∈FVp → S-prop S' (++ˡ S'∈FVp))
... | can-p-θ₁←θo≡can-p-θ₁←θ₂←θo
  with any (Code._≟_ Code.nothin) (Canₖ p (θ₁ ← θo))
     | any (Code._≟_ Code.nothin) (Canₖ p ((θ₁ ← θ₂) ← θo))
... | yes nothin∈can-p-θ₁←θo | yes nothin∈can-p-θ₁←θ₂←θo
  rewrite can-p-θ₁←θo≡can-p-θ₁←θ₂←θo
        | can-new-irr θ₁ θ₂ θo q cbq (λ S' S'∈FVq → S-prop S' (++ʳ (proj₁ FVp) S'∈FVq))
  = refl
... | yes nothin∈can-p-θ₁←θo | no  nothin∉can-p-θ₁←θ₂←θo
  = ⊥-elim (nothin∉can-p-θ₁←θ₂←θo
            (subst (λ xs → Code.nothin ∈ proj₁ (proj₂ xs))
                   can-p-θ₁←θo≡can-p-θ₁←θ₂←θo
                   nothin∈can-p-θ₁←θo))
... | no  nothin∉can-p-θ₁←θo | yes nothin∈can-p-θ₁←θ₂←θo
  = ⊥-elim (nothin∉can-p-θ₁←θo
            (subst (λ xs → Code.nothin ∈ proj₁ (proj₂ xs))
                   (sym can-p-θ₁←θo≡can-p-θ₁←θ₂←θo)
                   nothin∈can-p-θ₁←θ₂←θo))
... | no  nothin∉can-p-θ₁←θo | no  nothin∉can-p-θ₁←θ₂←θo
  rewrite can-p-θ₁←θo≡can-p-θ₁←θ₂←θo = refl
can-new-irr θ₁ θ₂ θo (suspend q S) (CBsusp cbq [S]≠BVp) S-prop =
  can-new-irr θ₁ θ₂ θo q cbq (λ S' S'∈FV → S-prop S' (there S'∈FV))
can-new-irr θ₁ θ₂ θo (exit n) CBexit S-prop = refl
can-new-irr θ₁ θ₂ θo (trap q) (CBtrap cbq) S-prop
  rewrite can-new-irr θ₁ θ₂ θo q cbq S-prop
  = refl
can-new-irr θ₁ θ₂ θo (shared s ≔ e in: q) (CBshared {FV = FV} cbq) S-prop
  rewrite set-subtract-[] (proj₁ FV)
        | can-new-irr θ₁ θ₂ θo q cbq (λ S' S'∈FV → S-prop S' (++ʳ (proj₁ (FVₑ e)) S'∈FV))
  = refl
can-new-irr θ₁ θ₂ θo (s ⇐ e) CBsset S-prop = refl
can-new-irr θ₁ θ₂ θo (var x ≔ e in: q) (CBvar {FV = FV} cbq) S-prop
  rewrite set-subtract-[] (proj₁ FV)
  = can-new-irr θ₁ θ₂ θo q cbq (λ S' S'∈FV → S-prop S' (++ʳ (proj₁ (FVₑ e)) S'∈FV))
can-new-irr θ₁ θ₂ θo (x ≔ e) CBvset S-prop = refl
can-new-irr θ₁ θ₂ θo (if x ∣⇒ p ∣⇒ q) (CBif {FVp = FVp} cbp cbq) S-prop
  rewrite can-new-irr θ₁ θ₂ θo p cbp (λ S' S'∈FVp → S-prop S' (++ˡ S'∈FVp))
        | can-new-irr θ₁ θ₂ θo q cbq (λ S' S'∈FVq → S-prop S' (++ʳ (proj₁ FVp) S'∈FVq))
  = refl
can-new-irr θ₁ θ₂ θo (ρ⟨ θ , A ⟩· q) (CBρ {FV = FV} cbq) S-prop
  rewrite canθ-new-irr (Env.sig θ) 0 θ₁ θ₂ θo q cbq
            (λ S' S'∈FV →
              Data.Sum.map
                (S-prop S')
                (subst (S' ∈_) (sym (map-id (proj₁ (Dom θ)))))
                (set-subtract-split {ys = proj₁ (Dom θ)} S'∈FV))
  = refl

canθ-new-irr-S-prop-accumulate : ∀ {xs ys zs} S status θo →

  (∀ S' → S' ∈ xs →
    (S' ∉ ys ⊎ S' ∈ proj₁ (Dom θo)) ⊎
    S' ∈ (S + 0 ∷ map (_+_ S) (map suc zs))) →

  ∀ S' → S' ∈ xs →
    (S' ∉ ys ⊎ S' ∈ proj₁ (Dom (θo ← [ (S ₛ) ↦ status ]))) ⊎
    S' ∈ map (_+_ (suc S)) zs

canθ-new-irr-S-prop-accumulate {zs = zs} S status θo S-prop S' S'∈xs with S-prop S' S'∈xs
... | inj₁ (inj₁ S'∉ys) = inj₁ (inj₁ S'∉ys)
... | inj₁ (inj₂ S'∈Domθo) =
  inj₁ (inj₂ (Env.sig-←-monoˡ (S' ₛ) θo [ (S ₛ) ↦ status ]  S'∈Domθo))
... | inj₂ (here refl) rewrite +-comm S 0 =
  inj₁ (inj₂ (Env.sig-←-monoʳ (S ₛ) [ S ₛ ↦ status ] θo (Env.sig-∈-single (S ₛ) status)))
... | inj₂ (there S'∈map-+-S-suc-zs)
  rewrite map-+-compose-suc S zs
  = inj₂ S'∈map-+-S-suc-zs


canθ-new-irr {BV} {FV} [] S θ₁ θ₂ θo q cbq S-prop =
  can-new-irr θ₁ θ₂ θo q cbq S-prop'
  where
    S-prop' : ∀ S' → S' ∈ proj₁ FV → S' ∉ proj₁ (Dom θ₂) ⊎ S' ∈ proj₁ (Dom θo)
    S-prop' S' S'∈FV with S-prop S' S'∈FV
    ... | inj₁ S'∉Domθ₂⊎S'∈Domθo = S'∉Domθ₂⊎S'∈Domθo
    ... | inj₂ ()
canθ-new-irr (nothing ∷ sigs) S θ₁ θ₂ θo q cbq S-prop =
  canθ-new-irr sigs (suc S) θ₁ θ₂ θo q cbq
    (λ S' S'∈FV →
      Data.Sum.map id (subst (S' ∈_) (map-+-compose-suc S (SigMap.keys sigs)))
        (S-prop S' S'∈FV))
canθ-new-irr (just Signal.present ∷ sigs) S θ₁ θ₂ θo q cbq S-prop
  rewrite sym (Env.←-assoc θ₁ θo ([S]-env-present (S ₛ)))
        | sym (Env.←-assoc (θ₁ ← θ₂) θo ([S]-env-present (S ₛ)))
  = canθ-new-irr sigs (suc S) θ₁ θ₂ (θo ← [S]-env-present (S ₛ)) q cbq
      (canθ-new-irr-S-prop-accumulate S Signal.present θo S-prop)
canθ-new-irr (just Signal.absent ∷ sigs) S θ₁ θ₂ θo q cbq S-prop
  rewrite sym (Env.←-assoc θ₁ θo ([S]-env-absent (S ₛ)))
        | sym (Env.←-assoc (θ₁ ← θ₂) θo ([S]-env-absent (S ₛ)))
  = canθ-new-irr sigs (suc S) θ₁ θ₂ (θo ← [S]-env-absent (S ₛ)) q cbq
      (canθ-new-irr-S-prop-accumulate S Signal.absent θo S-prop)
canθ-new-irr (just Signal.unknown ∷ sigs) S θ₁ θ₂ θo q cbq S-prop
  with any (_≟_ S) (Canθₛ sigs (suc S) q ((θ₁ ← θo) ← [S]-env (S ₛ)))
     | any (_≟_ S) (Canθₛ sigs (suc S) q (((θ₁ ← θ₂) ← θo) ← [S]-env (S ₛ)))
... | yes S∈canθ-sigs-q-θ₁←θo←[S] | yes S∈canθ-sigs-q-θ₁←θ₂←θo←[S]
  rewrite sym (Env.←-assoc θ₁ θo ([S]-env (S ₛ)))
        | sym (Env.←-assoc (θ₁ ← θ₂) θo ([S]-env (S ₛ)))
  = canθ-new-irr sigs (suc S) θ₁ θ₂ (θo ← [S]-env (S ₛ)) q cbq
      (canθ-new-irr-S-prop-accumulate S Signal.unknown θo S-prop)
... | no  S∉canθ-sigs-q-θ₁←θo←[S] | no  S∉canθ-sigs-q-θ₁←θ₂←θo←[S]
  rewrite sym (Env.←-assoc θ₁ θo ([S]-env-absent (S ₛ)))
        | sym (Env.←-assoc (θ₁ ← θ₂) θo ([S]-env-absent (S ₛ)))
  = canθ-new-irr sigs (suc S) θ₁ θ₂ (θo ← [S]-env-absent (S ₛ)) q cbq
      (canθ-new-irr-S-prop-accumulate S Signal.absent θo S-prop)
... | yes S∈canθ-sigs-q-θ₁←θo←[S] | no  S∉canθ-sigs-q-θ₁←θ₂←θo←[S]
  rewrite sym (Env.←-assoc θ₁ θo ([S]-env (S ₛ)))
        | sym (Env.←-assoc (θ₁ ← θ₂) θo ([S]-env (S ₛ)))
        | canθ-new-irr sigs (suc S) θ₁ θ₂ (θo ← [S]-env (S ₛ)) q cbq
            (canθ-new-irr-S-prop-accumulate S Signal.unknown θo S-prop)
  = ⊥-elim
      (S∉canθ-sigs-q-θ₁←θ₂←θo←[S]
        S∈canθ-sigs-q-θ₁←θo←[S])
... | no  S∉canθ-sigs-q-θ₁←θo←[S] | yes S∈canθ-sigs-q-θ₁←θ₂←θo←[S]
  rewrite sym (Env.←-assoc θ₁ θo ([S]-env (S ₛ)))
        | sym (Env.←-assoc (θ₁ ← θ₂) θo ([S]-env (S ₛ)))
        | canθ-new-irr sigs (suc S) θ₁ θ₂ (θo ← [S]-env (S ₛ)) q cbq
            (canθ-new-irr-S-prop-accumulate S Signal.unknown θo S-prop)
  = ⊥-elim
      (S∉canθ-sigs-q-θ₁←θo←[S]
        S∈canθ-sigs-q-θ₁←θ₂←θo←[S])


can-irr : ∀ {BV} {FV} θ₁ θ₂ q →
  CorrectBinding q BV FV →
  (distinct' (proj₁ FV) (proj₁ (Dom θ₂))) →
  Can q θ₁ ≡ Can q (θ₁ ← θ₂)
can-irr θ₁ θ₂ q cbq FV≠Domθ₂
  with can-new-irr θ₁ θ₂ Env.[]env q cbq (λ S' S'∈FV → inj₁ (FV≠Domθ₂ S' S'∈FV))
... | eq rewrite cong (Can q) (Env.←-comm Env.[]env θ₁ distinct-empty-left)
               | cong (Can q) (Env.←-comm Env.[]env (θ₁ ← θ₂) distinct-empty-left)
         = eq
