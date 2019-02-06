{-
Setting an unknown signal can only shrink Can.

  canₖ-set-sig-monotonic : ∀ p S θ S∈ status →
    Env.sig-stats {S} θ S∈ ≡ Signal.unknown →
    ∀ k →
      k ∈ Canₖ p (Env.set-sig {S} θ S∈ status) →
      k ∈ Canₖ p θ

  (And its counterpart for Canₛ and Canₛₕ.)

There are also corresponding Canθ versions: Setting a signal that
is immediately shadowed by the inner environment does not change
the result; setting a signal not in the inner environment can only
shrink Canθ.

  canθ-set-sig-irr : ∀ sigs S'' →
    ∀ p S θ S∈ status →
      Signal.unwrap S ∈ map (_+_ S'') (SigMap.keys sigs) →
      Canθ sigs S'' p θ ≡ Canθ sigs S'' p (Env.set-sig {S} θ S∈ status)

  canθₖ-set-sig-monotonic : ∀ sigs S'' →
    ∀ p S θ S∈ status →
      Env.sig-stats {S} θ S∈ ≡ Signal.unknown →
      Signal.unwrap S ∉ map (_+_ S'') (SigMap.keys sigs) →
      ∀ k →
        k ∈ Canθₖ sigs S'' p (Env.set-sig {S} θ S∈ status) →
        k ∈ Canθₖ sigs S'' p θ

For convenient reasoning of Canθ, we have a wrapper around canθ?-set-sig-monotonic
lemmas: changing some unknowns to present or absent in the new signals (sigs) will
only make the result smaller.

  canθₖ-add-sig-monotonic : ∀ sigs S'' p θ S status →
    ∀ k →
      k ∈ Canθₖ sigs S'' p (θ ← Θ SigMap.[ S ↦ status ] VarMap.empty ShrMap.empty) →
      k ∈ Canθₖ sigs S'' p (θ ← [S]-env S)

A similar lemma for Canθ also holds, with some proper add-sig-monotonic constriant
on the continuation. Specifically, this holds for using Canθ as the continuation.

  canθ'ₛ-add-sig-monotonic : ∀ sigs S'' κ θ S status →
    (∀ θ S status S' →
      S' ∈ proj₁ (κ (θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty)) →
      S' ∈ proj₁ (κ (θ ← [S]-env S))) →
    ∀ S' →
      S' ∈ proj₁ (Canθ' sigs S'' κ (θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty)) →
      S' ∈ proj₁ (Canθ' sigs S'' κ (θ ← [S]-env S))


  canθ'ₛ-canθ-add-sig-monotonic : ∀ sigs S sigs' S' p θ S''' status →
    ∀ S'' →
      S'' ∈ proj₁ (Canθ' sigs S (Canθ sigs' S' p)
                    (θ ← Θ SigMap.[ S''' ↦ status ] ShrMap.empty VarMap.empty)) →
      S'' ∈ proj₁ (Canθ' sigs S (Canθ sigs' S' p)
                    (θ ← [S]-env S'''))
-}
module Esterel.Lang.CanFunction.SetSigMonotonic where

open import utility

open import Esterel.Lang
-- Note: the dependency is weird here; SetSigMonotonic should be basic
-- and cannot import Base. Instead, Base relies on SetSigMonotonic.
open import Esterel.Lang.CanFunction
open import Esterel.Context
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ) renaming (unwrap to _ˢ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ) renaming (unwrap to _ˢʰ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ) renaming (unwrap to _ᵛ)

open import Data.Bool
  using (Bool ; true ; false ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.List.Properties
  using (map-id ; map-compose ; map-cong)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using (++⁻)
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ)
open import Data.Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_)
open import Data.Nat.Properties.Simple
  using (+-comm)
open import Data.Maybe
  using (Maybe ; just ; nothing)
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
  using (_≡_ ; refl ; trans ; sym ; cong ; subst ; inspect ; [_] ; Reveal_·_is_
       ; module ≡-Reasoning)

open ListSet Data.Nat._≟_
  using (set-subtract ; set-subtract-[] ; set-subtract-merge ;  set-subtract-split ;
         set-remove ; set-remove-removed ; set-remove-mono-∈ ; set-remove-not-removed ;
         set-subtract-[a]≡set-remove)

open ≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM


canₖ-set-sig-monotonic : ∀ p S θ S∈ status →
  Env.sig-stats {S} θ S∈ ≡ Signal.unknown →
  ∀ k →
    k ∈ Canₖ p (Env.set-sig {S} θ S∈ status) →
    k ∈ Canₖ p θ

canₛ-set-sig-monotonic : ∀ p S θ S∈ status →
  Env.sig-stats {S} θ S∈ ≡ Signal.unknown →
  ∀ S'' →
    S'' ∈ Canₛ p (Env.set-sig {S} θ S∈ status) →
    S'' ∈ Canₛ p θ

canₛₕ-set-sig-monotonic : ∀ p S θ S∈ status →
  Env.sig-stats {S} θ S∈ ≡ Signal.unknown →
  ∀ s →
    s ∈ Canₛₕ p (Env.set-sig {S} θ S∈ status) →
    s ∈ Canₛₕ p θ

canθ-set-sig-irr : ∀ sigs S'' →
  ∀ p S θ S∈ status →
    Signal.unwrap S ∈ map (_+_ S'') (SigMap.keys sigs) →
    Canθ sigs S'' p θ ≡ Canθ sigs S'' p (Env.set-sig {S} θ S∈ status)

canθₖ-set-sig-monotonic : ∀ sigs S'' →
  ∀ p S θ S∈ status →
    Env.sig-stats {S} θ S∈ ≡ Signal.unknown →
    Signal.unwrap S ∉ map (_+_ S'') (SigMap.keys sigs) →
    ∀ k →
      k ∈ Canθₖ sigs S'' p (Env.set-sig {S} θ S∈ status) →
      k ∈ Canθₖ sigs S'' p θ

canθₛ-set-sig-monotonic : ∀ sigs S'' →
  ∀ p S θ S∈ status →
    Env.sig-stats {S} θ S∈ ≡ Signal.unknown →
    Signal.unwrap S ∉ map (_+_ S'') (SigMap.keys sigs) →
    ∀ S' →
      S' ∈ Canθₛ sigs S'' p (Env.set-sig {S} θ S∈ status) →
      S' ∈ Canθₛ sigs S'' p θ

canθₛₕ-set-sig-monotonic : ∀ sigs S'' →
  ∀ p S θ S∈ status →
    Env.sig-stats {S} θ S∈ ≡ Signal.unknown →
    Signal.unwrap S ∉ map (_+_ S'') (SigMap.keys sigs) →
    ∀ s →
      s ∈ Canθₛₕ sigs S'' p (Env.set-sig {S} θ S∈ status) →
      s ∈ Canθₛₕ sigs S'' p θ

canθₖ-add-sig-monotonic : ∀ sigs S'' p θ S status →
  ∀ k →
    k ∈ Canθₖ sigs S'' p (θ ← Θ SigMap.[ S ↦ status ] VarMap.empty ShrMap.empty) →
    k ∈ Canθₖ sigs S'' p (θ ← [S]-env S)

canθₛ-add-sig-monotonic : ∀ sigs S'' p θ S status →
  ∀ S' →
    S' ∈ Canθₛ sigs S'' p (θ ← Θ SigMap.[ S ↦ status ] VarMap.empty ShrMap.empty) →
    S' ∈ Canθₛ sigs S'' p (θ ← [S]-env S)

canθₛₕ-add-sig-monotonic : ∀ sigs S'' p θ S status →
  ∀ s →
    s ∈ Canθₛₕ sigs S'' p (θ ← Θ SigMap.[ S ↦ status ] VarMap.empty ShrMap.empty) →
    s ∈ Canθₛₕ sigs S'' p (θ ← [S]-env S)


canθₖ-add-sig-monotonic sigs S'' p θ S status k k∈canθ-p-θ←[S↦status]
  with any (_≟_ (Signal.unwrap S)) (map (_+_ S'') (SigMap.keys sigs))
... | yes S∈map-S''+-sigs =
  subst (k ∈_)
    (trans
      (cong (Canθₖ sigs S'' p)
        (begin
             θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty
         ≡⟨ cong (θ ←_) (sym (Env.sig-put-1map-overwrite' S Signal.unknown status S∈[S])) ⟩
             θ ← Env.set-sig {S} ([S]-env S) S∈[S] status
         ≡⟨ Env.sig-switch-right S status θ ([S]-env S) S∈[S] S∈Domθ←[S] ⟩
             Env.set-sig {S} (θ ← [S]-env S) S∈Domθ←[S] status
         ∎))
      (cong (proj₁ ∘ proj₂)
        (sym
          (canθ-set-sig-irr sigs S'' p S (θ ← [S]-env S) S∈Domθ←[S] status S∈map-S''+-sigs))))
     k∈canθ-p-θ←[S↦status]
  where S∈[S]         = Env.sig-∈-single S Signal.unknown
        S∈Domθ←[S]    = Env.sig-←-monoʳ S ([S]-env S) θ S∈[S]
... | no  S∉map-S''+-sigs =
  canθₖ-set-sig-monotonic sigs S'' p S (θ ← [S]-env S) S∈Domθ←[S] status
    (trans ⟨θ←[S]⟩S≡[S]S (Env.sig-stats-1map' S Signal.unknown S∈[S])) S∉map-S''+-sigs k
    (subst (k ∈_)
      (cong (Canθₖ sigs S'' p)
        (begin
             θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty
         ≡⟨ cong (θ ←_) (sym (Env.sig-put-1map-overwrite' S Signal.unknown status S∈[S])) ⟩
             θ ← Env.set-sig {S} ([S]-env S) S∈[S] status
         ≡⟨ Env.sig-switch-right S status θ ([S]-env S) S∈[S] S∈Domθ←[S] ⟩
             Env.set-sig {S} (θ ← [S]-env S) S∈Domθ←[S] status
         ∎))
       k∈canθ-p-θ←[S↦status])
  where S∈[S]         = Env.sig-∈-single S Signal.unknown
        S∈Domθ←[S]    = Env.sig-←-monoʳ S ([S]-env S) θ S∈[S]
        ⟨θ←[S]⟩S≡[S]S = Env.sig-stats-←-right-irr' S θ ([S]-env S) S∈[S] S∈Domθ←[S]


canθₛ-add-sig-monotonic sigs S'' p θ S status S' S'∈canθ-p-θ←[S↦status]
  with any (_≟_ (Signal.unwrap S)) (map (_+_ S'') (SigMap.keys sigs))
... | yes S∈map-S''+-sigs =
  subst (S' ∈_)
    (trans
      (cong (Canθₛ sigs S'' p)
        (begin
             θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty
         ≡⟨ cong (θ ←_) (sym (Env.sig-put-1map-overwrite' S Signal.unknown status S∈[S])) ⟩
             θ ← Env.set-sig {S} ([S]-env S) S∈[S] status
         ≡⟨ Env.sig-switch-right S status θ ([S]-env S) S∈[S] S∈Domθ←[S] ⟩
             Env.set-sig {S} (θ ← [S]-env S) S∈Domθ←[S] status
         ∎))
      (cong proj₁
        (sym
          (canθ-set-sig-irr sigs S'' p S (θ ← [S]-env S) S∈Domθ←[S] status S∈map-S''+-sigs))))
     S'∈canθ-p-θ←[S↦status]
  where S∈[S]         = Env.sig-∈-single S Signal.unknown
        S∈Domθ←[S]    = Env.sig-←-monoʳ S ([S]-env S) θ S∈[S]
... | no  S∉map-S''+-sigs =
  canθₛ-set-sig-monotonic sigs S'' p S (θ ← [S]-env S) S∈Domθ←[S] status
    (trans ⟨θ←[S]⟩S≡[S]S (Env.sig-stats-1map' S Signal.unknown S∈[S])) S∉map-S''+-sigs S'
    (subst (S' ∈_)
      (cong (Canθₛ sigs S'' p)
        (begin
             θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty
         ≡⟨ cong (θ ←_) (sym (Env.sig-put-1map-overwrite' S Signal.unknown status S∈[S])) ⟩
             θ ← Env.set-sig {S} ([S]-env S) S∈[S] status
         ≡⟨ Env.sig-switch-right S status θ ([S]-env S) S∈[S] S∈Domθ←[S] ⟩
             Env.set-sig {S} (θ ← [S]-env S) S∈Domθ←[S] status
         ∎))
       S'∈canθ-p-θ←[S↦status])
  where S∈[S]         = Env.sig-∈-single S Signal.unknown
        S∈Domθ←[S]    = Env.sig-←-monoʳ S ([S]-env S) θ S∈[S]
        ⟨θ←[S]⟩S≡[S]S = Env.sig-stats-←-right-irr' S θ ([S]-env S) S∈[S] S∈Domθ←[S]


canθₛₕ-add-sig-monotonic sigs S'' p θ S status s s∈canθ-p-θ←[S↦status]
  with any (_≟_ (Signal.unwrap S)) (map (_+_ S'') (SigMap.keys sigs))
... | yes S∈map-S''+-sigs =
  subst (s ∈_)
    (trans
      (cong (Canθₛₕ sigs S'' p)
        (begin
             θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty
         ≡⟨ cong (θ ←_) (sym (Env.sig-put-1map-overwrite' S Signal.unknown status S∈[S])) ⟩
             θ ← Env.set-sig {S} ([S]-env S) S∈[S] status
         ≡⟨ Env.sig-switch-right S status θ ([S]-env S) S∈[S] S∈Domθ←[S] ⟩
             Env.set-sig {S} (θ ← [S]-env S) S∈Domθ←[S] status
         ∎))
      (cong (proj₂ ∘ proj₂)
        (sym
          (canθ-set-sig-irr sigs S'' p S (θ ← [S]-env S) S∈Domθ←[S] status S∈map-S''+-sigs))))
     s∈canθ-p-θ←[S↦status]
  where S∈[S]         = Env.sig-∈-single S Signal.unknown
        S∈Domθ←[S]    = Env.sig-←-monoʳ S ([S]-env S) θ S∈[S]
... | no  S∉map-S''+-sigs =
  canθₛₕ-set-sig-monotonic sigs S'' p S (θ ← [S]-env S) S∈Domθ←[S] status
    (trans ⟨θ←[S]⟩S≡[S]S (Env.sig-stats-1map' S Signal.unknown S∈[S])) S∉map-S''+-sigs s
    (subst (s ∈_)
      (cong (Canθₛₕ sigs S'' p)
        (begin
             θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty
         ≡⟨ cong (θ ←_) (sym (Env.sig-put-1map-overwrite' S Signal.unknown status S∈[S])) ⟩
             θ ← Env.set-sig {S} ([S]-env S) S∈[S] status
         ≡⟨ Env.sig-switch-right S status θ ([S]-env S) S∈[S] S∈Domθ←[S] ⟩
             Env.set-sig {S} (θ ← [S]-env S) S∈Domθ←[S] status
         ∎))
       s∈canθ-p-θ←[S↦status])
  where S∈[S]         = Env.sig-∈-single S Signal.unknown
        S∈Domθ←[S]    = Env.sig-←-monoʳ S ([S]-env S) θ S∈[S]
        ⟨θ←[S]⟩S≡[S]S = Env.sig-stats-←-right-irr' S θ ([S]-env S) S∈[S] S∈Domθ←[S]


canₖ-set-sig-monotonic nothin S θ S∈ status θS≡unknown k k∈can-p-θ' = k∈can-p-θ'
canₖ-set-sig-monotonic pause S θ S∈ status θS≡unknown k k∈can-p-θ' = k∈can-p-θ'
canₖ-set-sig-monotonic (signl S' p) S θ S∈ status θS≡unknown k k∈can-p-θ'
  with Env.Sig∈ S ([S]-env S')
... | yes S∈Dom[S]-env
  rewrite sym (map-id (proj₁ (Dom ([S]-env S'))))
        | canθ-set-sig-irr (Env.sig ([S]-env S')) 0 p S θ S∈ status S∈Dom[S]-env
  = k∈can-p-θ'
... | no S∉Dom[S]-env
  rewrite sym (map-id (proj₁ (Dom ([S]-env S'))))
  = canθₖ-set-sig-monotonic
      (Env.sig ([S]-env S')) 0 p S θ S∈ status θS≡unknown
      S∉Dom[S]-env
      k k∈can-p-θ'
canₖ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown k k∈can-p-θ' with S' Signal.≟ S
canₖ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | no  S'≢S with Env.Sig∈ S' θ | Env.Sig∈ S' (Env.set-sig {S} θ S∈ status)
canₖ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | no  S'≢S | yes S'∈θ | no  S'∉θ' =
  ⊥-elim (S'∉θ' (Env.sig-set-mono' {S'} {S} {θ} {status} {S∈} S'∈θ))
canₖ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | no  S'≢S | no  S'∉θ | yes S'∈θ' with Env.sig-stats {S'} (Env.set-sig {S} θ S∈ status) S'∈θ'
... | Signal.present =
  ++ˡ (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ')
... | Signal.absent  =
  ++ʳ (Canₖ p θ) (canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown k k∈can-p-θ')
... | Signal.unknown
  with ++⁻ (Canₖ p (Env.set-sig {S} θ S∈ status)) k∈can-p-θ'
... | inj₁ k∈can-p'-θ' =
  ++ˡ (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p'-θ')
... | inj₂ k∈can-q'-θ' =
  ++ʳ (Canₖ p θ) (canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown k k∈can-q'-θ')
canₖ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | no  S'≢S | no  S'∉θ | no  S'∉θ'
  with ++⁻ (Canₖ p (Env.set-sig {S} θ S∈ status)) k∈can-p-θ'
... | inj₁ k∈can-p'-θ' =
  ++ˡ (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p'-θ')
... | inj₂ k∈can-q'-θ' =
  ++ʳ (Canₖ p θ) (canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown k k∈can-q'-θ')
canₖ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | no  S'≢S | yes S'∈θ | yes S'∈θ'
  with Env.sig-stats {S'} θ S'∈θ
     | Env.sig-putputget {S'} {S} {θ} {_} {status} S'≢S S'∈θ S∈ S'∈θ' refl
... | Signal.present | eq rewrite eq = canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ'
... | Signal.absent  | eq rewrite eq = canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown k k∈can-p-θ'
... | Signal.unknown | eq rewrite eq
  with ++⁻ (Canₖ p (Env.set-sig {S} θ S∈ status)) k∈can-p-θ'
... | inj₁ k∈can-p'-θ' =
  ++ˡ (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p'-θ')
... | inj₂ k∈can-q'-θ' =
  ++ʳ (Canₖ p θ) (canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown k k∈can-q'-θ')
canₖ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | yes refl with Env.Sig∈ S' θ | Env.Sig∈ S' (Env.set-sig {S} θ S∈ status)
... | no  S'∉θ  | S'∈θ'?    = ⊥-elim (S'∉θ S∈)
... | yes S'∈θ  | no  S'∉θ' = ⊥-elim (S'∉θ' (Env.sig-set-mono' {S'} {S} {θ} {status} {S∈} S'∈θ))
... | yes S'∈θ  | yes S'∈θ'
  rewrite Env.sig-stats-∈-irr {S'} {θ} S'∈θ S∈ | θS≡unknown
  with Env.sig-stats {S'} (Env.set-sig {S} θ S∈ status) S'∈θ'
... | Signal.present =
  ++ˡ (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ')
... | Signal.absent =
  ++ʳ (Canₖ p θ) (canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown k k∈can-p-θ')
... | Signal.unknown
  with ++⁻ (Canₖ p (Env.set-sig {S} θ S∈ status)) k∈can-p-θ'
... | inj₁ k∈can-p'-θ' =
  ++ˡ (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p'-θ')
... | inj₂ k∈can-q'-θ' =
  ++ʳ (Canₖ p θ) (canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown k k∈can-q'-θ')
canₖ-set-sig-monotonic (emit S') S θ S∈ status θS≡unknown k k∈can-p-θ' = k∈can-p-θ'
canₖ-set-sig-monotonic (p ∥ q) S θ S∈ status
  θS≡unknown k k∈can-p-θ' =
  map-mono² Code._⊔_
    (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown)
    (canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown)
    k k∈can-p-θ'
canₖ-set-sig-monotonic (loop p) S θ S∈ status θS≡unknown k k∈can-p-θ' =
  canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ'
canₖ-set-sig-monotonic (loopˢ p q) S θ S∈ status θS≡unknown k s∈can-loopˢpq-θ' =
  canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k s∈can-loopˢpq-θ'

canₖ-set-sig-monotonic (p >> q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  with any (Code._≟_ Code.nothin) (Canₖ p θ)
     | any (Code._≟_ Code.nothin) (Canₖ p (Env.set-sig {S} θ S∈ status))
canₖ-set-sig-monotonic (p >> q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | yes nothin∈can-p-θ | yes nothin∈can-p-θ'
  with Code.nothin Code.≟ k
     | ++⁻ (CodeSet.set-remove (Canₖ p (Env.set-sig {S} θ S∈ status)) Code.nothin) k∈can-p-θ'
... | nothin≟k    | inj₂ k∈can-q-θ' =
  ++ʳ (CodeSet.set-remove (Canₖ p θ) Code.nothin)
      (canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown k k∈can-q-θ')
... | yes refl    | inj₁ nothin∈can-p-θ'-[nothin] =
  ⊥-elim (CodeSet.set-remove-removed {Code.nothin} {Canₖ p (Env.set-sig {S} θ S∈ status)}
                                     nothin∈can-p-θ'-[nothin])
... | no nothin≢k | inj₁ k∈can-p-θ'-[nothin] =
  ++ˡ (CodeSet.set-remove-not-removed
        nothin≢k
        (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k
           (CodeSet.set-remove-mono-∈ Code.nothin k∈can-p-θ'-[nothin])))
canₖ-set-sig-monotonic (p >> q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | yes nothin∈can-p-θ | no  nothin∉can-p-θ'
  with Code.nothin Code.≟ k
... | yes refl    = ⊥-elim (nothin∉can-p-θ' k∈can-p-θ')
... | no nothin≢k =
  ++ˡ (CodeSet.set-remove-not-removed
        nothin≢k
        (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ'))
canₖ-set-sig-monotonic (p >> q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | no  nothin∉can-p-θ | yes nothin∈can-p-θ'
  = ⊥-elim (nothin∉can-p-θ (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown Code.nothin nothin∈can-p-θ'))
canₖ-set-sig-monotonic (p >> q) S θ S∈ status θS≡unknown k k∈can-p-θ'
  | no  nothin∉can-p-θ | no  nothin∉can-p-θ' =
  canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ'
canₖ-set-sig-monotonic (suspend p S') S θ S∈ status θS≡unknown k k∈can-p-θ' =
  canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ'
canₖ-set-sig-monotonic (trap p) S θ S∈ status θS≡unknown k k∈can-p-θ' =
  map-mono Code.↓* (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown) k k∈can-p-θ'
canₖ-set-sig-monotonic (exit n) S θ S∈ status θS≡unknown k k∈can-p-θ' = k∈can-p-θ'
canₖ-set-sig-monotonic (shared s ≔ e in: p) S θ S∈ status θS≡unknown k k∈can-p-θ' =
  canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ'
canₖ-set-sig-monotonic (s ⇐ e) S θ S∈ status θS≡unknown k k∈can-p-θ' = k∈can-p-θ'
canₖ-set-sig-monotonic (var x ≔ e in: p) S θ S∈ status θS≡unknown k k∈can-p-θ' =
  canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ'
canₖ-set-sig-monotonic (x ≔ e) S θ S∈ status θS≡unknown k k∈can-p-θ' = k∈can-p-θ'
canₖ-set-sig-monotonic (if x ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown k k∈can-if-θ'
  with ++⁻ (Canₖ p (Env.set-sig {S} θ S∈ status)) k∈can-if-θ'
... | inj₁ k∈can-p-θ' =
  ++ˡ (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈can-p-θ')
... | inj₂ k∈can-q-θ' =
  ++ʳ
   (Canₖ p θ)
   (canₖ-set-sig-monotonic q S θ S∈ status θS≡unknown k k∈can-q-θ')
canₖ-set-sig-monotonic (ρ θ' · p) S θ S∈ status θS≡unknown k k∈can-p-θ'
  with Env.Sig∈ S θ'
... | yes S∈Domθ'
  rewrite sym (map-id (proj₁ (Dom θ')))
        | canθ-set-sig-irr (Env.sig θ') 0 p S θ S∈ status S∈Domθ'
  = k∈can-p-θ'
... | no  S∉Domθ'
  rewrite sym (map-id (proj₁ (Dom θ')))
  = canθₖ-set-sig-monotonic (Env.sig θ') 0 p S θ S∈ status θS≡unknown S∉Domθ' k k∈can-p-θ'


canₛ-set-sig-monotonic nothin S θ S∈ status θS≡unknown S'' S''∈can-p-θ' = S''∈can-p-θ'
canₛ-set-sig-monotonic pause S θ S∈ status θS≡unknown S'' S''∈can-p-θ' = S''∈can-p-θ'
canₛ-set-sig-monotonic (signl S' p) S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
  with Env.Sig∈ S ([S]-env S')
... | yes S∈Dom[S]-env
  rewrite sym (map-id (proj₁ (Dom ([S]-env S'))))
        | canθ-set-sig-irr (Env.sig ([S]-env S')) 0 p S θ S∈ status S∈Dom[S]-env
  = S''∈can-p-θ'
... | no S∉Dom[S]-env rewrite sym (map-id (proj₁ (Dom ([S]-env S'))))
  with Signal.unwrap S' ≟ S''
... | yes refl =
  ⊥-elim
    (set-remove-removed {S''}
      {Canθₛ (Env.sig ([S]-env S')) 0 p (Env.set-sig {S} θ S∈ status)}
      S''∈can-p-θ')
... | no S'≢S'' =
  set-remove-not-removed S'≢S''
    (canθₛ-set-sig-monotonic
      (Env.sig ([S]-env S')) 0 p S θ S∈ status θS≡unknown
      S∉Dom[S]-env S''
      (set-remove-mono-∈ (Signal.unwrap S') S''∈can-p-θ'))
canₛ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
  with S' Signal.≟ S
canₛ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
  | no  S'≢S with Env.Sig∈ S' θ | Env.Sig∈ S' (Env.set-sig {S} θ S∈ status)
canₛ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
  | no  S'≢S | yes S'∈θ | no  S'∉θ' =
  ⊥-elim (S'∉θ' (Env.sig-set-mono' {S'} {S} {θ} {status} {S∈} S'∈θ))
canₛ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
  | no  S'≢S | no  S'∉θ | yes S'∈θ' with Env.sig-stats {S'} (Env.set-sig {S} θ S∈ status) S'∈θ'
... | Signal.present =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ')
... | Signal.absent  =
  ++ʳ (Canₛ p θ) (canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-p-θ')
... | Signal.unknown
  with ++⁻ (Canₛ p (Env.set-sig {S} θ S∈ status)) S''∈can-p-θ'
... | inj₁ S''∈can-p'-θ' =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p'-θ')
... | inj₂ S''∈can-q'-θ' =
  ++ʳ (Canₛ p θ) (canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-q'-θ')
canₛ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
  | no  S'≢S | no  S'∉θ | no  S'∉θ'
  with ++⁻ (Canₛ p (Env.set-sig {S} θ S∈ status)) S''∈can-p-θ'
... | inj₁ S''∈can-p'-θ' =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p'-θ')
... | inj₂ S''∈can-q'-θ' =
  ++ʳ (Canₛ p θ) (canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-q'-θ')
canₛ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
  | no  S'≢S | yes S'∈θ | yes S'∈θ'
  with Env.sig-stats {S'} θ S'∈θ
     | Env.sig-putputget {S'} {S} {θ} {_} {status} S'≢S S'∈θ S∈ S'∈θ' refl
... | Signal.present | eq rewrite eq = canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
... | Signal.absent  | eq rewrite eq = canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
... | Signal.unknown | eq rewrite eq
  with ++⁻ (Canₛ p (Env.set-sig {S} θ S∈ status)) S''∈can-p-θ'
... | inj₁ S''∈can-p'-θ' =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p'-θ')
... | inj₂ S''∈can-q'-θ' =
  ++ʳ (Canₛ p θ) (canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-q'-θ')
canₛ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
  | yes refl with Env.Sig∈ S' θ | Env.Sig∈ S' (Env.set-sig {S} θ S∈ status)
... | no  S'∉θ  | S'∈θ'?    = ⊥-elim (S'∉θ S∈)
... | yes S'∈θ  | no  S'∉θ' = ⊥-elim (S'∉θ' (Env.sig-set-mono' {S'} {S} {θ} {status} {S∈} S'∈θ))
... | yes S'∈θ  | yes S'∈θ'
  rewrite Env.sig-stats-∈-irr {S'} {θ} S'∈θ S∈ | θS≡unknown
  with Env.sig-stats {S'} (Env.set-sig {S} θ S∈ status) S'∈θ'
... | Signal.present =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ')
... | Signal.absent =
  ++ʳ (Canₛ p θ) (canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-p-θ')
... | Signal.unknown
  with ++⁻ (Canₛ p (Env.set-sig {S} θ S∈ status)) S''∈can-p-θ'
... | inj₁ S''∈can-p'-θ' =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p'-θ')
... | inj₂ S''∈can-q'-θ' =
  ++ʳ (Canₛ p θ) (canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-q'-θ')
canₛ-set-sig-monotonic (emit S') S θ S∈ status θS≡unknown S'' S''∈can-p-θ' = S''∈can-p-θ'
canₛ-set-sig-monotonic (p ∥ q) S θ S∈ status θS≡unknown S'' S''∈can-p∥q-θ'
  with ++⁻ (Canₛ p (Env.set-sig {S} θ S∈ status)) S''∈can-p∥q-θ'
... | inj₁ S''∈can-p-θ' =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ')
... | inj₂ S''∈can-q-θ' =
  ++ʳ (Canₛ p θ) (canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-q-θ')
canₛ-set-sig-monotonic (loop p) S θ S∈ status θS≡unknown S'' S''∈can-p-θ' =
  canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
canₛ-set-sig-monotonic (loopˢ p q) S θ S∈ status θS≡unknown S'' s∈can-loopˢpq-θ' =
  canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' s∈can-loopˢpq-θ'

canₛ-set-sig-monotonic (p >> q) S θ S∈ status θS≡unknown S'' S''∈can-p>>q-θ'
  with any (Code._≟_ Code.nothin) (Canₖ p θ)
     | any (Code._≟_ Code.nothin) (Canₖ p (Env.set-sig {S} θ S∈ status))
... | no  nothin∉can-p-θ | yes nothin∈can-p-θ' =
  ⊥-elim
    (nothin∉can-p-θ
      (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown
        Code.nothin nothin∈can-p-θ'))
... | no  nothin∉can-p-θ | no  nothin∉can-p-θ' =
  canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p>>q-θ'
... | yes nothin∈can-p-θ | no  nothin∉can-p-θ' =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p>>q-θ')
... | yes nothin∈can-p-θ | yes nothin∈can-p-θ'
  with ++⁻ (Canₛ p (Env.set-sig {S} θ S∈ status)) S''∈can-p>>q-θ'
... | inj₁ S''∈can-p-θ' =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ')
... | inj₂ S''∈can-q-θ' =
  ++ʳ (Canₛ p θ) (canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-q-θ')
canₛ-set-sig-monotonic (suspend p S') S θ S∈ status θS≡unknown S'' S''∈can-p-θ' =
  canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
canₛ-set-sig-monotonic (trap p) S θ S∈ status θS≡unknown S'' S''∈can-p-θ' =
  canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
canₛ-set-sig-monotonic (exit n) S θ S∈ status θS≡unknown S'' S''∈can-p-θ' = S''∈can-p-θ'
canₛ-set-sig-monotonic (shared s' ≔ e in: p) S θ S∈ status θS≡unknown S'' S''∈can-p-θ' =
  canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
canₛ-set-sig-monotonic (s' ⇐ e) S θ S∈ status θS≡unknown S'' S''∈can-p-θ' = S''∈can-p-θ'
canₛ-set-sig-monotonic (var x ≔ e in: p) S θ S∈ status θS≡unknown S'' S''∈can-p-θ' =
  canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ'
canₛ-set-sig-monotonic (x ≔ e) S θ S∈ status θS≡unknown S'' S''∈can-p-θ' = S''∈can-p-θ'
canₛ-set-sig-monotonic (if x ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown S'' S''∈can-if-θ'
  with ++⁻ (Canₛ p (Env.set-sig {S} θ S∈ status)) S''∈can-if-θ'
... | inj₁ S''∈can-p-θ' =
  ++ˡ (canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S'' S''∈can-p-θ')
... | inj₂ S''∈can-q-θ' =
  ++ʳ
   (Canₛ p θ)
   (canₛ-set-sig-monotonic q S θ S∈ status θS≡unknown S'' S''∈can-q-θ')
canₛ-set-sig-monotonic (ρ θ' · p) S θ S∈ status θS≡unknown S'' S''∈can-ρθ'p-θ'
  with Env.Sig∈ S θ'
... | yes S∈Domθ'
  rewrite sym (map-id (proj₁ (Dom θ')))
        | canθ-set-sig-irr (Env.sig θ') 0 p S θ S∈ status S∈Domθ'
  = S''∈can-ρθ'p-θ'
... | no  S∉Domθ'
  with set-subtract-merge {xs = Canθₛ (Env.sig θ') 0 p (Env.set-sig {S} θ S∈ status)}
                          {ys = proj₁ (Dom θ')}
                          S''∈can-ρθ'p-θ'
... | S''∈canθ-p-θ' , S''∉Domθ'
  rewrite sym (map-id (proj₁ (Dom θ')))
  with set-subtract-split
         (canθₛ-set-sig-monotonic (Env.sig θ') 0 p S θ S∈ status θS≡unknown S∉Domθ'
           S'' S''∈canθ-p-θ')
... | inj₂ S''∈Domθ' = ⊥-elim (S''∉Domθ' S''∈Domθ')
... | inj₁ S''∈canθ-p-θ-Domθ' = S''∈canθ-p-θ-Domθ'


canₛₕ-set-sig-monotonic nothin S θ S∈ status θS≡unknown s s∈can-p-θ' = s∈can-p-θ'
canₛₕ-set-sig-monotonic pause S θ S∈ status θS≡unknown s s∈can-p-θ' = s∈can-p-θ'
canₛₕ-set-sig-monotonic (signl S' p) S θ S∈ status θS≡unknown s s∈can-p-θ'
  with Env.Sig∈ S ([S]-env S')
... | yes S∈Dom[S]-env
  rewrite sym (map-id (proj₁ (Dom ([S]-env S'))))
        | canθ-set-sig-irr (Env.sig ([S]-env S')) 0 p S θ S∈ status S∈Dom[S]-env
  = s∈can-p-θ'
... | no S∉Dom[S]-env
  rewrite sym (map-id (proj₁ (Dom ([S]-env S'))))
  = canθₛₕ-set-sig-monotonic
      (Env.sig ([S]-env S')) 0 p S θ S∈ status θS≡unknown
      S∉Dom[S]-env
      s s∈can-p-θ'
canₛₕ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown s s∈can-p-θ'
  with S' Signal.≟ S
canₛₕ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown s s∈can-p-θ'
  | no  S'≢S with Env.Sig∈ S' θ | Env.Sig∈ S' (Env.set-sig {S} θ S∈ status)
canₛₕ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown s s∈can-p-θ'
  | no  S'≢S | yes S'∈θ | no  S'∉θ' =
  ⊥-elim (S'∉θ' (Env.sig-set-mono' {S'} {S} {θ} {status} {S∈} S'∈θ))
canₛₕ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown s s∈can-p-θ'
  | no  S'≢S | no  S'∉θ | yes S'∈θ' with Env.sig-stats {S'} (Env.set-sig {S} θ S∈ status) S'∈θ'
... | Signal.present =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ')
... | Signal.absent  =
  ++ʳ (Canₛₕ p θ) (canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-p-θ')
... | Signal.unknown
  with ++⁻ (Canₛₕ p (Env.set-sig {S} θ S∈ status)) s∈can-p-θ'
... | inj₁ s∈can-p'-θ' =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p'-θ')
... | inj₂ s∈can-q'-θ' =
  ++ʳ (Canₛₕ p θ) (canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-q'-θ')
canₛₕ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown s s∈can-p-θ'
  | no  S'≢S | no  S'∉θ | no  S'∉θ'
  with ++⁻ (Canₛₕ p (Env.set-sig {S} θ S∈ status)) s∈can-p-θ'
... | inj₁ s∈can-p'-θ' =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p'-θ')
... | inj₂ s∈can-q'-θ' =
  ++ʳ (Canₛₕ p θ) (canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-q'-θ')
canₛₕ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown s s∈can-p-θ'
  | no  S'≢S | yes S'∈θ | yes S'∈θ'
  with Env.sig-stats {S'} θ S'∈θ
     | Env.sig-putputget {S'} {S} {θ} {_} {status} S'≢S S'∈θ S∈ S'∈θ' refl
... | Signal.present | eq rewrite eq = canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ'
... | Signal.absent  | eq rewrite eq = canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-p-θ'
... | Signal.unknown | eq rewrite eq
  with ++⁻ (Canₛₕ p (Env.set-sig {S} θ S∈ status)) s∈can-p-θ'
... | inj₁ s∈can-p'-θ' =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p'-θ')
... | inj₂ s∈can-q'-θ' =
  ++ʳ (Canₛₕ p θ) (canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-q'-θ')
canₛₕ-set-sig-monotonic (present S' ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown s s∈can-p-θ'
  | yes refl with Env.Sig∈ S' θ | Env.Sig∈ S' (Env.set-sig {S} θ S∈ status)
... | no  S'∉θ  | S'∈θ'?    = ⊥-elim (S'∉θ S∈)
... | yes S'∈θ  | no  S'∉θ' = ⊥-elim (S'∉θ' (Env.sig-set-mono' {S'} {S} {θ} {status} {S∈} S'∈θ))
... | yes S'∈θ  | yes S'∈θ'
  rewrite Env.sig-stats-∈-irr {S'} {θ} S'∈θ S∈ | θS≡unknown
  with Env.sig-stats {S'} (Env.set-sig {S} θ S∈ status) S'∈θ'
... | Signal.present =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ')
... | Signal.absent =
  ++ʳ (Canₛₕ p θ) (canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-p-θ')
... | Signal.unknown
  with ++⁻ (Canₛₕ p (Env.set-sig {S} θ S∈ status)) s∈can-p-θ'
... | inj₁ s∈can-p'-θ' =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p'-θ')
... | inj₂ s∈can-q'-θ' =
  ++ʳ (Canₛₕ p θ) (canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-q'-θ')
canₛₕ-set-sig-monotonic (emit S') S θ S∈ status θS≡unknown s s∈can-p-θ' = s∈can-p-θ'
canₛₕ-set-sig-monotonic (p ∥ q) S θ S∈ status θS≡unknown s s∈can-p∥q-θ'
  with ++⁻ (Canₛₕ p (Env.set-sig {S} θ S∈ status)) s∈can-p∥q-θ'
... | inj₁ s∈can-p-θ' =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ')
... | inj₂ s∈can-q-θ' =
  ++ʳ (Canₛₕ p θ) (canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-q-θ')
canₛₕ-set-sig-monotonic (loop p) S θ S∈ status θS≡unknown s s∈can-p-θ' =
  canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ'
canₛₕ-set-sig-monotonic (loopˢ p q) S θ S∈ status θS≡unknown s s∈can-loopˢpq-θ' =
  canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-loopˢpq-θ'
canₛₕ-set-sig-monotonic (p >> q) S θ S∈ status θS≡unknown s s∈can-p>>q-θ'
  with any (Code._≟_ Code.nothin) (Canₖ p θ)
     | any (Code._≟_ Code.nothin) (Canₖ p (Env.set-sig {S} θ S∈ status))
... | no  nothin∉can-p-θ | yes nothin∈-can-p-θ' =
  ⊥-elim
    (nothin∉can-p-θ
      (canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown
        Code.nothin nothin∈-can-p-θ'))
... | no  nothin∉can-p-θ | no  nothin∉-can-p-θ' =
  canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p>>q-θ'
... | yes nothin∈can-p-θ | no  nothin∉-can-p-θ' =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p>>q-θ')
... | yes nothin∈can-p-θ | yes nothin∈-can-p-θ'
  with ++⁻ (Canₛₕ p (Env.set-sig {S} θ S∈ status)) s∈can-p>>q-θ'
... | inj₁ s∈can-p-θ' =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ')
... | inj₂ s∈can-q-θ' =
  ++ʳ (Canₛₕ p θ) (canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-q-θ')
canₛₕ-set-sig-monotonic (suspend p S') S θ S∈ status θS≡unknown s s∈can-p-θ' =
  canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ'
canₛₕ-set-sig-monotonic (trap p) S θ S∈ status θS≡unknown s s∈can-p-θ' =
  canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ'
canₛₕ-set-sig-monotonic (exit n) S θ S∈ status θS≡unknown s s∈can-p-θ' = s∈can-p-θ'
canₛₕ-set-sig-monotonic (shared s' ≔ e in: p) S θ S∈ status θS≡unknown s s∈can-p-θ'
  with SharedVar.unwrap s' Data.Nat.≟ s
... | yes refl =
  ⊥-elim (set-remove-removed {SharedVar.unwrap s'} {Canₛₕ p (Env.set-sig {S} θ S∈ status)}
            s∈can-p-θ')
... | no  s'≢s =
  set-remove-not-removed s'≢s
    (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s
      (set-remove-mono-∈ (SharedVar.unwrap s') s∈can-p-θ'))
canₛₕ-set-sig-monotonic (s' ⇐ e) S θ S∈ status θS≡unknown s s∈can-p-θ' = s∈can-p-θ'
canₛₕ-set-sig-monotonic (var x ≔ e in: p) S θ S∈ status θS≡unknown s s∈can-p-θ' =
  canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ'
canₛₕ-set-sig-monotonic (x ≔ e) S θ S∈ status θS≡unknown s s∈can-p-θ' = s∈can-p-θ'
canₛₕ-set-sig-monotonic (if x ∣⇒ p ∣⇒ q) S θ S∈ status θS≡unknown s s∈can-if-θ'
  with ++⁻ (Canₛₕ p (Env.set-sig {S} θ S∈ status)) s∈can-if-θ'
... | inj₁ s∈can-p-θ' =
  ++ˡ (canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈can-p-θ')
... | inj₂ s∈can-q-θ' =
  ++ʳ
   (Canₛₕ p θ)
   (canₛₕ-set-sig-monotonic q S θ S∈ status θS≡unknown s s∈can-q-θ')
canₛₕ-set-sig-monotonic (ρ θ' · p) S θ S∈ status θS≡unknown s s∈can-ρθ'p-θ'
  with Env.Sig∈ S θ'
... | yes S∈Domθ'
  rewrite sym (map-id (proj₁ (Dom θ')))
        | canθ-set-sig-irr (Env.sig θ') 0 p S θ S∈ status S∈Domθ'
  = s∈can-ρθ'p-θ'
... | no  S∉Domθ'
  with set-subtract-merge {xs = Canθₛₕ (Env.sig θ') 0 p (Env.set-sig {S} θ S∈ status)}
                          {ys = proj₁ (proj₂ (Dom θ'))}
                          s∈can-ρθ'p-θ'
... | s∈canθ-p-θ' , s∉Domθ'
  rewrite sym (map-id (proj₁ (Dom θ')))
  with set-subtract-split
         (canθₛₕ-set-sig-monotonic (Env.sig θ') 0 p S θ S∈ status θS≡unknown S∉Domθ'
           s s∈canθ-p-θ')
... | inj₂ s∈Domθ' = ⊥-elim (s∉Domθ' s∈Domθ')
... | inj₁ s∈canθ-p-θ-Domθ' = s∈canθ-p-θ-Domθ'


canθ-set-sig-irr [] S'' p S θ S∈Domθ status ()
canθ-set-sig-irr (nothing ∷ sigs) S'' p S θ S∈Domθ status S∈sigs
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθ-set-sig-irr sigs (suc S'') p S θ S∈Domθ status S∈sigs
canθ-set-sig-irr (just Signal.present ∷ sigs) S'' p S θ S∈Domθ status S∈S'∷sigs
  with (S'' ₛ) Signal.≟ S
... | yes refl
  rewrite Env.sig-set-←-← S status θ ([S]-env-present S)
            S∈Domθ (Env.sig-∈-single S Signal.present)
  = refl
... | no  S''≢S with S | S∈S'∷sigs
... | _      | here S≡S''+0 rewrite +-comm S'' 0 =
  ⊥-elim (S''≢S (Signal.unwrap-injective (sym S≡S''+0)))
... | zero ₛ | there S∈sigs
  rewrite map-+-swap-suc S'' (SigMap.keys sigs)
  = ⊥-elim (SigM.0∈S S∈sigs)
... | suc S' ₛ | there S∈sigs
  rewrite sym (Env.sig-switch (suc S' ₛ) status θ ([S]-env-present (S'' ₛ))
                S∈Domθ (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env-present (S'' ₛ)) S∈Domθ)
                (Env.sig-∉-single (suc S' ₛ) (S'' ₛ) Signal.present (S''≢S ∘ sym)))
        | map-+-compose-suc S'' (SigMap.keys sigs)
  = canθ-set-sig-irr sigs (suc S'') p (suc S' ₛ) (θ ← [S]-env-present (S'' ₛ))
      (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env-present (S'' ₛ)) S∈Domθ) status
      S∈sigs
canθ-set-sig-irr (just Signal.absent ∷ sigs) S'' p S θ S∈Domθ status S∈S'∷sigs
  with (S'' ₛ) Signal.≟ S
... | yes refl
  rewrite Env.sig-set-←-← S status θ ([S]-env-absent S)
            S∈Domθ (Env.sig-∈-single S Signal.absent)
  = refl
... | no  S''≢S with S | S∈S'∷sigs
... | _      | here S≡S''+0 rewrite +-comm S'' 0 =
  ⊥-elim (S''≢S (Signal.unwrap-injective (sym S≡S''+0)))
... | zero ₛ | there S∈sigs
  rewrite map-+-swap-suc S'' (SigMap.keys sigs)
  = ⊥-elim (SigM.0∈S S∈sigs)
... | suc S' ₛ | there S∈sigs
  rewrite sym (Env.sig-switch (suc S' ₛ) status θ ([S]-env-absent (S'' ₛ))
                S∈Domθ (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ)
                (Env.sig-∉-single (suc S' ₛ) (S'' ₛ) Signal.absent (S''≢S ∘ sym)))
        | map-+-compose-suc S'' (SigMap.keys sigs)
  = canθ-set-sig-irr sigs (suc S'') p (suc S' ₛ) (θ ← [S]-env-absent (S'' ₛ))
      (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ) status
      S∈sigs
canθ-set-sig-irr (just Signal.unknown ∷ sigs) S'' p S θ S∈Domθ status S∈S'∷sigs
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') p
         ((Env.set-sig {S} θ S∈Domθ status) ← [S]-env (S'' ₛ)))
canθ-set-sig-irr (just Signal.unknown ∷ sigs) S'' p S θ S∈Domθ status S∈S'∷sigs
  | yes S''∈canθ-p-θ←[S''] | yes S''∈canθ-p-θ'←[S'']
  with (S'' ₛ) Signal.≟ S
... | yes refl
  rewrite Env.sig-set-←-← S status θ ([S]-env S)
            S∈Domθ (Env.sig-∈-single S Signal.unknown)
  = refl
... | no  S''≢S with S | S∈S'∷sigs
... | _      | here S≡S''+0 rewrite +-comm S'' 0 =
  ⊥-elim (S''≢S (Signal.unwrap-injective (sym S≡S''+0)))
... | zero ₛ | there S∈sigs
  rewrite map-+-swap-suc S'' (SigMap.keys sigs)
  = ⊥-elim (SigM.0∈S S∈sigs)
... | suc S' ₛ | there S∈sigs
  rewrite sym (Env.sig-switch (suc S' ₛ) status θ ([S]-env (S'' ₛ))
                S∈Domθ (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ)
                (Env.sig-∉-single (suc S' ₛ) (S'' ₛ) Signal.unknown (S''≢S ∘ sym)))
        | map-+-compose-suc S'' (SigMap.keys sigs)
  = canθ-set-sig-irr sigs (suc S'') p (suc S' ₛ) (θ ← [S]-env (S'' ₛ))
      (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ) status
      S∈sigs
canθ-set-sig-irr (just Signal.unknown ∷ sigs) S'' p S θ S∈Domθ status S∈S'∷sigs
  | no  S''∉can-pθ-θ←[S''] | no  S''∉can-pθ-θ'←[S'']
  with (S'' ₛ) Signal.≟ S
... | yes refl
  rewrite Env.sig-set-←-← S status θ ([S]-env-absent S)
            S∈Domθ (Env.sig-∈-single S Signal.absent)
  = refl
... | no  S''≢S with S | S∈S'∷sigs
... | _      | here S≡S''+0 rewrite +-comm S'' 0 =
  ⊥-elim (S''≢S (Signal.unwrap-injective (sym S≡S''+0)))
... | zero ₛ | there S∈sigs
  rewrite map-+-swap-suc S'' (SigMap.keys sigs)
  = ⊥-elim (SigM.0∈S S∈sigs)
... | suc S' ₛ | there S∈sigs
  rewrite sym (Env.sig-switch (suc S' ₛ) status θ ([S]-env-absent (S'' ₛ))
                S∈Domθ (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ)
                (Env.sig-∉-single (suc S' ₛ) (S'' ₛ) Signal.absent (S''≢S ∘ sym)))
        | map-+-compose-suc S'' (SigMap.keys sigs)
  = canθ-set-sig-irr sigs (suc S'') p (suc S' ₛ) (θ ← [S]-env-absent (S'' ₛ))
      (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ) status
      S∈sigs
canθ-set-sig-irr (just Signal.unknown ∷ sigs) S'' p S θ S∈Domθ status S∈S'∷sigs
  | yes S''∈canθ-p-θ←[S''] | no  S''∉canθ-p-θ'←[S'']
  with (S'' ₛ) Signal.≟ S
... | yes refl
  rewrite Env.sig-set-←-← S status θ ([S]-env S)
            S∈Domθ (Env.sig-∈-single S Signal.unknown)
  = ⊥-elim (S''∉canθ-p-θ'←[S''] S''∈canθ-p-θ←[S''])
... | no  S''≢S with S | S∈S'∷sigs
... | _      | here S≡S''+0 rewrite +-comm S'' 0 =
  ⊥-elim (S''≢S (Signal.unwrap-injective (sym S≡S''+0)))
... | zero ₛ | there S∈sigs
  rewrite map-+-swap-suc S'' (SigMap.keys sigs)
  = ⊥-elim (SigM.0∈S S∈sigs)
... | suc S' ₛ | there S∈sigs
  rewrite sym (Env.sig-switch (suc S' ₛ) status θ ([S]-env (S'' ₛ))
                S∈Domθ (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ)
                (Env.sig-∉-single (suc S' ₛ) (S'' ₛ) Signal.unknown (S''≢S ∘ sym)))
        | map-+-compose-suc S'' (SigMap.keys sigs)
        | canθ-set-sig-irr sigs (suc S'') p (suc S' ₛ) (θ ← [S]-env (S'' ₛ))
           (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ) status
           S∈sigs
  = ⊥-elim (S''∉canθ-p-θ'←[S''] S''∈canθ-p-θ←[S''])
canθ-set-sig-irr (just Signal.unknown ∷ sigs) S'' p S θ S∈Domθ status S∈S'∷sigs
  | no  S''∉canθ-p-θ←[S''] | yes S''∈canθ-p-θ'←[S'']
  with (S'' ₛ) Signal.≟ S
... | yes refl
  rewrite Env.sig-set-←-← S status θ ([S]-env S)
            S∈Domθ (Env.sig-∈-single S Signal.unknown)
  = ⊥-elim (S''∉canθ-p-θ←[S''] S''∈canθ-p-θ'←[S''])
... | no  S''≢S with S | S∈S'∷sigs
... | _      | here S≡S''+0 rewrite +-comm S'' 0 =
  ⊥-elim (S''≢S (Signal.unwrap-injective (sym S≡S''+0)))
... | zero ₛ | there S∈sigs
  rewrite map-+-swap-suc S'' (SigMap.keys sigs)
  = ⊥-elim (SigM.0∈S S∈sigs)
... | suc S' ₛ | there S∈sigs
  rewrite sym (Env.sig-switch (suc S' ₛ) status θ ([S]-env (S'' ₛ))
                S∈Domθ (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ)
                (Env.sig-∉-single (suc S' ₛ) (S'' ₛ) Signal.unknown (S''≢S ∘ sym)))
        | map-+-compose-suc S'' (SigMap.keys sigs)
        | canθ-set-sig-irr sigs (suc S'') p (suc S' ₛ) (θ ← [S]-env (S'' ₛ))
           (Env.sig-←-monoˡ (suc S' ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ) status
           S∈sigs
  = ⊥-elim (S''∉canθ-p-θ←[S''] S''∈canθ-p-θ'←[S''])


canθₖ-set-sig-monotonic [] S'' p S θ S∈ status θS≡unknown S∉sigs k k∈canθ-p-θ' =
  canₖ-set-sig-monotonic p S θ S∈ status θS≡unknown k k∈canθ-p-θ'
canθₖ-set-sig-monotonic (nothing ∷ sigs) S'' p S θ S∈ status θS≡unknown S∉sigs k k∈canθ-p-θ'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₖ-set-sig-monotonic sigs (suc S'') p S θ S∈ status θS≡unknown S∉sigs
    k k∈canθ-p-θ'
canθₖ-set-sig-monotonic (just Signal.present ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs k k∈canθ-p-θ'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₖ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env-present (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) k
      (subst (k ∈_)
        (cong (Canθₖ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env-present (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env-present (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.present
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        k∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env-present (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env-present (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.present
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₖ-set-sig-monotonic (just Signal.absent ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs k k∈canθ-p-θ'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₖ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env-absent (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) k
      (subst (k ∈_)
        (cong (Canθₖ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env-absent (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.absent
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        k∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env-absent (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.absent
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₖ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status θS≡unknown S∉sigs k k∈canθ-p-θ'
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') p ((Env.set-sig {S} θ S∈ status) ← [S]-env (S'' ₛ)))
canθₖ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs k k∈canθ-p-θ'
  | yes S''∈canθ-p-θ←[S] | yes S''∈canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₖ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) k
      (subst (k ∈_)
        (cong (Canθₖ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        k∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₖ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs k k∈canθ-p-θ'
  | no  S''∉canθ-p-θ←[S] | no  S''∉canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₖ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env-absent (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) k
      (subst (k ∈_)
        (cong (Canθₖ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env-absent (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.absent
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        k∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env-absent (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.absent
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₖ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs k k∈canθ-p-θ'
  | no  S''∉canθ-p-θ←[S] | yes S''∈canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
        | cong (Canθₖ sigs (suc S'') p)
           (Env.sig-switch S status θ ([S]-env (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))
  = ⊥-elim
      (S''∉canθ-p-θ←[S]
        (canθₛ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) S''
      (subst (S'' ∈_)
        (cong (Canθₛ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        S''∈canθ-p-θ'←[S])))
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₖ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs k k∈canθ-p-θ'
  | yes S''∈canθ-p-θ←[S] | no  S''∉canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₖ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.absent
      k k∈canθ-p-θ←[S↦absent]
  where S''∈[S'']      = Env.sig-∈-single (S'' ₛ) Signal.unknown
        S∈Domθ←[S'']   = Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈
        S''∈Domθ←[S''] = Env.sig-←-monoʳ (S'' ₛ) ([S]-env (S'' ₛ)) θ S''∈[S'']
        θS≡⟨θ←[S'']⟩S  = Env.sig-←-∉-irr-stats' S θ ([S]-env-absent (S'' ₛ)) S∈
                           (Env.sig-∉-single S (S'' ₛ) Signal.absent
                             (S∉sigs ∘ here ∘ cong Signal.unwrap))
                           S∈Domθ←[S'']
        ⟨θ←[S'']⟩S''≡[S'']S'' = Env.sig-stats-←-right-irr' (S'' ₛ) θ ([S]-env (S'' ₛ))
                                  S''∈[S''] S''∈Domθ←[S'']
        k∈canθ-p-θ←[S↦absent] =
          canθₖ-set-sig-monotonic sigs (suc S'') p S
            (θ ← [S]-env-absent (S'' ₛ))
            S∈Domθ←[S''] status
            (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
            (S∉sigs ∘ there) k
            (subst (k ∈_)
              (cong (Canθₖ sigs (suc S'') p)
                (sym (Env.sig-switch S status θ ([S]-env-absent (S'' ₛ))
                        S∈ (Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈)
                        (Env.sig-∉-single S (S'' ₛ) Signal.absent
                          (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
              k∈canθ-p-θ')


canθₛ-set-sig-monotonic [] S'' p S θ S∈ status θS≡unknown S∉sigs S' S'∈canθ-p-θ' =
  canₛ-set-sig-monotonic p S θ S∈ status θS≡unknown S' S'∈canθ-p-θ'
canθₛ-set-sig-monotonic (nothing ∷ sigs) S'' p S θ S∈ status θS≡unknown S∉sigs S' S'∈canθ-p-θ'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛ-set-sig-monotonic sigs (suc S'') p S θ S∈ status θS≡unknown S∉sigs
    S' S'∈canθ-p-θ'
canθₛ-set-sig-monotonic (just Signal.present ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs S' S'∈canθ-p-θ'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env-present (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) S'
      (subst (S' ∈_)
        (cong (Canθₛ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env-present (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env-present (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.present
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        S'∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env-present (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env-present (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.present
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛ-set-sig-monotonic (just Signal.absent ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs S' S'∈canθ-p-θ'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env-absent (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) S'
      (subst (S' ∈_)
        (cong (Canθₛ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env-absent (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.absent
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        S'∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env-absent (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.absent
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status θS≡unknown S∉sigs S' S'∈canθ-p-θ'
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') p ((Env.set-sig {S} θ S∈ status) ← [S]-env (S'' ₛ)))
canθₛ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs S' S'∈canθ-p-θ'
  | yes S''∈canθ-p-θ←[S] | yes S''∈canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) S'
      (subst (S' ∈_)
        (cong (Canθₛ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        S'∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs S' S'∈canθ-p-θ'
  | no  S''∉canθ-p-θ←[S] | no  S''∉canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env-absent (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) S'
      (subst (S' ∈_)
        (cong (Canθₛ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env-absent (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.absent
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        S'∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env-absent (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.absent
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs S' S'∈canθ-p-θ'
  | no  S''∉canθ-p-θ←[S] | yes S''∈canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
        | cong (Canθₛ sigs (suc S'') p)
           (Env.sig-switch S status θ ([S]-env (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))
  = ⊥-elim
      (S''∉canθ-p-θ←[S]
        (canθₛ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) S''
      (subst (S'' ∈_)
        (cong (Canθₛ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        S''∈canθ-p-θ'←[S])))
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs S' S'∈canθ-p-θ'
  | yes S''∈canθ-p-θ←[S] | no  S''∉canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.absent
      S' S'∈canθ-p-θ←[S↦absent]
  where S''∈[S'']      = Env.sig-∈-single (S'' ₛ) Signal.unknown
        S∈Domθ←[S'']   = Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈
        S''∈Domθ←[S''] = Env.sig-←-monoʳ (S'' ₛ) ([S]-env (S'' ₛ)) θ S''∈[S'']
        θS≡⟨θ←[S'']⟩S  = Env.sig-←-∉-irr-stats' S θ ([S]-env-absent (S'' ₛ)) S∈
                           (Env.sig-∉-single S (S'' ₛ) Signal.absent
                             (S∉sigs ∘ here ∘ cong Signal.unwrap))
                           S∈Domθ←[S'']
        ⟨θ←[S'']⟩S''≡[S'']S'' = Env.sig-stats-←-right-irr' (S'' ₛ) θ ([S]-env (S'' ₛ))
                                  S''∈[S''] S''∈Domθ←[S'']
        S'∈canθ-p-θ←[S↦absent] =
          canθₛ-set-sig-monotonic sigs (suc S'') p S
            (θ ← [S]-env-absent (S'' ₛ))
            S∈Domθ←[S''] status
            (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
            (S∉sigs ∘ there) S'
            (subst (S' ∈_)
              (cong (Canθₛ sigs (suc S'') p)
                (sym (Env.sig-switch S status θ ([S]-env-absent (S'' ₛ))
                        S∈ (Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈)
                        (Env.sig-∉-single S (S'' ₛ) Signal.absent
                          (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
              S'∈canθ-p-θ')


canθₛₕ-set-sig-monotonic [] S'' p S θ S∈ status θS≡unknown S∉sigs s s∈canθ-p-θ' =
  canₛₕ-set-sig-monotonic p S θ S∈ status θS≡unknown s s∈canθ-p-θ'
canθₛₕ-set-sig-monotonic (nothing ∷ sigs) S'' p S θ S∈ status θS≡unknown S∉sigs s s∈canθ-p-θ'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛₕ-set-sig-monotonic sigs (suc S'') p S θ S∈ status θS≡unknown S∉sigs
    s s∈canθ-p-θ'
canθₛₕ-set-sig-monotonic (just Signal.present ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs s s∈canθ-p-θ'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛₕ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env-present (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) s
      (subst (s ∈_)
        (cong (Canθₛₕ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env-present (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env-present (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.present
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        s∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env-present (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env-present (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.present
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛₕ-set-sig-monotonic (just Signal.absent ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs s s∈canθ-p-θ'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛₕ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env-absent (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) s
      (subst (s ∈_)
        (cong (Canθₛₕ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env-absent (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.absent
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        s∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env-absent (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.absent
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛₕ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status θS≡unknown S∉sigs s s∈canθ-p-θ'
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') p ((Env.set-sig {S} θ S∈ status) ← [S]-env (S'' ₛ)))
canθₛₕ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs s s∈canθ-p-θ'
  | yes S''∈canθ-p-θ←[S] | yes S''∈canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛₕ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) s
      (subst (s ∈_)
        (cong (Canθₛₕ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        s∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛₕ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs s s∈canθ-p-θ'
  | no  S''∉canθ-p-θ←[S] | no  S''∉canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛₕ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env-absent (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) s
      (subst (s ∈_)
        (cong (Canθₛₕ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env-absent (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.absent
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        s∈canθ-p-θ')
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env-absent (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.absent
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛₕ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs s s∈canθ-p-θ'
  | no  S''∉canθ-p-θ←[S] | yes S''∈canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
        | cong (Canθₛₕ sigs (suc S'') p)
           (Env.sig-switch S status θ ([S]-env (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))
  = ⊥-elim
      (S''∉canθ-p-θ←[S]
        (canθₛ-set-sig-monotonic sigs (suc S'') p S
      (θ ← [S]-env (S'' ₛ))
      S∈Domθ←[S''] status
      (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
      (S∉sigs ∘ there) S''
      (subst (S'' ∈_)
        (cong (Canθₛ sigs (suc S'') p)
          (sym (Env.sig-switch S status θ ([S]-env (S'' ₛ))
                  S∈ (Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈)
                  (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                    (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
        S''∈canθ-p-θ'←[S])))
  where S∈Domθ←[S'']  = Env.sig-←-monoˡ S θ ([S]-env (S'' ₛ)) S∈
        θS≡⟨θ←[S'']⟩S = Env.sig-←-∉-irr-stats' S θ ([S]-env (S'' ₛ)) S∈
                          (Env.sig-∉-single S (S'' ₛ) Signal.unknown
                            (S∉sigs ∘ here ∘ cong Signal.unwrap))
                          S∈Domθ←[S'']
canθₛₕ-set-sig-monotonic (just Signal.unknown ∷ sigs) S'' p S θ S∈ status
  θS≡unknown S∉sigs s s∈canθ-p-θ'
  | yes S''∈canθ-p-θ←[S] | no  S''∉canθ-p-θ'←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = canθₛₕ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.absent
      s s∈canθ-p-θ←[S↦absent]
  where S''∈[S'']      = Env.sig-∈-single (S'' ₛ) Signal.unknown
        S∈Domθ←[S'']   = Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈
        S''∈Domθ←[S''] = Env.sig-←-monoʳ (S'' ₛ) ([S]-env (S'' ₛ)) θ S''∈[S'']
        θS≡⟨θ←[S'']⟩S  = Env.sig-←-∉-irr-stats' S θ ([S]-env-absent (S'' ₛ)) S∈
                           (Env.sig-∉-single S (S'' ₛ) Signal.absent
                             (S∉sigs ∘ here ∘ cong Signal.unwrap))
                           S∈Domθ←[S'']
        ⟨θ←[S'']⟩S''≡[S'']S'' = Env.sig-stats-←-right-irr' (S'' ₛ) θ ([S]-env (S'' ₛ))
                                  S''∈[S''] S''∈Domθ←[S'']
        s∈canθ-p-θ←[S↦absent] =
          canθₛₕ-set-sig-monotonic sigs (suc S'') p S
            (θ ← [S]-env-absent (S'' ₛ))
            S∈Domθ←[S''] status
            (trans (sym θS≡⟨θ←[S'']⟩S) θS≡unknown)
            (S∉sigs ∘ there) s
            (subst (s ∈_)
              (cong (Canθₛₕ sigs (suc S'') p)
                (sym (Env.sig-switch S status θ ([S]-env-absent (S'' ₛ))
                        S∈ (Env.sig-←-monoˡ S θ ([S]-env-absent (S'' ₛ)) S∈)
                        (Env.sig-∉-single S (S'' ₛ) Signal.absent
                          (S∉sigs ∘ here ∘ cong Signal.unwrap)))))
              s∈canθ-p-θ')

private -- re-defined and exported in Base; so we put it in private here
  [_↦_] : Signal → Signal.Status → Env
  [ S ↦ status ] = Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty


canθₛ-cong-←-add-sig-monotonic : ∀ sigs S'' p θ θ' S status →
  ∀ S' →
    S' ∈ Canθₛ sigs S'' p ((θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty) ← θ') →
    S' ∈ Canθₛ sigs S'' p ((θ ← [S]-env S) ← θ')
canθₛ-cong-←-add-sig-monotonic sigs S'' p θ θ' S status S' S'∈
  with Env.Sig∈ S θ'
... | yes S∈Domθ'
  rewrite sym (Env.←-assoc θ [ S ↦ status ] θ')
        | cong (θ ←_) (Env.←-single-overwrite-sig S status θ' S∈Domθ')
        | sym (Env.←-assoc θ ([S]-env S) θ')
        | cong (θ ←_) (Env.←-single-overwrite-sig S Signal.unknown θ' S∈Domθ')
  = S'∈
... | no  S∉Domθ'
  rewrite Env.←-assoc-comm θ ([S]-env S) θ'
            (Env.sig-single-notin-distinct S Signal.unknown θ' S∉Domθ')
  = canθₛ-add-sig-monotonic sigs S'' p (θ ← θ') S status S'
      (subst (S' ∈_)
        (cong (proj₁ ∘ Canθ sigs S'' p)
          (Env.←-assoc-comm θ [ S ↦ status ] θ'
            (Env.sig-single-notin-distinct S status θ' S∉Domθ')))
        S'∈)
