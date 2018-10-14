{-
The subset "goodness" of can w.r.t. other ρθ-reductions. For each of the 7 non-merge
ρθ-reductions, there are two corresponding Can subset lemmas.

The lemmas for shared variables and sequential variables are merged together,
using term-raise and term-nothing to capture the relevant esterel Terms
(see Base for their definitions):

  canₛ-raise : ∀ {E any/shr any/var r r' p} θ →
    term-raise any/shr any/var r' p →
    r ≐ E ⟦ r' ⟧e →
    ∀ S →
      Signal.unwrap S ∈ Canₛ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ →
      Signal.unwrap S ∈ Canₛ r θ

  canₛ-term-nothin : ∀ {r' E r} θ θ' →
    Env.sig θ ≡ Env.sig θ' →
    term-nothin r' →
    r ≐ E ⟦ r' ⟧e →
    ∀ S →
      Signal.unwrap S ∈ Canₛ (E ⟦ nothin ⟧e) θ' →
      Signal.unwrap S ∈ Canₛ r θ
-}
module Esterel.Lang.CanFunction.NonMergePotentialRules where

open import utility

open import Esterel.Lang
open import Esterel.Lang.CanFunction
open import Esterel.Lang.CanFunction.Base
open import Esterel.Lang.CanFunction.CanThetaContinuation
open import Esterel.Lang.CanFunction.SetSigMonotonic
open import Esterel.Lang.CanFunction.Plug
open import Esterel.Context
open import Esterel.Context.Properties
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
  using (++ˡ ; ++ʳ)
open import Data.Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_ ; _∸_ ; _<_ ; _≤_ ; _<′_ ; _≤′_)
open import Data.Nat.Properties.Simple
  using (+-comm ; +-assoc)
open import Data.Nat.Properties
--  using (n∸n≡0 ; +-∸-assoc ; m≢1+m+n ; z≤′n)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Product
  using (Σ ; Σ-syntax ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; id ; _∋_)
open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; subst ; inspect ; [_] ; Reveal_·_is_
       ; module ≡-Reasoning)

open ListSet Data.Nat._≟_
  using (set-subtract ; set-subtract-[] ; set-subtract-merge ;  set-subtract-split ;
         set-remove ; set-remove-removed ; set-remove-mono-∈ ; set-remove-not-removed ;
         set-subtract-[a]≡set-remove)

module LCode = ListSet Code._≟_


open _≤′_
open _≤_
open ≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

<⇒≢ : ∀ {m n} → m < n → m ≢ n
<⇒≢ (s≤s m<n) refl = <⇒≢ m<n refl


can-is-unknown-lemma : ∀ q θ S →
  ¬ (Env.isSig∈ S θ) →
  Can q θ ≡ Can q (θ ← [ S ↦ Signal.unknown ])


canθ'-is-unknown-lemma : ∀ sigs' S' q θ S →
  S ∉ proj₁ (Dom θ) →
  S ∉ map (_+_ S') (SigMap.keys sigs') →
  Canθ' sigs' S' (Can q) θ ≡
  Canθ' sigs' S' (Can q ∘ (_← [ (S ₛ) ↦ Signal.unknown ])) θ


canθ-is-unknown-lemma : ∀ sigs' S' q θ S →
  ¬ (Env.isSig∈ S θ) →
  Signal.unwrap S ∉ map (_+_ S') (SigMap.keys sigs') →
  Canθ sigs' S' q θ ≡ Canθ sigs' S' q (θ ← [ S ↦ Signal.unknown ])
canθ-is-unknown-lemma sigs' S' q θ S S∉Domθ S∉map-+-S'-sigs'
  rewrite unfold sigs' S' q θ
        | unfold sigs' S' q (θ ← [S]-env S)
        | canθ'-search-acc sigs' S' (Can q) θ (Signal.unwrap S) Signal.unknown
            S∉map-+-S'-sigs'
  = canθ'-is-unknown-lemma sigs' S' q θ (Signal.unwrap S) S∉Domθ S∉map-+-S'-sigs'


can-is-unknown-lemma nothin θ S S∉Domθ = refl
can-is-unknown-lemma pause θ S S∉Domθ = refl
can-is-unknown-lemma (signl S' q) θ S S∉Domθ
  with Env.Sig∈ S ([S]-env S')
... | yes S∈Domθ'
  rewrite canθ-shadowing-irr (Env.sig ([S]-env S')) 0
            q S Signal.unknown θ
            (subst (Signal.unwrap S ∈_)
              (sym (map-id (proj₁ (Dom ([S]-env S')))))
              S∈Domθ')
  = refl
... | no S∉Domθ'
  rewrite canθ-is-unknown-lemma (Env.sig ([S]-env S')) 0
            q θ S S∉Domθ
            (subst (Signal.unwrap S ∉_)
              (sym (map-id (proj₁ (Dom ([S]-env S')))))
              S∉Domθ')
  = refl
can-is-unknown-lemma (present S' ∣⇒ p ∣⇒ q) θ S S∉Domθ
  with S' Signal.≟ S
can-is-unknown-lemma (present S' ∣⇒ p ∣⇒ q) θ S S∉Domθ
  | yes refl with Env.Sig∈ S' θ | Env.Sig∈ S' (θ ← [ S ↦ Signal.unknown ])
... | no S'∉Domθ | yes S'∈Domθ←[S]
  rewrite Env.sig-stats-1map-right-← S Signal.unknown θ S'∈Domθ←[S]
        | can-is-unknown-lemma p θ S S∉Domθ
        | can-is-unknown-lemma q θ S S∉Domθ
  = refl
... | S'∈?Domθ | no S'∉Domθ←[S] =
  ⊥-elim (S'∉Domθ←[S] (Env.sig-∈-single-right-← S Signal.unknown θ))
... | yes S'∈Domθ | S'∈?Domθ←[S] = ⊥-elim (S∉Domθ S'∈Domθ)
can-is-unknown-lemma (present S' ∣⇒ p ∣⇒ q) θ S S∉Domθ
  | no S'≠S with Env.Sig∈ S' θ | Env.Sig∈ S' (θ ← [ S ↦ Signal.unknown ])
... | no S'∉Domθ | yes S'∈Domθ←[S]
  = ⊥-elim
      (Data.Sum.[ S'∉Domθ , Env.sig-∉-single S' S Signal.unknown S'≠S ]
        (Env.sig-←⁻ {θ} {[ S ↦ Signal.unknown ]} S' S'∈Domθ←[S]))
... | yes S'∈Domθ | no S'∉Domθ←[S]
  = ⊥-elim (S'∉Domθ←[S] (Env.sig-←-monoˡ S' θ [ S ↦ Signal.unknown ] S'∈Domθ))
... | no S'∉Domθ | no S'∉Domθ←[S]
  rewrite can-is-unknown-lemma p θ S S∉Domθ
        | can-is-unknown-lemma q θ S S∉Domθ
  = refl
... | yes S'∈Domθ | yes S'∈Domθ←[S]
  rewrite sym (Env.sig-←-∉-irr-stats' S' θ [ S ↦ Signal.unknown ]
                S'∈Domθ (Env.sig-∉-single S' S Signal.unknown S'≠S) S'∈Domθ←[S])
  with Env.sig-stats {S'} θ S'∈Domθ
... | Signal.present
  rewrite can-is-unknown-lemma p θ S S∉Domθ
  = refl
... | Signal.absent
  rewrite can-is-unknown-lemma q θ S S∉Domθ
  = refl
... | Signal.unknown
  rewrite can-is-unknown-lemma p θ S S∉Domθ
        | can-is-unknown-lemma q θ S S∉Domθ
  = refl
can-is-unknown-lemma (emit S') θ S S∉Domθ = refl
can-is-unknown-lemma (p ∥ q) θ S S∉Domθ
  rewrite can-is-unknown-lemma p θ S S∉Domθ
        | can-is-unknown-lemma q θ S S∉Domθ
  = refl
can-is-unknown-lemma (loop q) θ S S∉Domθ =
  can-is-unknown-lemma q θ S S∉Domθ
can-is-unknown-lemma (loopˢ p q) θ S S∉Domθ =
  can-is-unknown-lemma p θ S S∉Domθ
can-is-unknown-lemma (p >> q) θ S S∉Domθ
  with any (Code._≟_ Code.nothin) (Canₖ p θ)
     | any (Code._≟_ Code.nothin) (Canₖ p (θ ← [ S ↦ Signal.unknown ]))
... | yes nothin∈can-p-θ | yes nothin∈can-p-θ←[S]
  rewrite can-is-unknown-lemma p θ S S∉Domθ
        | can-is-unknown-lemma q θ S S∉Domθ
  = refl
... | no  nothin∉can-p-θ | no  nothin∉can-p-θ←[S]
  rewrite can-is-unknown-lemma p θ S S∉Domθ
  = refl
... | yes nothin∈can-p-θ | no  nothin∉can-p-θ←[S]
  rewrite can-is-unknown-lemma p θ S S∉Domθ
  = ⊥-elim (nothin∉can-p-θ←[S] nothin∈can-p-θ)
... | no  nothin∉can-p-θ | yes nothin∈can-p-θ←[S]
  rewrite can-is-unknown-lemma p θ S S∉Domθ
  = ⊥-elim (nothin∉can-p-θ nothin∈can-p-θ←[S])
can-is-unknown-lemma (suspend q S') θ S S∉Domθ =
  can-is-unknown-lemma q θ S S∉Domθ
can-is-unknown-lemma (trap q) θ S S∉Domθ
  rewrite can-is-unknown-lemma q θ S S∉Domθ
  = refl
can-is-unknown-lemma (exit n) θ S S∉Domθ = refl
can-is-unknown-lemma (shared s ≔ e in: q) θ S S∉Domθ
  rewrite can-is-unknown-lemma q θ S S∉Domθ
  = refl
can-is-unknown-lemma (s ⇐ e) θ S S∉Domθ = refl
can-is-unknown-lemma (var x ≔ e in: q) θ S S∉Domθ
  rewrite can-is-unknown-lemma q θ S S∉Domθ
  = refl
can-is-unknown-lemma (x ≔ e) θ S S∉Domθ = refl
can-is-unknown-lemma (if x ∣⇒ p ∣⇒ q) θ S S∉Domθ
  rewrite can-is-unknown-lemma p θ S S∉Domθ
        | can-is-unknown-lemma q θ S S∉Domθ
  = refl
can-is-unknown-lemma (ρ θ' · q) θ S S∉Domθ
  with Env.Sig∈ S θ'
... | yes S∈Domθ'
  rewrite canθ-shadowing-irr (Env.sig θ') 0 q S Signal.unknown θ
            (subst (Signal.unwrap S ∈_)
              (sym (map-id (proj₁ (Dom θ'))))
              S∈Domθ')
  = refl
... | no S∉Domθ'
  rewrite canθ-is-unknown-lemma (Env.sig θ') 0 q θ S S∉Domθ
            (subst (Signal.unwrap S ∉_)
              (sym (map-id (proj₁ (Dom θ'))))
              S∉Domθ')
  = refl


canθ'-is-unknown-lemma [] S' q θ S S∉Domθ S∉map-+-S'-sigs' =
  can-is-unknown-lemma q θ (S ₛ) S∉Domθ
canθ'-is-unknown-lemma (nothing ∷ sigs') S' q θ S S∉Domθ S∉map-+-S'-sigs'
  rewrite map-+-compose-suc S' (SigMap.keys sigs')
  = canθ'-is-unknown-lemma sigs' (suc S') q θ S S∉Domθ S∉map-+-S'-sigs'
canθ'-is-unknown-lemma (just Signal.present ∷ sigs') S' q θ S S∉Domθ S∉map-+-S'-sigs'
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
  = canθ'-is-unknown-lemma sigs' (suc S') q (θ ← [S]-env-present (S' ₛ))
      S (Env.sig-↚⁻ {θ} {[S]-env-present (S' ₛ)} (S ₛ)
          S∉Domθ
          (Env.sig-∉-single (S ₛ) (S' ₛ) Signal.present
            (S∉map-+-S'-sigs' ∘ here ∘ cong Signal.unwrap)))
      (S∉map-+-S'-sigs' ∘ there)
canθ'-is-unknown-lemma (just Signal.absent ∷ sigs') S' q θ S S∉Domθ S∉map-+-S'-sigs'
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
  = canθ'-is-unknown-lemma sigs' (suc S') q (θ ← [S]-env-absent (S' ₛ))
      S (Env.sig-↚⁻ {θ} {[S]-env-absent (S' ₛ)} (S ₛ)
          S∉Domθ
          (Env.sig-∉-single (S ₛ) (S' ₛ) Signal.absent
            (S∉map-+-S'-sigs' ∘ here ∘ cong Signal.unwrap)))
      (S∉map-+-S'-sigs' ∘ there)
canθ'-is-unknown-lemma (just Signal.unknown ∷ sigs') S' q θ S S∉Domθ S∉map-+-S'-sigs'
  with any (_≟_ S') (proj₁ (Canθ' sigs' (suc S') (Can q)
                             (θ ← [S]-env (S' ₛ))))
     | any (_≟_ S') (proj₁ (Canθ' sigs' (suc S') (Can q ∘ (_← [ (S ₛ) ↦ Signal.unknown ]))
                             (θ ← [S]-env (S' ₛ))))
... | yes S∈canθ'-sigs'-can-q-θ←[S'] | yes S∈canθ'-sigs'-can-q←[S]-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
  = canθ'-is-unknown-lemma sigs' (suc S') q (θ ← [S]-env (S' ₛ))
      S (Env.sig-↚⁻ {θ} {[S]-env (S' ₛ)} (S ₛ)
          S∉Domθ
          (Env.sig-∉-single (S ₛ) (S' ₛ) Signal.unknown
            (S∉map-+-S'-sigs' ∘ here ∘ cong Signal.unwrap)))
      (S∉map-+-S'-sigs' ∘ there)
... | no  S∉canθ'-sigs'-can-q-θ←[S'] | no  S∉canθ'-sigs'-can-q←[S]-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
  = canθ'-is-unknown-lemma sigs' (suc S') q (θ ← [S]-env-absent (S' ₛ))
      S (Env.sig-↚⁻ {θ} {[S]-env-absent (S' ₛ)} (S ₛ)
          S∉Domθ
          (Env.sig-∉-single (S ₛ) (S' ₛ) Signal.absent
            (S∉map-+-S'-sigs' ∘ here ∘ cong Signal.unwrap)))
      (S∉map-+-S'-sigs' ∘ there)
... | yes S∈canθ'-sigs'-can-q-θ←[S'] | no  S∉canθ'-sigs'-can-q←[S]-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | canθ'-is-unknown-lemma sigs' (suc S') q (θ ← [S]-env (S' ₛ))
            S (Env.sig-↚⁻ {θ} {[S]-env (S' ₛ)} (S ₛ)
                S∉Domθ
                (Env.sig-∉-single (S ₛ) (S' ₛ) Signal.unknown
                  (S∉map-+-S'-sigs' ∘ here ∘ cong Signal.unwrap)))
            (S∉map-+-S'-sigs' ∘ there)
  = ⊥-elim (S∉canθ'-sigs'-can-q←[S]-θ←[S'] S∈canθ'-sigs'-can-q-θ←[S'])
... | no  S∉canθ'-sigs'-can-q-θ←[S'] | yes S∈canθ'-sigs'-can-q←[S]-θ←[S']
  rewrite +-comm S' 0
        | map-+-compose-suc S' (SigMap.keys sigs')
        | canθ'-is-unknown-lemma sigs' (suc S') q (θ ← [S]-env (S' ₛ))
            S (Env.sig-↚⁻ {θ} {[S]-env (S' ₛ)} (S ₛ)
                S∉Domθ
                (Env.sig-∉-single (S ₛ) (S' ₛ) Signal.unknown
                  (S∉map-+-S'-sigs' ∘ here ∘ cong Signal.unwrap)))
            (S∉map-+-S'-sigs' ∘ there)
  = ⊥-elim (S∉canθ'-sigs'-can-q-θ←[S'] S∈canθ'-sigs'-can-q←[S]-θ←[S'])


can-is-present-lemma : ∀ p q S θ S∈ E →
  Env.sig-stats {S} θ S∈ ≡ Signal.present →
    Can (E ⟦ present S ∣⇒ p ∣⇒ q ⟧e) θ ≡
    Can (E ⟦ p ⟧e) θ
can-is-present-lemma p q S θ S∈ [] θS≡present with Env.Sig∈ S θ
... | no  S∉  = ⊥-elim (S∉ S∈)
... | yes S∈' rewrite Env.sig-stats-∈-irr {S} {θ} S∈ S∈'
  with Signal.present Signal.≟ₛₜ Env.sig-stats {S} θ S∈'
... | no  θS≢present  = ⊥-elim (θS≢present (sym θS≡present))
... | yes θS≡present' = refl
can-is-present-lemma p q S θ S∈ (epar₁ _ ∷ E) θS≡present
  rewrite can-is-present-lemma p q S θ S∈ E θS≡present
  = refl
can-is-present-lemma p q S θ S∈ (epar₂ _ ∷ E) θS≡present
  rewrite can-is-present-lemma p q S θ S∈ E θS≡present
  = refl
can-is-present-lemma p q S θ S∈ (eloopˢ _ ∷ E) θS≡present = can-is-present-lemma p q S θ S∈ E θS≡present
can-is-present-lemma p q S θ S∈ (eseq _ ∷ E) θS≡present
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ present S ∣⇒ p ∣⇒ q ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ p ⟧e) θ)
     | can-is-present-lemma p q S θ S∈ E θS≡present
... | yes nothin∈can-E⟦present⟧ | yes nothin∈can-E⟦p⟧ | eq rewrite eq = refl
... | yes nothin∈can-E⟦present⟧ | no  nothin∉can-E⟦p⟧ | eq rewrite eq
  = ⊥-elim (nothin∉can-E⟦p⟧ nothin∈can-E⟦present⟧)
... | no  nothin∉can-E⟦present⟧ | yes nothin∈can-E⟦p⟧ | eq rewrite eq
  = ⊥-elim (nothin∉can-E⟦present⟧ nothin∈can-E⟦p⟧)
... | no  nothin∉can-E⟦present⟧ | no  nothin∉can-E⟦p⟧ | eq rewrite eq = refl
can-is-present-lemma p q S θ S∈ (esuspend S' ∷ E) θS≡present
  rewrite can-is-present-lemma p q S θ S∈ E θS≡present
  = refl
can-is-present-lemma p q S θ S∈ (etrap ∷ E) θS≡present
  rewrite can-is-present-lemma p q S θ S∈ E θS≡present
  = refl



can-is-absent-lemma : ∀ p q S θ S∈ E →
  Env.sig-stats {S} θ S∈ ≡ Signal.absent →
    Can (E ⟦ present S ∣⇒ p ∣⇒ q ⟧e) θ ≡
    Can (E ⟦ q ⟧e) θ
can-is-absent-lemma p q S θ S∈ [] θS≡absent with Env.Sig∈ S θ
... | no  S∉  = ⊥-elim (S∉ S∈)
... | yes S∈' rewrite Env.sig-stats-∈-irr {S} {θ} S∈ S∈'
  with Signal.present Signal.≟ₛₜ Env.sig-stats {S} θ S∈'
... | yes present≡θS = ((Signal.present ≡ Signal.absent → _) ∋ λ ())
                       (trans present≡θS θS≡absent)
... | no  present≢θS
  with Signal.absent Signal.≟ₛₜ Env.sig-stats {S} θ S∈'
... | no  absent≢θS = ⊥-elim (absent≢θS (sym θS≡absent))
... | yes absent≡θS = refl
can-is-absent-lemma p q S θ S∈ (epar₁ _ ∷ E) θS≡absent
  rewrite can-is-absent-lemma p q S θ S∈ E θS≡absent
  = refl
can-is-absent-lemma p q S θ S∈ (epar₂ _ ∷ E) θS≡absent
  rewrite can-is-absent-lemma p q S θ S∈ E θS≡absent
  = refl
can-is-absent-lemma p q S θ S∈ (eloopˢ _ ∷ E) θS≡absent = can-is-absent-lemma p q S θ S∈ E θS≡absent
can-is-absent-lemma p q S θ S∈ (eseq _ ∷ E) θS≡absent
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ present S ∣⇒ p ∣⇒ q ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ q ⟧e) θ)
     | can-is-absent-lemma p q S θ S∈ E θS≡absent
... | yes nothin∈can-E⟦present⟧ | yes nothin∈can-E⟦p⟧ | eq rewrite eq = refl
... | yes nothin∈can-E⟦present⟧ | no  nothin∉can-E⟦p⟧ | eq rewrite eq
  = ⊥-elim (nothin∉can-E⟦p⟧ nothin∈can-E⟦present⟧)
... | no  nothin∉can-E⟦present⟧ | yes nothin∈can-E⟦p⟧ | eq rewrite eq
  = ⊥-elim (nothin∉can-E⟦present⟧ nothin∈can-E⟦p⟧)
... | no  nothin∉can-E⟦present⟧ | no  nothin∉can-E⟦p⟧ | eq rewrite eq = refl
can-is-absent-lemma p q S θ S∈ (esuspend S' ∷ E) θS≡absent
  rewrite can-is-absent-lemma p q S θ S∈ E θS≡absent
  = refl
can-is-absent-lemma p q S θ S∈ (etrap ∷ E) θS≡absent
  rewrite can-is-absent-lemma p q S θ S∈ E θS≡absent
  = refl



can-is-present : ∀ {r p q S E} θ S∈ →
  r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e →
  Env.sig-stats {S} θ S∈ ≡ Signal.present →
    Can r θ ≡
    Can (E ⟦ p ⟧e) θ
can-is-present {_} {p} {q} {S} {E} θ S∈ r≐E⟦present⟧ rewrite sym (unplug r≐E⟦present⟧) =
  can-is-present-lemma p q S θ S∈ E


canθ-is-present-lemma : ∀ {r p q E} sigs S'' S θ →
  r ≐ E ⟦ present (S ₛ) ∣⇒ p ∣⇒ q ⟧e →
  (Σ[ S''≤S ∈ S'' ≤′ S ]
    ∃ λ S-S''∈sigs →
      SigMap.lookup {_} {(S ∸ S'')ₛ} sigs S-S''∈sigs ≡ Signal.present) ⊎
  (Σ[ S<S'' ∈ S <′ S'' ]
    ∃ λ S∈Domθ →
      Env.sig-stats {S ₛ} θ S∈Domθ ≡ Signal.present) →
  Canθ sigs S'' r θ ≡
  Canθ sigs S'' (E ⟦ p ⟧e) θ

canθ-is-present-lemma [] S'' S θ r≐E⟦present⟧ (inj₁ (S''≤S , () , sigs⟨S-S''⟩≡present))
canθ-is-present-lemma [] S'' S θ r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡present)) =
  can-is-present θ S∈Domθ r≐E⟦present⟧ θS≡present

canθ-is-present-lemma (nothing ∷ sigs) S'' .S'' θ
  r≐E⟦present⟧ (inj₁ (≤′-refl , S-S''∈sigs , sigs⟨S-S''⟩≡present))
  rewrite n∸n≡0 S''
  = ⊥-elim (n∉map-suc-n-+ 0 (SigMap.keys sigs) S-S''∈sigs)
canθ-is-present-lemma (just Signal.present ∷ sigs) S'' .S'' θ
  r≐E⟦present⟧ (inj₁ (≤′-refl , S-S''∈sigs , sigs⟨S-S''⟩≡present))
  = canθ-is-present-lemma sigs (suc S'') S'' (θ ← [S]-env-present (S'' ₛ)) r≐E⟦present⟧
    (inj₂ (≤′-refl , S''∈Domθ←[S''] ,
           trans (Env.sig-stats-←-right-irr' (S'' ₛ) θ
                   ([S]-env-present (S'' ₛ)) S''∈[S''] S''∈Domθ←[S''])
                 (Env.sig-stats-1map' (S'' ₛ) Signal.present S''∈[S''])))
  where S''∈[S'']      = Env.sig-∈-single (S'' ₛ) Signal.present
        S''∈Domθ←[S''] = Env.sig-←-monoʳ (S'' ₛ) ([S]-env-present (S'' ₛ)) θ S''∈[S'']
canθ-is-present-lemma (just Signal.absent ∷ sigs) S'' .S'' θ
  r≐E⟦present⟧(inj₁ (≤′-refl , S-S''∈sigs , sigs⟨S-S''⟩≡present))
  rewrite n∸n≡0 S'' with sigs⟨S-S''⟩≡present
... | ()
canθ-is-present-lemma (just Signal.unknown ∷ sigs) S'' .S'' θ
  r≐E⟦present⟧ (inj₁ (≤′-refl , S-S''∈sigs , sigs⟨S-S''⟩≡present))
  rewrite n∸n≡0 S'' with sigs⟨S-S''⟩≡present
... | ()

canθ-is-present-lemma (nothing ∷ sigs) S'' (suc S) θ
  r≐E⟦present⟧ (inj₁ (≤′-step S''≤S , S-S''∈sigs , sigs⟨S-S''⟩≡present))
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-present-lemma sigs (suc S'') (suc S) θ
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
         SigM.n∈S {S ∸ S''} {nothing} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡present))
canθ-is-present-lemma (just Signal.present ∷ sigs) S'' (suc S) θ
  r≐E⟦present⟧ (inj₁ (≤′-step S''≤S , S-S''∈sigs , sigs⟨S-S''⟩≡present))
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-present-lemma sigs (suc S'') (suc S) (θ ← ([S]-env-present (S'' ₛ)))
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
         SigM.n∈S {S ∸ S''} {just Signal.present} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡present))
canθ-is-present-lemma (just Signal.absent ∷ sigs) S'' (suc S) θ
  r≐E⟦present⟧ (inj₁ (≤′-step S''≤S , S-S''∈sigs , sigs⟨S-S''⟩≡present))
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-present-lemma sigs (suc S'') (suc S) (θ ← ([S]-env-absent (S'' ₛ)))
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
          SigM.n∈S {S ∸ S''} {just Signal.absent} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡present))
canθ-is-present-lemma {r = r} {p} {E = E} (just Signal.unknown ∷ sigs) S'' (suc S) θ
  r≐E⟦present⟧ (inj₁ (≤′-step S''≤S , S-S''∈sigs , sigs⟨S-S''⟩≡present))
  with any (_≟_ S'') (Canθₛ sigs (suc S'') (E ⟦ p ⟧e) (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') r (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sig-E⟦p⟧-θ←[S''] | yes S''∈canθ-sig-r-θ←[S'']
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-present-lemma sigs (suc S'') (suc S) (θ ← ([S]-env (S'' ₛ)))
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
          SigM.n∈S {S ∸ S''} {just Signal.unknown} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡present))
... | no  S''∉canθ-sig-E⟦p⟧-θ←[S''] | no  S''∉canθ-sig-r-θ←[S'']
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-present-lemma sigs (suc S'') (suc S) (θ ← ([S]-env-absent (S'' ₛ)))
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
          SigM.n∈S {S ∸ S''} {just Signal.unknown} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡present))
... | yes S''∈canθ-sig-E⟦p⟧-θ←[S''] | no  S''∉canθ-sig-r-θ←[S'']
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
        | canθ-is-present-lemma sigs (suc S'') (suc S) (θ ← ([S]-env (S'' ₛ)))
            r≐E⟦present⟧
            (inj₁
              (s≤′s S''≤S ,
              SigM.n∈S {S ∸ S''} {just Signal.unknown} {sigs} S-S''∈sigs ,
              sigs⟨S-S''⟩≡present))
  = ⊥-elim (S''∉canθ-sig-r-θ←[S''] S''∈canθ-sig-E⟦p⟧-θ←[S''])
... | no  S''∉canθ-sig-E⟦p⟧-θ←[S''] | yes S''∈canθ-sig-r-θ←[S'']
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
        | canθ-is-present-lemma sigs (suc S'') (suc S) (θ ← ([S]-env (S'' ₛ)))
            r≐E⟦present⟧
            (inj₁
              (s≤′s S''≤S ,
              SigM.n∈S {S ∸ S''} {just Signal.unknown} {sigs} S-S''∈sigs ,
              sigs⟨S-S''⟩≡present))
  = ⊥-elim (S''∉canθ-sig-E⟦p⟧-θ←[S''] S''∈canθ-sig-r-θ←[S''])

canθ-is-present-lemma (nothing ∷ sigs) S'' S θ
  r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡present))
  = canθ-is-present-lemma sigs (suc S'') S θ
      r≐E⟦present⟧
      (inj₂
        (≤′-step S<S'' ,
         S∈Domθ ,
         θS≡present))
canθ-is-present-lemma (just Signal.present ∷ sigs) S'' S θ
  r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡present)) =
  canθ-is-present-lemma sigs (suc S'') S (θ ← [S]-env-present (S'' ₛ))
    r≐E⟦present⟧
    (inj₂
      (≤′-step S<S'' ,
       S∈Domθ←[S''] ,
       trans (sym θS≡⟨θ←[S'']⟩S) θS≡present))
  where
    S∈Domθ←[S'']  = Env.sig-←-monoˡ (S ₛ) θ ([S]-env-present (S'' ₛ)) S∈Domθ
    θS≡⟨θ←[S'']⟩S =
      Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env-present (S'' ₛ)) S∈Domθ
        (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.present
          (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
        S∈Domθ←[S'']
canθ-is-present-lemma (just Signal.absent ∷ sigs) S'' S θ
  r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡present)) =
  canθ-is-present-lemma sigs (suc S'') S (θ ← [S]-env-absent (S'' ₛ))
    r≐E⟦present⟧
    (inj₂
      (≤′-step S<S'' ,
       S∈Domθ←[S''] ,
       trans (sym θS≡⟨θ←[S'']⟩S) θS≡present))
  where
    S∈Domθ←[S'']  = Env.sig-←-monoˡ (S ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ
    θS≡⟨θ←[S'']⟩S =
      Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ
        (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.absent
          (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
        S∈Domθ←[S'']
canθ-is-present-lemma {r = r} {p} {E = E} (just Signal.unknown ∷ sigs) S'' S θ
  r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡present))
  with any (_≟_ S'') (Canθₛ sigs (suc S'') (E ⟦ p ⟧e) (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') r (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sig-E⟦p⟧-θ←[S''] | yes S''∈canθ-sig-r-θ←[S''] =
  canθ-is-present-lemma sigs (suc S'') S (θ ← [S]-env (S'' ₛ))
    r≐E⟦present⟧
    (inj₂
      (≤′-step S<S'' ,
       S∈Domθ←[S''] ,
       trans (sym θS≡⟨θ←[S'']⟩S) θS≡present))
  where
    S∈Domθ←[S'']  = Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ
    θS≡⟨θ←[S'']⟩S =
      Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ
        (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.unknown
          (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
        S∈Domθ←[S'']
... | no  S''∉canθ-sig-E⟦p⟧-θ←[S''] | no  S''∉canθ-sig-r-θ←[S''] =
  canθ-is-present-lemma sigs (suc S'') S (θ ← [S]-env-absent (S'' ₛ))
    r≐E⟦present⟧
    (inj₂
      (≤′-step S<S'' ,
       S∈Domθ←[S''] ,
       trans (sym θS≡⟨θ←[S'']⟩S) θS≡present))
  where
    S∈Domθ←[S'']  = Env.sig-←-monoˡ (S ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ
    θS≡⟨θ←[S'']⟩S =
      Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ
        (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.absent
          (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
        S∈Domθ←[S'']
... | yes S''∈canθ-sig-E⟦p⟧-θ←[S''] | no  S''∉canθ-sig-r-θ←[S'']
  rewrite canθ-is-present-lemma sigs (suc S'') S (θ ← [S]-env (S'' ₛ))
            r≐E⟦present⟧
            (inj₂
              (≤′-step S<S'' ,
               Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ ,
               (trans
                 (sym
                   (Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ
                     (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.unknown
                       (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
                     (Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ)))
                 θS≡present)))
  = ⊥-elim (S''∉canθ-sig-r-θ←[S''] S''∈canθ-sig-E⟦p⟧-θ←[S''])
... | no  S''∉canθ-sig-E⟦p⟧-θ←[S''] | yes S''∈canθ-sig-r-θ←[S'']
  rewrite canθ-is-present-lemma sigs (suc S'') S (θ ← [S]-env (S'' ₛ))
            r≐E⟦present⟧
            (inj₂
              (≤′-step S<S'' ,
               Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ ,
               (trans
                 (sym
                   (Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ
                     (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.unknown
                       (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
                     (Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ)))
                 θS≡present)))
  = ⊥-elim (S''∉canθ-sig-E⟦p⟧-θ←[S''] S''∈canθ-sig-r-θ←[S''])


canθ-is-present : ∀ {S r p q E} sigs S∈ θ → -- perhaps θ is not needed at all
  r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e →
  SigMap.lookup {_} {S} sigs S∈ ≡ Signal.present →
  Canθ sigs 0 r θ ≡
  Canθ sigs 0 (E ⟦ p ⟧e) θ
canθ-is-present {S ₛ} sigs S∈ θ r≐E⟦present⟧ sigs-S≡present =
  canθ-is-present-lemma sigs 0 S θ r≐E⟦present⟧
    (inj₁ (z≤′n , S∈ , sigs-S≡present))


can-is-absent : ∀ {r p q S E} θ S∈ →
  r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e →
  Env.sig-stats {S} θ S∈ ≡ Signal.absent →
    Can r θ ≡
    Can (E ⟦ q ⟧e) θ
can-is-absent {_} {p} {q} {S} {E} θ S∈ r≐E⟦present⟧ rewrite sym (unplug r≐E⟦present⟧) =
  can-is-absent-lemma p q S θ S∈ E


canθ-is-absent-lemma : ∀ {r p q E} sigs S'' S θ →
  r ≐ E ⟦ present (S ₛ) ∣⇒ q ∣⇒ p ⟧e →
  (Σ[ S''≤S ∈ S'' ≤′ S ]
    ∃ λ S-S''∈sigs →
      SigMap.lookup {_} {(S ∸ S'')ₛ} sigs S-S''∈sigs ≡ Signal.absent) ⊎
  (Σ[ S<S'' ∈ S <′ S'' ]
    ∃ λ S∈Domθ →
      Env.sig-stats {S ₛ} θ S∈Domθ ≡ Signal.absent) →
  Canθ sigs S'' r θ ≡
  Canθ sigs S'' (E ⟦ p ⟧e) θ

canθ-is-absent-lemma [] S'' S θ r≐E⟦present⟧ (inj₁ (S''≤S , () , sigs⟨S-S''⟩≡absent))
canθ-is-absent-lemma [] S'' S θ r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡absent)) =
  can-is-absent θ S∈Domθ r≐E⟦present⟧ θS≡absent

canθ-is-absent-lemma (nothing ∷ sigs) S'' .S'' θ
  r≐E⟦present⟧ (inj₁ (≤′-refl , S-S''∈sigs , sigs⟨S-S''⟩≡absent))
  rewrite n∸n≡0 S''
  = ⊥-elim (n∉map-suc-n-+ 0 (SigMap.keys sigs) S-S''∈sigs)
canθ-is-absent-lemma (just Signal.present ∷ sigs) S'' .S'' θ
  r≐E⟦present⟧(inj₁ (≤′-refl , S-S''∈sigs , sigs⟨S-S''⟩≡absent))
  rewrite n∸n≡0 S'' with sigs⟨S-S''⟩≡absent
... | ()
canθ-is-absent-lemma (just Signal.absent ∷ sigs) S'' .S'' θ
  r≐E⟦present⟧ (inj₁ (≤′-refl , S-S''∈sigs , sigs⟨S-S''⟩≡absent))
  = canθ-is-absent-lemma sigs (suc S'') S'' (θ ← [S]-env-absent (S'' ₛ)) r≐E⟦present⟧
    (inj₂ (≤′-refl , S''∈Domθ←[S''] ,
           trans (Env.sig-stats-←-right-irr' (S'' ₛ) θ
                   ([S]-env-absent (S'' ₛ)) S''∈[S''] S''∈Domθ←[S''])
                 (Env.sig-stats-1map' (S'' ₛ) Signal.absent S''∈[S''])))
  where S''∈[S'']      = Env.sig-∈-single (S'' ₛ) Signal.absent
        S''∈Domθ←[S''] = Env.sig-←-monoʳ (S'' ₛ) ([S]-env-absent (S'' ₛ)) θ S''∈[S'']
canθ-is-absent-lemma (just Signal.unknown ∷ sigs) S'' .S'' θ
  r≐E⟦present⟧ (inj₁ (≤′-refl , S-S''∈sigs , sigs⟨S-S''⟩≡absent))
  rewrite n∸n≡0 S'' with sigs⟨S-S''⟩≡absent
... | ()

canθ-is-absent-lemma (nothing ∷ sigs) S'' (suc S) θ
  r≐E⟦present⟧ (inj₁ (≤′-step S''≤S , S-S''∈sigs , sigs⟨S-S''⟩≡absent))
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-absent-lemma sigs (suc S'') (suc S) θ
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
         SigM.n∈S {S ∸ S''} {nothing} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡absent))
canθ-is-absent-lemma (just Signal.present ∷ sigs) S'' (suc S) θ
  r≐E⟦present⟧ (inj₁ (≤′-step S''≤S , S-S''∈sigs , sigs⟨S-S''⟩≡absent))
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-absent-lemma sigs (suc S'') (suc S) (θ ← ([S]-env-present (S'' ₛ)))
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
         SigM.n∈S {S ∸ S''} {just Signal.present} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡absent))
canθ-is-absent-lemma (just Signal.absent ∷ sigs) S'' (suc S) θ
  r≐E⟦present⟧ (inj₁ (≤′-step S''≤S , S-S''∈sigs , sigs⟨S-S''⟩≡absent))
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-absent-lemma sigs (suc S'') (suc S) (θ ← ([S]-env-absent (S'' ₛ)))
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
          SigM.n∈S {S ∸ S''} {just Signal.absent} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡absent))
canθ-is-absent-lemma {r = r} {p} {E = E} (just Signal.unknown ∷ sigs) S'' (suc S) θ
  r≐E⟦present⟧ (inj₁ (≤′-step S''≤S , S-S''∈sigs , sigs⟨S-S''⟩≡absent))
  with any (_≟_ S'') (Canθₛ sigs (suc S'') (E ⟦ p ⟧e) (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') r (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sig-E⟦p⟧-θ←[S''] | yes S''∈canθ-sig-r-θ←[S'']
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-absent-lemma sigs (suc S'') (suc S) (θ ← ([S]-env (S'' ₛ)))
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
          SigM.n∈S {S ∸ S''} {just Signal.unknown} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡absent))
... | no  S''∉canθ-sig-E⟦p⟧-θ←[S''] | no  S''∉canθ-sig-r-θ←[S'']
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
  = canθ-is-absent-lemma sigs (suc S'') (suc S) (θ ← ([S]-env-absent (S'' ₛ)))
      r≐E⟦present⟧
      (inj₁
        (s≤′s S''≤S ,
          SigM.n∈S {S ∸ S''} {just Signal.unknown} {sigs} S-S''∈sigs ,
         sigs⟨S-S''⟩≡absent))
... | yes S''∈canθ-sig-E⟦p⟧-θ←[S''] | no  S''∉canθ-sig-r-θ←[S'']
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
        | canθ-is-absent-lemma sigs (suc S'') (suc S) (θ ← ([S]-env (S'' ₛ)))
            r≐E⟦present⟧
            (inj₁
              (s≤′s S''≤S ,
              SigM.n∈S {S ∸ S''} {just Signal.unknown} {sigs} S-S''∈sigs ,
              sigs⟨S-S''⟩≡absent))
  = ⊥-elim (S''∉canθ-sig-r-θ←[S''] S''∈canθ-sig-E⟦p⟧-θ←[S''])
... | no  S''∉canθ-sig-E⟦p⟧-θ←[S''] | yes S''∈canθ-sig-r-θ←[S'']
  rewrite +-∸-assoc 1 (≤′⇒≤ S''≤S)
        | canθ-is-absent-lemma sigs (suc S'') (suc S) (θ ← ([S]-env (S'' ₛ)))
            r≐E⟦present⟧
            (inj₁
              (s≤′s S''≤S ,
              SigM.n∈S {S ∸ S''} {just Signal.unknown} {sigs} S-S''∈sigs ,
              sigs⟨S-S''⟩≡absent))
  = ⊥-elim (S''∉canθ-sig-E⟦p⟧-θ←[S''] S''∈canθ-sig-r-θ←[S''])

canθ-is-absent-lemma (nothing ∷ sigs) S'' S θ
  r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡absent))
  = canθ-is-absent-lemma sigs (suc S'') S θ
      r≐E⟦present⟧
      (inj₂
        (≤′-step S<S'' ,
         S∈Domθ ,
         θS≡absent))
canθ-is-absent-lemma (just Signal.present ∷ sigs) S'' S θ
  r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡absent)) =
  canθ-is-absent-lemma sigs (suc S'') S (θ ← [S]-env-present (S'' ₛ))
    r≐E⟦present⟧
    (inj₂
      (≤′-step S<S'' ,
       S∈Domθ←[S''] ,
       trans (sym θS≡⟨θ←[S'']⟩S) θS≡absent))
  where
    S∈Domθ←[S'']  = Env.sig-←-monoˡ (S ₛ) θ ([S]-env-present (S'' ₛ)) S∈Domθ
    θS≡⟨θ←[S'']⟩S =
      Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env-present (S'' ₛ)) S∈Domθ
        (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.present
          (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
        S∈Domθ←[S'']
canθ-is-absent-lemma (just Signal.absent ∷ sigs) S'' S θ
  r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡absent)) =
  canθ-is-absent-lemma sigs (suc S'') S (θ ← [S]-env-absent (S'' ₛ))
    r≐E⟦present⟧
    (inj₂
      (≤′-step S<S'' ,
       S∈Domθ←[S''] ,
       trans (sym θS≡⟨θ←[S'']⟩S) θS≡absent))
  where
    S∈Domθ←[S'']  = Env.sig-←-monoˡ (S ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ
    θS≡⟨θ←[S'']⟩S =
      Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ
        (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.absent
          (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
        S∈Domθ←[S'']
canθ-is-absent-lemma {r = r} {p} {E = E} (just Signal.unknown ∷ sigs) S'' S θ
  r≐E⟦present⟧ (inj₂ (S<S'' , S∈Domθ , θS≡absent))
  with any (_≟_ S'') (Canθₛ sigs (suc S'') (E ⟦ p ⟧e) (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') r (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sig-E⟦p⟧-θ←[S''] | yes S''∈canθ-sig-r-θ←[S''] =
  canθ-is-absent-lemma sigs (suc S'') S (θ ← [S]-env (S'' ₛ))
    r≐E⟦present⟧
    (inj₂
      (≤′-step S<S'' ,
       S∈Domθ←[S''] ,
       trans (sym θS≡⟨θ←[S'']⟩S) θS≡absent))
  where
    S∈Domθ←[S'']  = Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ
    θS≡⟨θ←[S'']⟩S =
      Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ
        (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.unknown
          (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
        S∈Domθ←[S'']
... | no  S''∉canθ-sig-E⟦p⟧-θ←[S''] | no  S''∉canθ-sig-r-θ←[S''] =
  canθ-is-absent-lemma sigs (suc S'') S (θ ← [S]-env-absent (S'' ₛ))
    r≐E⟦present⟧
    (inj₂
      (≤′-step S<S'' ,
       S∈Domθ←[S''] ,
       trans (sym θS≡⟨θ←[S'']⟩S) θS≡absent))
  where
    S∈Domθ←[S'']  = Env.sig-←-monoˡ (S ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ
    θS≡⟨θ←[S'']⟩S =
      Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env-absent (S'' ₛ)) S∈Domθ
        (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.absent
          (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
        S∈Domθ←[S'']
... | yes S''∈canθ-sig-E⟦p⟧-θ←[S''] | no  S''∉canθ-sig-r-θ←[S'']
  rewrite canθ-is-absent-lemma sigs (suc S'') S (θ ← [S]-env (S'' ₛ))
            r≐E⟦present⟧
            (inj₂
              (≤′-step S<S'' ,
               Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ ,
               (trans
                 (sym
                   (Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ
                     (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.unknown
                       (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
                     (Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ)))
                 θS≡absent)))
  = ⊥-elim (S''∉canθ-sig-r-θ←[S''] S''∈canθ-sig-E⟦p⟧-θ←[S''])
... | no  S''∉canθ-sig-E⟦p⟧-θ←[S''] | yes S''∈canθ-sig-r-θ←[S'']
  rewrite canθ-is-absent-lemma sigs (suc S'') S (θ ← [S]-env (S'' ₛ))
            r≐E⟦present⟧
            (inj₂
              (≤′-step S<S'' ,
               Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ ,
               (trans
                 (sym
                   (Env.sig-←-∉-irr-stats' (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ
                     (Env.sig-∉-single (S ₛ) (S'' ₛ) Signal.unknown
                       (<⇒≢ (≤′⇒≤ S<S'') ∘ cong Signal.unwrap))
                     (Env.sig-←-monoˡ (S ₛ) θ ([S]-env (S'' ₛ)) S∈Domθ)))
                 θS≡absent)))
  = ⊥-elim (S''∉canθ-sig-E⟦p⟧-θ←[S''] S''∈canθ-sig-r-θ←[S''])


canθ-is-absent : ∀ {S r p q E} sigs S∈ θ →
  r ≐ E ⟦ present S ∣⇒ q ∣⇒ p ⟧e →
  SigMap.lookup {_} {S} sigs S∈ ≡ Signal.absent →
  Canθ sigs 0 r θ ≡
  Canθ sigs 0 (E ⟦ p ⟧e) θ
canθ-is-absent {S ₛ} sigs S∈ θ r≐E⟦present⟧ sigs-S≡absent =
  canθ-is-absent-lemma sigs 0 S θ r≐E⟦present⟧
    (inj₁ (z≤′n , S∈ , sigs-S≡absent))


canₛₕ-emit-lemma : ∀ S θ E →
  ∀ s →
    s ∈ Canₛₕ (E ⟦ nothin ⟧e) θ →
    s ∈ Canₛₕ (E ⟦ emit S ⟧e) θ
canₛₕ-emit-lemma S θ [] s s∈can-E⟦nothin⟧ = s∈can-E⟦nothin⟧
canₛₕ-emit-lemma S θ (epar₁ q ∷ E) s s∈can-E∥q⟦nothin⟧
  with ++⁻ (Canₛₕ (E ⟦ nothin ⟧e) θ) s∈can-E∥q⟦nothin⟧
... | inj₁ s∈can-E⟦nothin⟧ = ++ˡ (canₛₕ-emit-lemma S θ E s s∈can-E⟦nothin⟧)
... | inj₂ s∈can-q = ++ʳ (Canₛₕ (E ⟦ emit S ⟧e) θ) s∈can-q
canₛₕ-emit-lemma S θ (epar₂ p ∷ E) s s∈can-p∥E⟦nothin⟧
  with ++⁻ (Canₛₕ p θ) s∈can-p∥E⟦nothin⟧
... | inj₁ s∈can-p = ++ˡ s∈can-p
... | inj₂ s∈can-E⟦nothin⟧ = ++ʳ (Canₛₕ p θ) (canₛₕ-emit-lemma S θ E s s∈can-E⟦nothin⟧)
canₛₕ-emit-lemma S θ (eloopˢ q ∷ E) s s∈can-E⟦nothin⟧ = canₛₕ-emit-lemma S θ E s s∈can-E⟦nothin⟧
canₛₕ-emit-lemma S θ (eseq q ∷ E) s s∈can-E⟦nothin⟧
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ emit S ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ nothin ⟧e) θ)
... | yes nothin∈can-E⟦emit⟧ | no  nothin∉can-E⟦nothin⟧ =
  ⊥-elim (nothin∉can-E⟦nothin⟧
            (canₖ-term-nothin-lemma θ E (temit S) tnothin
              Code.nothin nothin∈can-E⟦emit⟧))
... | no  nothin∉can-E⟦emit⟧ | yes nothin∈can-E⟦nothin⟧ =
  ⊥-elim (nothin∉can-E⟦emit⟧
            (canₖ-term-nothin-lemma θ E tnothin (temit S)
              Code.nothin nothin∈can-E⟦nothin⟧))
... | no  nothin∉can-E⟦emit⟧ | no  nothin∉can-E⟦nothin⟧ =
  canₛₕ-emit-lemma S θ E s s∈can-E⟦nothin⟧
... | yes nothin∈can-E⟦emit⟧ | yes nothin∈can-E⟦nothin⟧
  with ++⁻ (Canₛₕ (E ⟦ nothin ⟧e) θ) s∈can-E⟦nothin⟧
... | inj₁ s∈can-E⟦nothin⟧-θ = ++ˡ (canₛₕ-emit-lemma S θ E s s∈can-E⟦nothin⟧-θ)
... | inj₂ s∈can-q-θ = ++ʳ (Canₛₕ (E ⟦ emit S ⟧e) θ) s∈can-q-θ
canₛₕ-emit-lemma S θ (esuspend S' ∷ E) s s∈can-E⟦nothin⟧ =
  canₛₕ-emit-lemma S θ E s s∈can-E⟦nothin⟧
canₛₕ-emit-lemma S θ (etrap ∷ E) s s∈can-E⟦nothin⟧ =
  canₛₕ-emit-lemma S θ E s s∈can-E⟦nothin⟧


canₛₕ-emit : ∀ {S r E} θ S∈ →
  r ≐ E ⟦ emit S ⟧e →
  ¬ (Env.sig-stats {S} θ S∈ ≡ Signal.absent) →
  ∀ s →
    SharedVar.unwrap s ∈ Canₛₕ (E ⟦ nothin ⟧e) (Env.set-sig {S} θ S∈ Signal.present) →
    SharedVar.unwrap s ∈ Canₛₕ r θ
canₛₕ-emit {S} {r} {E} θ S∈ r≐E⟦emitS⟧ θS≢absent s s∈can-E⟦nothin⟧-θ'
  rewrite sym (unplug r≐E⟦emitS⟧)
  with Env.sig-stats {S} θ S∈ | inspect (Env.sig-stats {S} θ) S∈
... | Signal.present | [ θS≡present ]
  rewrite (sym θS≡present) | sym (SigMap.getput-m S (Env.sig θ) S∈)
  = canₛₕ-emit-lemma S θ E (SharedVar.unwrap s) s∈can-E⟦nothin⟧-θ'
... | Signal.absent  | [ θS≡absent  ] = ⊥-elim (θS≢absent refl)
... | Signal.unknown | [ θS≡unknown ] =
  canₛₕ-emit-lemma S θ E (SharedVar.unwrap s)
    (canₛₕ-set-sig-monotonic (E ⟦ nothin ⟧e) S θ S∈ Signal.present
      θS≡unknown (SharedVar.unwrap s) s∈can-E⟦nothin⟧-θ')


canₛ-emit-lemma : ∀ S θ E →
  ∀ S'' →
    S'' ∈ Canₛ (E ⟦ nothin ⟧e) θ →
    S'' ∈ Canₛ (E ⟦ emit S ⟧e) θ
canₛ-emit-lemma S θ [] S'' ()
canₛ-emit-lemma S θ (epar₁ q ∷ E) S'' S''∈can-E∥q⟦nothin⟧
  with ++⁻ (Canₛ (E ⟦ nothin ⟧e) θ) S''∈can-E∥q⟦nothin⟧
... | inj₁ S''∈can-E⟦nothin⟧ = ++ˡ (canₛ-emit-lemma S θ E S'' S''∈can-E⟦nothin⟧)
... | inj₂ S''∈can-q = ++ʳ (Canₛ (E ⟦ emit S ⟧e) θ) S''∈can-q
canₛ-emit-lemma S θ (epar₂ p ∷ E) S'' S''∈can-p∥E⟦nothin⟧
  with ++⁻ (Canₛ p θ) S''∈can-p∥E⟦nothin⟧
... | inj₁ S''∈can-p = ++ˡ S''∈can-p
... | inj₂ S''∈can-E⟦nothin⟧ = ++ʳ (Canₛ p θ) (canₛ-emit-lemma S θ E S'' S''∈can-E⟦nothin⟧)
canₛ-emit-lemma S θ (eloopˢ q ∷ E) S'' S''∈can-E⟦nothin⟧ = canₛ-emit-lemma S θ E S'' S''∈can-E⟦nothin⟧
canₛ-emit-lemma S θ (eseq q ∷ E) S'' S''∈can-E⟦nothin⟧
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ emit S ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ nothin ⟧e) θ)
... | yes nothin∈can-E⟦emit⟧ | no  nothin∉can-E⟦nothin⟧ =
  ⊥-elim (nothin∉can-E⟦nothin⟧
            (canₖ-term-nothin-lemma θ E (temit S) tnothin
              Code.nothin nothin∈can-E⟦emit⟧))
... | no  nothin∉can-E⟦emit⟧ | yes nothin∈can-E⟦nothin⟧ =
  ⊥-elim (nothin∉can-E⟦emit⟧
            (canₖ-term-nothin-lemma θ E tnothin (temit S)
              Code.nothin nothin∈can-E⟦nothin⟧))
... | no  nothin∉can-E⟦emit⟧ | no  nothin∉can-E⟦nothin⟧ =
  canₛ-emit-lemma S θ E S'' S''∈can-E⟦nothin⟧
... | yes nothin∈can-E⟦emit⟧ | yes nothin∈can-E⟦nothin⟧
  with ++⁻ (Canₛ (E ⟦ nothin ⟧e) θ) S''∈can-E⟦nothin⟧
... | inj₁ S''∈can-E⟦nothin⟧-θ = ++ˡ (canₛ-emit-lemma S θ E S'' S''∈can-E⟦nothin⟧-θ)
... | inj₂ S''∈can-q-θ = ++ʳ (Canₛ (E ⟦ emit S ⟧e) θ) S''∈can-q-θ
canₛ-emit-lemma S θ (esuspend S' ∷ E) S'' S''∈can-E⟦nothin⟧ =
  canₛ-emit-lemma S θ E S'' S''∈can-E⟦nothin⟧
canₛ-emit-lemma S θ (etrap ∷ E) S'' S''∈can-E⟦nothin⟧ =
  canₛ-emit-lemma S θ E S'' S''∈can-E⟦nothin⟧




canₛ-emit : ∀ {S r E} θ S∈ →
  r ≐ E ⟦ emit S ⟧e →
  ¬ (Env.sig-stats {S} θ S∈ ≡ Signal.absent) →
  ∀ S'' →
    Signal.unwrap S'' ∈ Canₛ (E ⟦ nothin ⟧e) (Env.set-sig {S} θ S∈ Signal.present) →
    Signal.unwrap S'' ∈ Canₛ r θ
canₛ-emit {S} {r} {E} θ S∈ r≐E⟦emitS⟧ θS≢absent S'' S''∈can-E⟦nothin⟧-θ'
  rewrite sym (unplug r≐E⟦emitS⟧)
  with Env.sig-stats {S} θ S∈ | inspect (Env.sig-stats {S} θ) S∈
... | Signal.present | [ θS≡present ]
  rewrite (sym θS≡present) | sym (SigMap.getput-m S (Env.sig θ) S∈)
  = canₛ-emit-lemma S θ E (Signal.unwrap S'') S''∈can-E⟦nothin⟧-θ'
... | Signal.absent  | [ θS≡absent  ] = ⊥-elim (θS≢absent refl)
... | Signal.unknown | [ θS≡unknown ] =
  canₛ-emit-lemma S θ E (Signal.unwrap S'')
    (canₛ-set-sig-monotonic (E ⟦ nothin ⟧e) S θ S∈ Signal.present
      θS≡unknown (Signal.unwrap S'') S''∈can-E⟦nothin⟧-θ')

canθₛ-emit-lemma : ∀ sigs S'' p θ S S∈ →
  (S'' + S) ∈ Canθₛ sigs S'' p θ →
  SigMap.lookup {_} {S ₛ} sigs S∈ ≡ Signal.unknown →
  ∀ S' →
    S' ∈ Canθₛ (SigMap.update sigs (S ₛ) Signal.present) S'' p θ →
    S' ∈ Canθₛ sigs S'' p θ

canθₖ-emit-lemma : ∀ sigs S'' p θ S S∈ →
  (S'' + S) ∈ Canθₛ sigs S'' p θ →
  SigMap.lookup {_} {S ₛ} sigs S∈ ≡ Signal.unknown →
  ∀ k →
    k ∈ Canθₖ (SigMap.update sigs (S ₛ) Signal.present) S'' p θ →
    k ∈ Canθₖ sigs S'' p θ
canθₖ-emit-lemma [] S'' p θ S () S''+S∈canθ-sigs-p-θ lk==u k k∈
canθₖ-emit-lemma (nothing ∷ sigs) S'' p θ zero S∈ S''+S∈canθ-sigs-p-θ lk==u k k∈ =  ⊥-elim (SigM.0∈S S∈)
canθₖ-emit-lemma (just Signal.present ∷ sigs) S'' p θ zero S∈ S''+S∈canθ-sigs-p-θ () k k∈
canθₖ-emit-lemma (just Signal.absent ∷ sigs) S'' p θ zero S∈ S''+S∈canθ-sigs-p-θ () k k∈
canθₖ-emit-lemma (just Signal.unknown ∷ sigs) S'' p θ zero S∈ S''+S∈canθ-sigs-p-θ lk==u k k∈
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
... | yes is∈ = canθₖ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.present k k∈
... | no ¬is∈ rewrite +-comm S'' 0 =  ⊥-elim
      (¬is∈
        (canθₛ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.absent
           S'' S''+S∈canθ-sigs-p-θ))
canθₖ-emit-lemma (nothing ∷ sigs) S'' p θ (suc S) S∈ S''+S∈canθ-sigs-p-θ lk==u k k∈
    rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₖ-emit-lemma sigs (suc S'') p θ S (SigM.n∈S {S} {nothing} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ lk==u k k∈
canθₖ-emit-lemma (just Signal.present ∷ sigs) S'' p θ (suc S) S∈ S''+S∈canθ-sigs-p-θ lk==u k k∈
    rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₖ-emit-lemma sigs (suc S'') p (θ ← [S]-env-present (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.present} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ lk==u k k∈
canθₖ-emit-lemma (just Signal.absent ∷ sigs) S'' p θ (suc S) S∈ S''+S∈canθ-sigs-p-θ lk==u k k∈
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₖ-emit-lemma sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.absent} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ lk==u k k∈
canθₖ-emit-lemma (just Signal.unknown ∷ sigs) S'' p θ (suc S) S∈ S''+S∈canθ-sigs-p-θ lk==u k k∈
    with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ (SigMap.update sigs (S ₛ) Signal.present) (suc S'') p
                       (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sigs-p-θ←[S''] | yes S''∈canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  =  canθₖ-emit-lemma sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ lk==u k k∈ 
... | no  S''∉canθ-sigs-p-θ←[S''] | no  S''∉canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  =  canθₖ-emit-lemma sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ lk==u k k∈
... | no  S''∉canθ-sigs-p-θ←[S''] | yes S''∈canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  =  ⊥-elim
      (S''∉canθ-sigs-p-θ←[S'']
        (canθₛ-emit-lemma sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S
          (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
          (canθₛ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.absent
             (suc (S'' + S)) S''+S∈canθ-sigs-p-θ)
          lk==u S'' S''∈canθ-θ'-p-θ←[S''])) 
... | yes S''∈canθ-sigs-p-θ←[S''] | no  S''∉canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  =  canθₖ-emit-lemma sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ lk==u k
      (canθₖ-add-sig-monotonic
         (SigM.m-insert (just Signal.present) S sigs) (suc S'') p θ (S'' ₛ)
          Signal.absent k k∈)



canθₛ-emit-lemma [] S'' p θ S () S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
canθₛ-emit-lemma (nothing ∷ sigs) S'' p θ zero S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p =
  ⊥-elim (SigM.0∈S S∈)
canθₛ-emit-lemma (nothing ∷ sigs) S'' p θ (suc S) S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛ-emit-lemma sigs (suc S'') p θ S (SigM.n∈S {S} {nothing} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
canθₛ-emit-lemma (just Signal.present ∷ sigs) S'' p θ 0 S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
  with sigs-S≡unknown
... | ()
canθₛ-emit-lemma (just Signal.absent ∷ sigs) S'' p θ 0 S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
  with sigs-S≡unknown
... | ()
canθₛ-emit-lemma (just Signal.unknown ∷ sigs) S'' p θ 0 S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
... | no  S''∉canθ-sigs-θ←[S''] rewrite +-comm S'' 0
  = ⊥-elim
      (S''∉canθ-sigs-θ←[S'']
        (canθₛ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.absent
           S'' S''+S∈canθ-sigs-p-θ))
... | yes S''∈canθ-sigs-θ↽[S''] =
  canθₛ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.present
    S' S'∈canθ-θ'-p
canθₛ-emit-lemma (just Signal.present ∷ sigs) S'' p θ (suc S) S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛ-emit-lemma sigs (suc S'') p (θ ← [S]-env-present (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.present} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
canθₛ-emit-lemma (just Signal.absent ∷ sigs) S'' p θ (suc S) S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛ-emit-lemma sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.absent} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
canθₛ-emit-lemma (just Signal.unknown ∷ sigs) S'' p θ (suc S) S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ (SigMap.update sigs (S ₛ) Signal.present) (suc S'') p
                       (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sigs-p-θ←[S''] | yes S''∈canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛ-emit-lemma sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
... | no  S''∉canθ-sigs-p-θ←[S''] | no  S''∉canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛ-emit-lemma sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown S' S'∈canθ-θ'-p
... | no  S''∉canθ-sigs-p-θ←[S''] | yes S''∈canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  = ⊥-elim
      (S''∉canθ-sigs-p-θ←[S'']
        (canθₛ-emit-lemma sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S
          (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
          (canθₛ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.absent
             (suc (S'' + S)) S''+S∈canθ-sigs-p-θ)
          sigs-S≡unknown S'' S''∈canθ-θ'-p-θ←[S'']))
... | yes S''∈canθ-sigs-p-θ←[S''] | no  S''∉canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛ-emit-lemma sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown S'
      (canθₛ-add-sig-monotonic
         (SigM.m-insert (just Signal.present) S sigs) (suc S'') p θ (S'' ₛ)
         Signal.absent S' S'∈canθ-θ'-p)


canθₛ-emit : ∀ {S r E} θ S∈ θ' →
  r ≐ E ⟦ emit S ⟧e →
  ¬ (Env.sig-stats {S} θ S∈ ≡ Signal.absent) →
  Signal.unwrap S ∈ Canθₛ (Env.sig θ) 0 r θ' →
  ∀ S'' →
    Signal.unwrap S'' ∈ Canθₛ (Env.sig (Env.set-sig {S} θ S∈ Signal.present)) 0
                          (E ⟦ nothin ⟧e) θ' →
    Signal.unwrap S'' ∈ Canθₛ (Env.sig θ) 0
                          r θ'
canθₛ-emit {S} {r} {E} θ S∈ θ' r≐E⟦emitS⟧ θS≢absent S∈canθ-r S'' S''∈canθ-E⟦nothin⟧
  rewrite sym (unplug r≐E⟦emitS⟧)
  with Env.sig-stats {S} θ S∈ | inspect (Env.sig-stats {S} θ) S∈
... | Signal.present | [ θS≡present ]
  rewrite (sym θS≡present) | sym (SigMap.getput-m S (Env.sig θ) S∈)
  = canθₛ-subset-lemma (Env.sig θ) 0 (E ⟦ nothin ⟧e) (E ⟦ emit S ⟧e) θ'
      (λ θ* S* → canₛ-emit-lemma S θ* E S*)
      (Signal.unwrap S'') S''∈canθ-E⟦nothin⟧
... | Signal.absent  | [ θS≡absent  ] = ⊥-elim (θS≢absent refl)
... | Signal.unknown | [ θS≡unknown ] =
  canθₛ-emit-lemma (Env.sig θ) 0 (E ⟦ emit S ⟧e) θ' (Signal.unwrap S) S∈
    S∈canθ-r θS≡unknown (Signal.unwrap S'')
    (canθₛ-subset-lemma (Env.sig (Env.set-sig {S} θ S∈ Signal.present)) 0
      (E ⟦ nothin ⟧e) (E ⟦ emit S ⟧e) θ'
      (λ θ* S* → canₛ-emit-lemma S θ* E S*) (Signal.unwrap S'')
      S''∈canθ-E⟦nothin⟧)

canθₖ-emit : ∀ {S r E} θ S∈ θ' →
  r ≐ E ⟦ emit S ⟧e →
  ¬ (Env.sig-stats {S} θ S∈ ≡ Signal.absent) →
  Signal.unwrap S ∈ Canθₛ (Env.sig θ) 0 r θ' →
  ∀ k →
    k ∈ Canθₖ (Env.sig (Env.set-sig {S} θ S∈ Signal.present)) 0
              (E ⟦ nothin ⟧e) θ' →
    k ∈ Canθₖ (Env.sig θ) 0
              r θ'
canθₖ-emit {S} {r} {E} θ S∈ θ' r≐E⟦emitS⟧ θS≢absent S∈canθ-r k k∈canθ'-E⟦nothin⟧
  rewrite sym (unplug r≐E⟦emitS⟧)
  with Env.sig-stats {S} θ S∈ | inspect (Env.sig-stats {S} θ) S∈
... | Signal.present | [ θS≡present ]
  rewrite (sym θS≡present) | sym (SigMap.getput-m S (Env.sig θ) S∈)
  = canθₖ-subset-lemma (Env.sig θ) 0 (E ⟦ nothin ⟧e) (E ⟦ emit S ⟧e) θ'
      (λ θ* S* → canₛ-emit-lemma S θ* E S*)
      (λ θ* S* → canₖ-term-nothin-lemma θ* E tnothin (temit S) S*)
      k k∈canθ'-E⟦nothin⟧
... | Signal.absent  | [ θS≡absent  ] = ⊥-elim (θS≢absent refl)
... | Signal.unknown | [ θS≡unknown ] =
  
  canθₖ-emit-lemma (Env.sig θ) 0 (E ⟦ emit S ⟧e) θ' (Signal.unwrap S) S∈
    S∈canθ-r θS≡unknown k
    (canθₖ-subset-lemma (Env.sig (Env.set-sig {S} θ S∈ Signal.present)) 0
      (E ⟦ nothin ⟧e) (E ⟦ emit S ⟧e) θ'
      (λ θ* S* → canₛ-emit-lemma S θ* E S*)
      (λ θ* S* → canₖ-term-nothin-lemma θ* E tnothin (temit S) S*)
      k
      k∈canθ'-E⟦nothin⟧) 




canθₛₕ-emit-lemma : ∀ sigs S'' p θ S S∈ →
  (S'' + S) ∈ Canθₛ sigs S'' p θ →
  SigMap.lookup {_} {S ₛ} sigs S∈ ≡ Signal.unknown →
  ∀ s →
    s ∈ Canθₛₕ (SigMap.update sigs (S ₛ) Signal.present) S'' p θ →
    s ∈ Canθₛₕ sigs S'' p θ
canθₛₕ-emit-lemma [] S'' p θ S () S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
canθₛₕ-emit-lemma (nothing ∷ sigs) S'' p θ zero S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p =
  ⊥-elim (SigM.0∈S S∈)
canθₛₕ-emit-lemma (nothing ∷ sigs) S'' p θ (suc S) S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛₕ-emit-lemma sigs (suc S'') p θ S (SigM.n∈S {S} {nothing} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
canθₛₕ-emit-lemma (just Signal.present ∷ sigs) S'' p θ 0 S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
  with sigs-S≡unknown
... | ()
canθₛₕ-emit-lemma (just Signal.absent ∷ sigs) S'' p θ 0 S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
  with sigs-S≡unknown
... | ()
canθₛₕ-emit-lemma (just Signal.unknown ∷ sigs) S'' p θ 0 S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
... | no  S''∉canθ-sigs-θ←[S''] rewrite +-comm S'' 0
  = ⊥-elim
      (S''∉canθ-sigs-θ←[S'']
        (canθₛ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.absent
           S'' S''+S∈canθ-sigs-p-θ))
... | yes S''∈canθ-sigs-θ↽[S''] =
  canθₛₕ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.present
    s s∈canθ-θ'-p
canθₛₕ-emit-lemma (just Signal.present ∷ sigs) S'' p θ (suc S) S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛₕ-emit-lemma sigs (suc S'') p (θ ← [S]-env-present (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.present} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
canθₛₕ-emit-lemma (just Signal.absent ∷ sigs) S'' p θ (suc S) S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛₕ-emit-lemma sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.absent} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
canθₛₕ-emit-lemma (just Signal.unknown ∷ sigs) S'' p θ (suc S) S∈
  S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ (SigMap.update sigs (S ₛ) Signal.present) (suc S'') p
                       (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sigs-p-θ←[S''] | yes S''∈canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛₕ-emit-lemma sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
... | no  S''∉canθ-sigs-p-θ←[S''] | no  S''∉canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛₕ-emit-lemma sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown s s∈canθ-θ'-p
... | no  S''∉canθ-sigs-p-θ←[S''] | yes S''∈canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  = ⊥-elim
      (S''∉canθ-sigs-p-θ←[S'']
        (canθₛ-emit-lemma sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S
          (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
          (canθₛ-add-sig-monotonic sigs (suc S'') p θ (S'' ₛ) Signal.absent
             (suc (S'' + S)) S''+S∈canθ-sigs-p-θ)
          sigs-S≡unknown S'' S''∈canθ-θ'-p-θ←[S'']))
... | yes S''∈canθ-sigs-p-θ←[S''] | no  S''∉canθ-θ'-p-θ←[S'']
  rewrite +-comm S'' (suc S) | +-comm S S''
  = canθₛₕ-emit-lemma sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S
      (SigM.n∈S {S} {just Signal.unknown} {sigs} S∈)
      S''+S∈canθ-sigs-p-θ sigs-S≡unknown s
      (canθₛₕ-add-sig-monotonic
         (SigM.m-insert (just Signal.present) S sigs) (suc S'') p θ (S'' ₛ)
         Signal.absent s s∈canθ-θ'-p)


canθₛₕ-emit : ∀ {S r E} θ S∈ θ' →
  r ≐ E ⟦ emit S ⟧e →
  ¬ (Env.sig-stats {S} θ S∈ ≡ Signal.absent) →
  Signal.unwrap S ∈ Canθₛ (Env.sig θ) 0 r θ' →
  ∀ s →
    SharedVar.unwrap s ∈ Canθₛₕ (Env.sig (Env.set-sig {S} θ S∈ Signal.present)) 0
                           (E ⟦ nothin ⟧e) θ' →
    SharedVar.unwrap s ∈ Canθₛₕ (Env.sig θ) 0
                           r θ'
canθₛₕ-emit {S} {r} {E} θ S∈ θ' r≐E⟦emitS⟧ θS≢absent S∈canθ-r s s∈canθ'-E⟦nothin⟧
  rewrite sym (unplug r≐E⟦emitS⟧)
  with Env.sig-stats {S} θ S∈ | inspect (Env.sig-stats {S} θ) S∈
... | Signal.present | [ θS≡present ]
  rewrite (sym θS≡present) | sym (SigMap.getput-m S (Env.sig θ) S∈)
  = canθₛₕ-subset-lemma (Env.sig θ) 0 (E ⟦ nothin ⟧e) (E ⟦ emit S ⟧e) θ'
      (λ θ* S* → canₛ-emit-lemma S θ* E S*)
      (λ θ* s* → canₛₕ-emit-lemma S θ* E s*)
      (SharedVar.unwrap s) s∈canθ'-E⟦nothin⟧
... | Signal.absent  | [ θS≡absent  ] = ⊥-elim (θS≢absent refl)
... | Signal.unknown | [ θS≡unknown ] =
  canθₛₕ-emit-lemma (Env.sig θ) 0 (E ⟦ emit S ⟧e) θ' (Signal.unwrap S) S∈
    S∈canθ-r θS≡unknown (SharedVar.unwrap s)
    (canθₛₕ-subset-lemma (Env.sig (Env.set-sig {S} θ S∈ Signal.present)) 0
      (E ⟦ nothin ⟧e) (E ⟦ emit S ⟧e) θ'
      (λ θ* S* → canₛ-emit-lemma S θ* E S*)
      (λ θ* s* → canₛₕ-emit-lemma S θ* E s*)
      (SharedVar.unwrap s) s∈canθ'-E⟦nothin⟧)


canₖ-raise-lemma : ∀ {any/shr any/var r p} θ E →
  term-raise any/shr any/var r p →
    Canₖ (E ⟦ r ⟧e) θ ≡
    Canₖ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ
canₖ-raise-lemma {any/shr} {any/var} {r} {p} θ [] (tshared n s e .p)
  rewrite can-shr-var-irr p θ (θ ← Θ SigMap.empty any/shr any/var)
            (SigMap.union-comm {_} SigMap.empty (Env.sig θ) (λ _ ()))
        | set-subtract-[] (Canₛ p (θ ← Θ SigMap.empty any/shr any/var))
  = refl
canₖ-raise-lemma {any/shr} {any/var} {r} {p} θ [] (tvar n x e .p)
  rewrite can-shr-var-irr p θ (θ ← Θ SigMap.empty any/shr any/var)
            (SigMap.union-comm {_} SigMap.empty (Env.sig θ) (λ _ ()))
        | set-subtract-[] (Canₛ p (θ ← Θ SigMap.empty any/shr any/var))
  = refl
canₖ-raise-lemma θ (epar₁ q ∷ E) tr
  rewrite canₖ-raise-lemma θ E tr
  = refl
canₖ-raise-lemma θ (epar₂ p ∷ E) tr
  rewrite canₖ-raise-lemma θ E tr
  = refl
canₖ-raise-lemma {any/shr} {any/var} {r} {p} θ (eloopˢ q ∷ E) tr = canₖ-raise-lemma θ E tr
canₖ-raise-lemma {any/shr} {any/var} {r} {p} θ (eseq q ∷ E) tr
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ)
... | no  nothin∉can-E⟦r⟧ | no  nothin∉can-E⟦ρΘp⟧ =
  canₖ-raise-lemma θ E tr
... | yes nothin∈can-E⟦r⟧ | no  nothin∉can-E⟦ρΘp⟧
  rewrite canₖ-raise-lemma {any/shr} {any/var} θ E tr
  = ⊥-elim (nothin∉can-E⟦ρΘp⟧ nothin∈can-E⟦r⟧)
... | no  nothin∉can-E⟦r⟧ | yes nothin∈can-E⟦ρΘp⟧
  rewrite canₖ-raise-lemma {any/shr} {any/var} θ E tr
  = ⊥-elim (nothin∉can-E⟦r⟧ nothin∈can-E⟦ρΘp⟧)
... | yes nothin∈can-E⟦r⟧ | yes nothin∈can-E⟦ρΘp⟧
  rewrite canₖ-raise-lemma θ E tr
  = refl
canₖ-raise-lemma θ (esuspend S ∷ E) tr =
  canₖ-raise-lemma θ E tr
canₖ-raise-lemma θ (etrap ∷ E) tr
  rewrite canₖ-raise-lemma θ E tr
  = refl

canₛ-raise-lemma : ∀ {any/shr any/var r p} θ E →
  term-raise any/shr any/var r p →
    Canₛ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ ≡
    Canₛ (E ⟦ r ⟧e) θ
canₛ-raise-lemma {any/shr} {any/var} {r} {p} θ [] (tshared n s e .p)
  rewrite set-subtract-[] (Canₛ p θ) = refl
canₛ-raise-lemma {any/shr} {any/var} {r} {p} θ [] (tvar n x e .p)
  rewrite set-subtract-[] (Canₛ p θ) = refl
canₛ-raise-lemma {any/shr} {any/var} {r} {p} θ (epar₁ q ∷ E) tr
  rewrite canₛ-raise-lemma {any/shr} {any/var} {r} {p} θ E tr = refl
canₛ-raise-lemma θ (epar₂ p ∷ E) tr
  rewrite canₛ-raise-lemma θ E tr = refl
canₛ-raise-lemma {any/shr} {any/var} {r} {p} θ (eloopˢ q ∷ E) tr = canₛ-raise-lemma θ E tr
canₛ-raise-lemma {any/shr} {any/var} {r} {p} θ (eseq q ∷ E) tr
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ)
... | no  nothin∉can-E⟦r⟧ | no  nothin∉can-E⟦ρΘp⟧ = canₛ-raise-lemma θ E tr
... | yes nothin∈can-E⟦r⟧ | no  nothin∉can-E⟦ρΘp⟧
  rewrite canₖ-raise-lemma {any/shr} {any/var} θ E tr
  = ⊥-elim (nothin∉can-E⟦ρΘp⟧ nothin∈can-E⟦r⟧)
... | no  nothin∉can-E⟦r⟧ | yes nothin∈can-E⟦ρΘp⟧
  rewrite canₖ-raise-lemma {any/shr} {any/var} θ E tr
  = ⊥-elim (nothin∉can-E⟦r⟧ nothin∈can-E⟦ρΘp⟧)
... | yes nothin∈can-E⟦r⟧ | yes nothin∈can-E⟦ρΘp⟧
  rewrite canₛ-raise-lemma θ E tr = refl
canₛ-raise-lemma θ (esuspend S' ∷ E) tr = canₛ-raise-lemma θ E tr
canₛ-raise-lemma θ (etrap ∷ E) tr = canₛ-raise-lemma θ E tr


canθₛ-raise-lemma : ∀ {any/shr any/var r p} sigs S' θ E →
  term-raise any/shr any/var r p →
    Canθₛ sigs S' (E ⟦ r ⟧e) θ ≡
    Canθₛ sigs S' (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ
canθₛ-raise-lemma [] S' θ E tr =  sym (canₛ-raise-lemma θ E tr) 
canθₛ-raise-lemma (nothing ∷ sigs) S' = canθₛ-raise-lemma sigs (suc S')
canθₛ-raise-lemma (just Signal.present ∷ sigs) S' θ = canθₛ-raise-lemma sigs (suc S') (θ ← _)
canθₛ-raise-lemma (just Signal.absent ∷ sigs) S' θ = canθₛ-raise-lemma sigs (suc S') (θ ← _)
canθₛ-raise-lemma {any/shr} {any/var} {r} {p} (just Signal.unknown ∷ sigs) S' θ E tr
  with any (_≟_ S') (Canθₛ sigs (suc S') (E ⟦ r ⟧e) (θ ← ([S]-env (S' ₛ))))
     | any (_≟_ S') (Canθₛ sigs (suc S') (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) (θ ← ([S]-env (S' ₛ))))
... | yes S'∈CanE⟦r⟧ | yes S'∈CanE⟦ρ⟧ = canθₛ-raise-lemma sigs (suc S') (θ ← _) E tr
... | no S'∉CanE⟦r⟧  | no  S'∉CanE⟦ρ⟧ = canθₛ-raise-lemma sigs (suc S') (θ ← _) E tr
... | yes S'∈CanE⟦r⟧ | no  S'∉CanE⟦ρ⟧
  rewrite (canθₛ-raise-lemma sigs (suc S') (θ ← ([S]-env (S' ₛ))) E tr)
  = ⊥-elim (S'∉CanE⟦ρ⟧ S'∈CanE⟦r⟧)
canθₛ-raise-lemma {any/shr} {any/var} {r} {p} (just Signal.unknown ∷ sigs) S' θ E tr | no S'∉CanE⟦r⟧  | yes S'∈CanE⟦ρ⟧
  rewrite (canθₛ-raise-lemma sigs (suc S') (θ ← ([S]-env (S' ₛ))) E tr)
  = ⊥-elim (S'∉CanE⟦r⟧ S'∈CanE⟦ρ⟧)

canθₖ-raise-lemma : ∀ {any/shr any/var r p} sigs S' θ E →
  term-raise any/shr any/var r p →
    Canθₖ sigs S' (E ⟦ r ⟧e) θ ≡
    Canθₖ sigs S' (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ
canθₖ-raise-lemma [] S' = canₖ-raise-lemma
canθₖ-raise-lemma (nothing ∷ sigs) S' = canθₖ-raise-lemma sigs (suc S')
canθₖ-raise-lemma (just Signal.present ∷ sigs) S' θ = canθₖ-raise-lemma sigs (suc S') (θ ← _)
canθₖ-raise-lemma (just Signal.absent ∷ sigs) S' θ = canθₖ-raise-lemma sigs (suc S') (θ ← _)
canθₖ-raise-lemma {any/shr} {any/var} {r} {p} (just Signal.unknown ∷ sigs) S' θ E tr
  with any (_≟_ S') (Canθₛ sigs (suc S') (E ⟦ r ⟧e) (θ ← ([S]-env (S' ₛ))))
     | any (_≟_ S') (Canθₛ sigs (suc S') (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) (θ ← ([S]-env (S' ₛ))))
... | yes S'∈CanE⟦r⟧ | yes S'∈CanE⟦ρ⟧ = canθₖ-raise-lemma sigs (suc S') (θ ← _) E tr
... | no S'∉CanE⟦r⟧  | no  S'∉CanE⟦ρ⟧ = canθₖ-raise-lemma sigs (suc S') (θ ← _) E tr
... | yes S'∈CanE⟦r⟧ | no  S'∉CanE⟦ρ⟧
  rewrite (canθₛ-raise-lemma sigs (suc S') (θ ← ([S]-env (S' ₛ))) E tr)
  = ⊥-elim (S'∉CanE⟦ρ⟧ S'∈CanE⟦r⟧)
canθₖ-raise-lemma {any/shr} {any/var} {r} {p} (just Signal.unknown ∷ sigs) S' θ E tr | no S'∉CanE⟦r⟧  | yes S'∈CanE⟦ρ⟧
  rewrite (canθₛ-raise-lemma sigs (suc S') (θ ← ([S]-env (S' ₛ))) E tr)
  = ⊥-elim (S'∉CanE⟦r⟧ S'∈CanE⟦ρ⟧)


canₛ-raise : ∀ {E any/shr any/var r r' p} θ →
  term-raise any/shr any/var r' p →
  r ≐ E ⟦ r' ⟧e →
  ∀ S →
    Signal.unwrap S ∈ Canₛ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ →
    Signal.unwrap S ∈ Canₛ r θ
canₛ-raise {E} θ tr r≐E⟦shared⟧ S S∈
  rewrite sym (unplug r≐E⟦shared⟧)
        | canₛ-raise-lemma θ E tr 
  = S∈


canₛₕ-raise-lemma : ∀ {any/shr any/var r p} θ E →
  term-raise any/shr any/var r p →
  ∀ s'' →
    s'' ∈ Canₛₕ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ →
    s'' ∈ Canₛₕ (E ⟦ r ⟧e) θ
canₛₕ-raise-lemma {any/shr} {any/var} {r} {p} θ [] (tshared n s e .p) s'' s''∈can-ρΘp-θ
  rewrite ShrMap.keys-1map s (SharedVar.old ,′ n)
        | set-subtract-[a]≡set-remove (Canₛₕ p θ) (SharedVar.unwrap s)
  = s''∈can-ρΘp-θ
canₛₕ-raise-lemma {any/shr} {any/var} {r} {p} θ [] (tvar n x e .p) s'' s''∈can-ρΘp-θ
  rewrite set-subtract-[] (Canₛₕ p θ)
  = s''∈can-ρΘp-θ
canₛₕ-raise-lemma {any/shr} {any/var} {r} {p} θ (epar₁ q ∷ E) tr s'' s''∈can-E⟦ρΘp⟧∥q-θ
  with ++⁻ (Canₛₕ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p  ⟧e) θ) s''∈can-E⟦ρΘp⟧∥q-θ
... | inj₁ s''∈can-E⟦ρΘp⟧-θ = ++ˡ (canₛₕ-raise-lemma θ E tr s'' s''∈can-E⟦ρΘp⟧-θ)
... | inj₂ s''∈can-q-θ = ++ʳ (Canₛₕ (E ⟦ r ⟧e) θ) s''∈can-q-θ
canₛₕ-raise-lemma θ (epar₂ p ∷ E) tr s'' s''∈can-p∥E⟦ρΘp⟧-θ
  with ++⁻ (Canₛₕ p θ) s''∈can-p∥E⟦ρΘp⟧-θ
... | inj₁ s''∈can-p-θ = ++ˡ s''∈can-p-θ
... | inj₂ s''∈can-E⟦ρΘp⟧-θ = ++ʳ (Canₛₕ p θ) (canₛₕ-raise-lemma θ E tr s'' s''∈can-E⟦ρΘp⟧-θ)
canₛₕ-raise-lemma {any/shr} {any/var} {r} {p} θ (eloopˢ q ∷ E) tr s'' s''∈can-E⟦ρΘp⟧>>q-θ = canₛₕ-raise-lemma θ E tr s'' s''∈can-E⟦ρΘp⟧>>q-θ
canₛₕ-raise-lemma {any/shr} {any/var} {r} {p} θ (eseq q ∷ E) tr s'' s''∈can-E⟦ρΘp⟧>>q-θ
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ)
... | no  nothin∉can-E⟦r⟧ | no  nothin∉can-E⟦ρΘp⟧ =
  canₛₕ-raise-lemma θ E tr s'' s''∈can-E⟦ρΘp⟧>>q-θ
... | yes nothin∈can-E⟦r⟧ | no  nothin∉can-E⟦ρΘp⟧
  rewrite canₖ-raise-lemma {any/shr} {any/var} θ E tr
  = ⊥-elim (nothin∉can-E⟦ρΘp⟧ nothin∈can-E⟦r⟧)
... | no  nothin∉can-E⟦r⟧ | yes nothin∈can-E⟦ρΘp⟧
  rewrite canₖ-raise-lemma {any/shr} {any/var} θ E tr
  = ⊥-elim (nothin∉can-E⟦r⟧ nothin∈can-E⟦ρΘp⟧)
... | yes nothin∈can-E⟦r⟧ | yes nothin∈can-E⟦ρΘp⟧
  with ++⁻ (Canₛₕ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ) s''∈can-E⟦ρΘp⟧>>q-θ
... | inj₁ s''∈can-E⟦ρΘp⟧ = ++ˡ (canₛₕ-raise-lemma θ E tr s'' s''∈can-E⟦ρΘp⟧)
... | inj₂ s''∈can-q = ++ʳ (Canₛₕ (E ⟦ r ⟧e) θ) s''∈can-q
canₛₕ-raise-lemma θ (esuspend S' ∷ E) tr s'' s''∈can-E⟦ρΘp⟧-θ =
  canₛₕ-raise-lemma θ E tr s'' s''∈can-E⟦ρΘp⟧-θ
canₛₕ-raise-lemma θ (etrap ∷ E) tr s'' s''∈can-E⟦ρΘp⟧-θ =
  canₛₕ-raise-lemma θ E tr s'' s''∈can-E⟦ρΘp⟧-θ


canₛₕ-raise : ∀ {E any/shr any/var r r' p} θ →
  term-raise any/shr any/var r' p →
  r ≐ E ⟦ r' ⟧e →
  ∀ s'' →
    SharedVar.unwrap s'' ∈ Canₛₕ (E ⟦ ρ (Θ SigMap.empty any/shr any/var) · p ⟧e) θ →
    SharedVar.unwrap s'' ∈ Canₛₕ r θ
canₛₕ-raise {E} θ tr r≐E⟦shared⟧ s'' s''∈
  rewrite sym (unplug r≐E⟦shared⟧)
  = canₛₕ-raise-lemma θ E tr (SharedVar.unwrap s'') s''∈


canₛ-term-nothin-lemma : ∀ {r} θ E →
  term-nothin r →
  ∀ S →
    S ∈ Canₛ (E ⟦ nothin ⟧e) θ →
    S ∈ Canₛ (E ⟦ r ⟧e) θ
canₛ-term-nothin-lemma θ [] tn S ()
canₛ-term-nothin-lemma {r} θ (epar₁ q ∷ E) tn S S∈can-E⟦nothin⟧∥q
  with ++⁻ (Canₛ (E ⟦ nothin ⟧e) θ) S∈can-E⟦nothin⟧∥q
... | inj₁ S∈can-E⟦nothin⟧ = ++ˡ (canₛ-term-nothin-lemma θ E tn S S∈can-E⟦nothin⟧)
... | inj₂ S∈can-q = ++ʳ (Canₛ (E ⟦ r ⟧e) θ) S∈can-q
canₛ-term-nothin-lemma θ (epar₂ p ∷ E) tn S S∈can-p∥E⟦nothin⟧
  with ++⁻ (Canₛ p θ) S∈can-p∥E⟦nothin⟧
... | inj₁ S∈can-q = ++ˡ S∈can-q
... | inj₂ S∈can-E⟦nothin⟧ =
  ++ʳ (Canₛ p θ) (canₛ-term-nothin-lemma θ E tn S S∈can-E⟦nothin⟧)
canₛ-term-nothin-lemma {r} θ (eloopˢ q ∷ E) tn S S∈can-E⟦nothin⟧>>q = canₛ-term-nothin-lemma θ E tn S S∈can-E⟦nothin⟧>>q
canₛ-term-nothin-lemma {r} θ (eseq q ∷ E) tn S S∈can-E⟦nothin⟧>>q
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ nothin ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r ⟧e) θ)
... | yes nothin∈can-E⟦nothin⟧ | no  nothin∉can-E⟦r⟧ =
  ⊥-elim
    (nothin∉can-E⟦r⟧
      (canₖ-term-nothin-lemma θ E tnothin tn Code.nothin
        nothin∈can-E⟦nothin⟧))
... | no  nothin∉can-E⟦nothin⟧ | yes nothin∈can-E⟦r⟧ =
  ⊥-elim
    (nothin∉can-E⟦nothin⟧
      (canₖ-term-nothin-lemma θ E tn tnothin Code.nothin
        nothin∈can-E⟦r⟧))
... | no  nothin∉can-E⟦nothin⟧ | no  nothin∉can-E⟦s'⇐e⟧ =
  canₛ-term-nothin-lemma θ E tn S S∈can-E⟦nothin⟧>>q
... | yes nothin∈can-E⟦nothin⟧ | yes nothin∈can-E⟦s'⇐e⟧
  with ++⁻ (Canₛ (E ⟦ nothin ⟧e) θ)  S∈can-E⟦nothin⟧>>q
... | inj₁ S∈can-E⟦nothin⟧ = ++ˡ (canₛ-term-nothin-lemma θ E tn S S∈can-E⟦nothin⟧)
... | inj₂ S∈can-q = ++ʳ (Canₛ (E ⟦ r ⟧e) θ) S∈can-q
canₛ-term-nothin-lemma θ (esuspend S' ∷ E) tn S S∈can-E⟦nothin⟧ =
 canₛ-term-nothin-lemma θ E tn S S∈can-E⟦nothin⟧
canₛ-term-nothin-lemma θ (etrap ∷ E) tn S S∈can-E⟦nothin⟧ =
  canₛ-term-nothin-lemma θ E tn S S∈can-E⟦nothin⟧


canₛ-term-nothin : ∀ {r' E r} θ θ' →
  Env.sig θ ≡ Env.sig θ' →
  term-nothin r' →
  r ≐ E ⟦ r' ⟧e →
  ∀ S →
    Signal.unwrap S ∈ Canₛ (E ⟦ nothin ⟧e) θ' →
    Signal.unwrap S ∈ Canₛ r θ
canₛ-term-nothin {r'} {E} {r} θ θ' θₛ≡θ'ₛ tn r≐E⟦r'⟧ S S∈can-E⟦nothin⟧-θ'
  rewrite can-shr-var-irr (E ⟦ nothin ⟧e) θ' θ (sym θₛ≡θ'ₛ)
        | sym (unplug r≐E⟦r'⟧)
  = canₛ-term-nothin-lemma θ E tn (Signal.unwrap S) S∈can-E⟦nothin⟧-θ'

canₛₕ-term-nothin-lemma : ∀ {r} θ E →
  term-nothin r →
  ∀ S →
    S ∈ Canₛₕ (E ⟦ nothin ⟧e) θ →
    S ∈ Canₛₕ (E ⟦ r ⟧e) θ
canₛₕ-term-nothin-lemma θ [] tn S ()
canₛₕ-term-nothin-lemma {r} θ (epar₁ q ∷ E) tn s'' s''∈can-E⟦nothin⟧∥q
  with ++⁻ (Canₛₕ (E ⟦ nothin ⟧e) θ) s''∈can-E⟦nothin⟧∥q
... | inj₁ s''∈can-E⟦nothin⟧ = ++ˡ (canₛₕ-term-nothin-lemma θ E tn s'' s''∈can-E⟦nothin⟧)
... | inj₂ s''∈can-q = ++ʳ (Canₛₕ (E ⟦ r ⟧e) θ) s''∈can-q
canₛₕ-term-nothin-lemma θ (epar₂ p ∷ E) tn s'' s''∈can-p∥E⟦nothin⟧
  with ++⁻ (Canₛₕ p θ) s''∈can-p∥E⟦nothin⟧
... | inj₁ s''∈can-q = ++ˡ s''∈can-q
... | inj₂ s''∈can-E⟦nothin⟧ =
  ++ʳ (Canₛₕ p θ) (canₛₕ-term-nothin-lemma θ E tn s'' s''∈can-E⟦nothin⟧)
canₛₕ-term-nothin-lemma {r} θ (eloopˢ q ∷ E) tn s'' s''∈can-E⟦nothin⟧>>q = canₛₕ-term-nothin-lemma θ E tn s'' s''∈can-E⟦nothin⟧>>q
canₛₕ-term-nothin-lemma {r} θ (eseq q ∷ E) tn s'' s''∈can-E⟦nothin⟧>>q
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ nothin ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r ⟧e) θ)
... | yes nothin∈can-E⟦nothin⟧ | no  nothin∉can-E⟦r⟧ =
  ⊥-elim
    (nothin∉can-E⟦r⟧
      (canₖ-term-nothin-lemma θ E tnothin tn Code.nothin
        nothin∈can-E⟦nothin⟧))
... | no  nothin∉can-E⟦nothin⟧ | yes nothin∈can-E⟦r⟧ =
  ⊥-elim
    (nothin∉can-E⟦nothin⟧
      (canₖ-term-nothin-lemma θ E tn tnothin Code.nothin
        nothin∈can-E⟦r⟧))
... | no  nothin∉can-E⟦nothin⟧ | no  nothin∉can-E⟦s'⇐e⟧ =
  canₛₕ-term-nothin-lemma {r} θ E tn s'' s''∈can-E⟦nothin⟧>>q
... | yes nothin∈can-E⟦nothin⟧ | yes nothin∈can-E⟦s'⇐e⟧
  with ++⁻ (Canₛₕ (E ⟦ nothin ⟧e) θ) s''∈can-E⟦nothin⟧>>q
... | inj₁ s''∈can-E⟦nothin⟧ = ++ˡ (canₛₕ-term-nothin-lemma θ E tn s'' s''∈can-E⟦nothin⟧)
... | inj₂ s''∈can-q = ++ʳ (Canₛₕ (E ⟦ r ⟧e) θ) s''∈can-q
canₛₕ-term-nothin-lemma θ (esuspend S' ∷ E) tn s'' s''∈can-E⟦nothin⟧ =
 canₛₕ-term-nothin-lemma θ E tn s'' s''∈can-E⟦nothin⟧
canₛₕ-term-nothin-lemma θ (etrap ∷ E) tn s'' s''∈can-E⟦nothin⟧ =
  canₛₕ-term-nothin-lemma θ E tn s'' s''∈can-E⟦nothin⟧

canₛₕ-term-nothin : ∀ {r' E r} θ θ' →
  Env.sig θ ≡ Env.sig θ' →
  term-nothin r' →
  r ≐ E ⟦ r' ⟧e →
  ∀ s'' →
    SharedVar.unwrap s'' ∈ Canₛₕ (E ⟦ nothin ⟧e) θ' →
    SharedVar.unwrap s'' ∈ Canₛₕ r θ
canₛₕ-term-nothin {r'} {E} {r} θ θ' θₛ≡θ'ₛ tn r≐E⟦r'⟧ s'' s''∈can-E⟦nothin⟧-θ'
  rewrite can-shr-var-irr (E ⟦ nothin ⟧e) θ' θ (sym θₛ≡θ'ₛ)
        | sym (unplug r≐E⟦r'⟧)
  = canₛₕ-term-nothin-lemma θ E tn (SharedVar.unwrap s'') s''∈can-E⟦nothin⟧-θ'


canₖ-if-true-lemma : ∀ x p q θ E →
  ∀ k →
    k ∈ Canₖ (E ⟦ p ⟧e) θ →
    k ∈ Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canₖ-if-true-lemma x p q θ [] k k∈can-E⟦p⟧ = ++ˡ k∈can-E⟦p⟧
canₖ-if-true-lemma x p q θ (epar₁ q' ∷ E) k k∈can-E⟦p⟧∥q' =
  map-mono² {xs = Canₖ (E ⟦ p ⟧e) θ} Code._⊔_ (canₖ-if-true-lemma x p q θ E) (λ _ → id) k k∈can-E⟦p⟧∥q'
canₖ-if-true-lemma x p q θ (epar₂ p' ∷ E) k k∈can-p'∥E⟦p⟧ =
  map-mono² {xs = Canₖ p' θ} Code._⊔_ (λ _ → id) (canₖ-if-true-lemma x p q θ E) k k∈can-p'∥E⟦p⟧
canₖ-if-true-lemma x p q θ (eloopˢ q' ∷ E) k k∈can-E⟦p⟧>>q' = canₖ-if-true-lemma x p q θ E k k∈can-E⟦p⟧>>q'
canₖ-if-true-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦p⟧>>q'
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ p ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ)
canₖ-if-true-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦p⟧>>q'
  | yes nothin∈can-E⟦p⟧ | no  nothin∉can-E⟦if⟧ =
  ⊥-elim (nothin∉can-E⟦if⟧ (canₖ-if-true-lemma x p q θ E Code.nothin nothin∈can-E⟦p⟧))
canₖ-if-true-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦p⟧>>q'
  | no  nothin∉can-E⟦p⟧ | no  nothin∉can-E⟦if⟧ =
  canₖ-if-true-lemma x p q θ E k k∈can-E⟦p⟧>>q'
canₖ-if-true-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦p⟧>>q'
  | no  nothin∉can-E⟦p⟧ | yes nothin∈can-E⟦if⟧
  with Code.nothin Code.≟ k
... | yes refl = ⊥-elim (nothin∉can-E⟦p⟧ k∈can-E⟦p⟧>>q')
... | no nothin≢k =
  ++ˡ
    (CodeSet.set-remove-not-removed nothin≢k
      (canₖ-if-true-lemma x p q θ E k
        k∈can-E⟦p⟧>>q'))
canₖ-if-true-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦p⟧>>q'
  | yes nothin∈can-E⟦p⟧ | yes nothin∈can-E⟦if⟧
  with ++⁻ (CodeSet.set-remove (Canₖ (E ⟦ p ⟧e) θ) Code.nothin) k∈can-E⟦p⟧>>q'
... | inj₂ k∈can-q' = ++ʳ (CodeSet.set-remove (Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) Code.nothin) k∈can-q'
... | inj₁ k∈can-E⟦p⟧-nothin
  with Code.nothin Code.≟ k
... | yes refl = ⊥-elim (CodeSet.set-remove-removed {Code.nothin} {Canₖ (E ⟦ p ⟧e) θ} k∈can-E⟦p⟧-nothin)
... | no nothin≢k =
  ++ˡ
    (CodeSet.set-remove-not-removed nothin≢k
      (canₖ-if-true-lemma x p q θ E k
        (CodeSet.set-remove-mono-∈ Code.nothin
          k∈can-E⟦p⟧-nothin)))
canₖ-if-true-lemma x p q θ (esuspend S' ∷ E) k k∈can-E⟦p⟧ =
  canₖ-if-true-lemma x p q θ E k k∈can-E⟦p⟧
canₖ-if-true-lemma x p q θ (etrap ∷ E) k k∈can-E⟦p⟧ =
  map-mono Code.↓* (canₖ-if-true-lemma x p q θ E) k k∈can-E⟦p⟧


canₖ-if-false-lemma : ∀ x p q θ E →
  ∀ k →
    k ∈ Canₖ (E ⟦ q ⟧e) θ →
    k ∈ Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canₖ-if-false-lemma x p q θ [] k k∈can-E⟦q⟧ = ++ʳ (Canₖ p θ) k∈can-E⟦q⟧
canₖ-if-false-lemma x p q θ (epar₁ q' ∷ E) k k∈can-E⟦q⟧∥q' =
  map-mono² {xs = Canₖ (E ⟦ q ⟧e) θ} Code._⊔_ (canₖ-if-false-lemma x p q θ E) (λ _ → id) k k∈can-E⟦q⟧∥q'
canₖ-if-false-lemma x p q θ (epar₂ p' ∷ E) k k∈can-p'∥E⟦q⟧ =
  map-mono² {xs = Canₖ p' θ} Code._⊔_ (λ _ → id) (canₖ-if-false-lemma x p q θ E) k k∈can-p'∥E⟦q⟧
canₖ-if-false-lemma x p q θ (eloopˢ q' ∷ E) k k∈can-E⟦q⟧>>q' = canₖ-if-false-lemma x p q θ E k k∈can-E⟦q⟧>>q'
canₖ-if-false-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦q⟧>>q'
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ q ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ)
canₖ-if-false-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦q⟧>>q'
  | yes nothin∈can-E⟦q⟧ | no  nothin∉can-E⟦if⟧ =
  ⊥-elim (nothin∉can-E⟦if⟧ (canₖ-if-false-lemma x p q θ E Code.nothin nothin∈can-E⟦q⟧))
canₖ-if-false-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦q⟧>>q'
  | no  nothin∉can-E⟦q⟧ | no  nothin∉can-E⟦if⟧ =
  canₖ-if-false-lemma x p q θ E k k∈can-E⟦q⟧>>q'
canₖ-if-false-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦q⟧>>q'
  | no  nothin∉can-E⟦q⟧ | yes nothin∈can-E⟦if⟧
  with Code.nothin Code.≟ k
... | yes refl = ⊥-elim (nothin∉can-E⟦q⟧ k∈can-E⟦q⟧>>q')
... | no nothin≢k =
  ++ˡ
    (CodeSet.set-remove-not-removed nothin≢k
      (canₖ-if-false-lemma x p q θ E k
        k∈can-E⟦q⟧>>q'))
canₖ-if-false-lemma x p q θ (eseq q' ∷ E) k k∈can-E⟦q⟧>>q'
  | yes nothin∈can-E⟦q⟧ | yes nothin∈can-E⟦if⟧
  with ++⁻ (CodeSet.set-remove (Canₖ (E ⟦ q ⟧e) θ) Code.nothin) k∈can-E⟦q⟧>>q'
... | inj₂ k∈can-q' = ++ʳ (CodeSet.set-remove (Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) Code.nothin) k∈can-q'
... | inj₁ k∈can-E⟦q⟧-nothin
  with Code.nothin Code.≟ k
... | yes refl = ⊥-elim (CodeSet.set-remove-removed {Code.nothin} {Canₖ (E ⟦ q ⟧e) θ} k∈can-E⟦q⟧-nothin)
... | no nothin≢k =
  ++ˡ
    (CodeSet.set-remove-not-removed nothin≢k
      (canₖ-if-false-lemma x p q θ E k
        (CodeSet.set-remove-mono-∈ Code.nothin
          k∈can-E⟦q⟧-nothin)))
canₖ-if-false-lemma x p q θ (esuspend S' ∷ E) k k∈can-E⟦q⟧ =
  canₖ-if-false-lemma x p q θ E k k∈can-E⟦q⟧
canₖ-if-false-lemma x p q θ (etrap ∷ E) k k∈can-E⟦q⟧ =
  map-mono Code.↓* (canₖ-if-false-lemma x p q θ E) k k∈can-E⟦q⟧

canθₖ-if-false-lemma : ∀ sig S → ∀ x p q θ E →
  ∀ k →
    k ∈ Canθₖ sig S (E ⟦ q ⟧e) θ →
    k ∈ Canθₖ sig S (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canθₖ-if-false-lemma sig S x p q θ E =
   (canθₖ-plugE S sig E (if x ∣⇒ p ∣⇒ q) q (λ θ₁ k x₁ → ++ʳ (Canₖ p θ₁) x₁) ((λ θ₁ k x₁ → ++ʳ (Canₛ p θ₁) x₁)) θ)

canθₖ-if-true-lemma : ∀ sig S → ∀ x p q θ E →
  ∀ k →
    k ∈ Canθₖ sig S (E ⟦ p ⟧e) θ →
    k ∈ Canθₖ sig S (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canθₖ-if-true-lemma sig S x p q θ E =
   (canθₖ-plugE S sig E (if x ∣⇒ p ∣⇒ q) p (λ θ₁ k x₁ → ++ˡ x₁) ((λ θ₁ k x₁ → ++ˡ x₁)) θ)

canθₛ-if-false-lemma : ∀ sig S → ∀ x p q θ E →
  ∀ S' →
    S' ∈ Canθₛ sig S (E ⟦ q ⟧e) θ →
    S' ∈ Canθₛ sig S (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canθₛ-if-false-lemma sig S x p q θ E =
   (canθₛ-plugE S sig E (if x ∣⇒ p ∣⇒ q) q (λ θ₁ k x₁ → ++ʳ (Canₛ p θ₁) x₁) ((λ θ₁ k x₁ → ++ʳ (Canₖ p θ₁) x₁)) θ)

canθₛ-if-true-lemma : ∀ sig S → ∀ x p q θ E →
  ∀ S' →
    S' ∈ Canθₛ sig S (E ⟦ p ⟧e) θ →
    S' ∈ Canθₛ sig S (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canθₛ-if-true-lemma sig S x p q θ E =
   (canθₛ-plugE S sig E (if x ∣⇒ p ∣⇒ q) p (λ θ₁ k x₁ → ++ˡ x₁) ((λ θ₁ k x₁ → ++ˡ x₁)) θ)

canθₛₕ-if-true-lemma : ∀ sigs S → ∀ x p q θ E →
  ∀ s →
    s ∈ Canθₛₕ sigs S (E ⟦ p ⟧e) θ →
    s ∈ Canθₛₕ sigs S (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canθₛₕ-if-true-lemma sig S x p q θ E = (canθₛₕ-plugE S sig E (if x ∣⇒ p ∣⇒ q) p (λ θ₁ k x₁ → ++ˡ x₁) ((λ θ₁ k x₁ → ++ˡ x₁)) ((λ θ₁ k x₁ → ++ˡ x₁)) θ)

canθₛₕ-if-false-lemma : ∀ sigs S → ∀ x p q θ E →
  ∀ s →
    s ∈ Canθₛₕ sigs S (E ⟦ q ⟧e) θ →
    s ∈ Canθₛₕ sigs S (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canθₛₕ-if-false-lemma sig S x p q θ E
  = (canθₛₕ-plugE S sig E (if x ∣⇒ p ∣⇒ q) q (λ θ₁ k x₁ → ++ʳ (Canₛₕ p θ₁) x₁) ((λ θ₁ k x₁ → ++ʳ ((Canₖ p θ₁)) x₁)) ((λ θ₁ k x₁ → ++ʳ ((Canₛ p θ₁)) x₁)) θ)






canₛ-if-true-lemma : ∀ x p q θ E →
  ∀ S →
    S ∈ Canₛ (E ⟦ p ⟧e) θ →
    S ∈ Canₛ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canₛ-if-true-lemma x p q θ [] S S∈can-E⟦p⟧ = ++ˡ S∈can-E⟦p⟧
canₛ-if-true-lemma x p q θ (epar₁ q' ∷ E) S S∈can-E⟦p⟧∥q'
  with ++⁻ (Canₛ (E ⟦ p ⟧e) θ) S∈can-E⟦p⟧∥q'
... | inj₁ S∈can-E⟦p⟧ = ++ˡ (canₛ-if-true-lemma x p q θ E S S∈can-E⟦p⟧)
... | inj₂ S∈can-q' = ++ʳ (Canₛ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) S∈can-q'
canₛ-if-true-lemma x p q θ (epar₂ p' ∷ E) S S∈can-p'∥E⟦p⟧
  with ++⁻ (Canₛ p' θ) S∈can-p'∥E⟦p⟧
... | inj₁ S∈can-p' = ++ˡ S∈can-p'
... | inj₂ S∈can-E⟦p⟧ = ++ʳ (Canₛ p' θ) (canₛ-if-true-lemma x p q θ E S S∈can-E⟦p⟧)
canₛ-if-true-lemma x p q θ (eloopˢ q' ∷ E) S S∈can-E⟦p⟧>>q' = canₛ-if-true-lemma x p q θ E S S∈can-E⟦p⟧>>q'
canₛ-if-true-lemma x p q θ (eseq q' ∷ E) S S∈can-E⟦p⟧>>q'
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ p ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ)
... | yes nothin∈can-E⟦p⟧ | no  nothin∉can-E⟦if⟧ =
  ⊥-elim (nothin∉can-E⟦if⟧ (canₖ-if-true-lemma x p q θ E Code.nothin nothin∈can-E⟦p⟧))
... | no  nothin∉can-E⟦p⟧ | yes nothin∈can-E⟦if⟧ =
  ++ˡ (canₛ-if-true-lemma x p q θ E S S∈can-E⟦p⟧>>q')
... | no  nothin∉can-E⟦p⟧ | no  nothin∉can-E⟦if⟧ =
  canₛ-if-true-lemma x p q θ E S S∈can-E⟦p⟧>>q'
... | yes nothin∈can-E⟦p⟧ | yes nothin∈can-E⟦if⟧
  with ++⁻ (Canₛ (E ⟦ p ⟧e) θ) S∈can-E⟦p⟧>>q'
... | inj₁ S∈can-E⟦p⟧ = ++ˡ (canₛ-if-true-lemma x p q θ E S S∈can-E⟦p⟧)
... | inj₂ S∈can-q' = ++ʳ (Canₛ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) S∈can-q'
canₛ-if-true-lemma x p q θ (esuspend S' ∷ E) S S∈can-E⟦p⟧ =
  canₛ-if-true-lemma x p q θ E S S∈can-E⟦p⟧
canₛ-if-true-lemma x p q θ (etrap ∷ E) S S∈can-E⟦p⟧ =
  canₛ-if-true-lemma x p q θ E S S∈can-E⟦p⟧

canₛ-if-true : ∀ {x p q E r} θ →
  r ≐ E ⟦ if x ∣⇒ p ∣⇒ q  ⟧e →
  ∀ S →
    Signal.unwrap S ∈ Canₛ (E ⟦ p ⟧e) θ →
    Signal.unwrap S ∈ Canₛ r θ
canₛ-if-true {x} {p} {q} {E} θ r≐E⟦if⟧ S S∈can-E⟦p⟧
  rewrite sym (unplug r≐E⟦if⟧)
  = canₛ-if-true-lemma x p q θ E (Signal.unwrap S) S∈can-E⟦p⟧


canₛ-if-false-lemma : ∀ x p q θ E →
  ∀ S →
    S ∈ Canₛ (E ⟦ q ⟧e) θ →
    S ∈ Canₛ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canₛ-if-false-lemma x p q θ [] S S∈can-E⟦q⟧ = ++ʳ (Canₛ p θ) S∈can-E⟦q⟧
canₛ-if-false-lemma x p q θ (epar₁ q' ∷ E) S S∈can-E⟦q⟧∥q'
  with ++⁻ (Canₛ (E ⟦ q ⟧e) θ) S∈can-E⟦q⟧∥q'
... | inj₁ S∈can-E⟦q⟧ = ++ˡ (canₛ-if-false-lemma x p q θ E S S∈can-E⟦q⟧)
... | inj₂ S∈can-q' = ++ʳ (Canₛ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) S∈can-q'
canₛ-if-false-lemma x p q θ (epar₂ p' ∷ E) S S∈can-p'∥E⟦q⟧
  with ++⁻ (Canₛ p' θ) S∈can-p'∥E⟦q⟧
... | inj₁ S∈can-p' = ++ˡ S∈can-p'
... | inj₂ S∈can-E⟦q⟧ = ++ʳ (Canₛ p' θ) (canₛ-if-false-lemma x p q θ E S S∈can-E⟦q⟧)
canₛ-if-false-lemma x p q θ (eloopˢ q' ∷ E) S S∈can-E⟦q⟧>>q' = canₛ-if-false-lemma x p q θ E S S∈can-E⟦q⟧>>q'
canₛ-if-false-lemma x p q θ (eseq q' ∷ E) S S∈can-E⟦q⟧>>q'
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ q ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ)
... | yes nothin∈can-E⟦q⟧ | no  nothin∉can-E⟦if⟧ =
  ⊥-elim (nothin∉can-E⟦if⟧ (canₖ-if-false-lemma x p q θ E Code.nothin nothin∈can-E⟦q⟧))
... | no  nothin∉can-E⟦q⟧ | yes nothin∈can-E⟦if⟧ =
  ++ˡ (canₛ-if-false-lemma x p q θ E S S∈can-E⟦q⟧>>q')
... | no  nothin∉can-E⟦q⟧ | no  nothin∉can-E⟦if⟧ =
  canₛ-if-false-lemma x p q θ E S S∈can-E⟦q⟧>>q'
... | yes nothin∈can-E⟦q⟧ | yes nothin∈can-E⟦if⟧
  with ++⁻ (Canₛ (E ⟦ q ⟧e) θ) S∈can-E⟦q⟧>>q'
... | inj₁ S∈can-E⟦q⟧ = ++ˡ (canₛ-if-false-lemma x p q θ E S S∈can-E⟦q⟧)
... | inj₂ S∈can-q' = ++ʳ (Canₛ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) S∈can-q'
canₛ-if-false-lemma x p q θ (esuspend S' ∷ E) S S∈can-E⟦q⟧ =
  canₛ-if-false-lemma x p q θ E S S∈can-E⟦q⟧
canₛ-if-false-lemma x p q θ (etrap ∷ E) S S∈can-E⟦q⟧ =
  canₛ-if-false-lemma x p q θ E S S∈can-E⟦q⟧

canₛ-if-false : ∀ {x p q E r} θ →
  r ≐ E ⟦ if x ∣⇒ p ∣⇒ q  ⟧e →
  ∀ S →
    Signal.unwrap S ∈ Canₛ (E ⟦ q ⟧e) θ →
    Signal.unwrap S ∈ Canₛ r θ
canₛ-if-false {x} {p} {q} {E} θ r≐E⟦if⟧ S S∈can-E⟦q⟧
  rewrite sym (unplug r≐E⟦if⟧)
  = canₛ-if-false-lemma x p q θ E (Signal.unwrap S) S∈can-E⟦q⟧


canₛₕ-if-true-lemma : ∀ x p q θ E →
  ∀ S →
    S ∈ Canₛₕ (E ⟦ p ⟧e) θ →
    S ∈ Canₛₕ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canₛₕ-if-true-lemma x p q θ [] s s∈can-E⟦p⟧ = ++ˡ s∈can-E⟦p⟧
canₛₕ-if-true-lemma x p q θ (epar₁ q' ∷ E) s s∈can-E⟦p⟧∥q'
  with ++⁻ (Canₛₕ (E ⟦ p ⟧e) θ) s∈can-E⟦p⟧∥q'
... | inj₁ s∈can-E⟦p⟧ = ++ˡ (canₛₕ-if-true-lemma x p q θ E s s∈can-E⟦p⟧)
... | inj₂ s∈can-q' = ++ʳ (Canₛₕ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) s∈can-q'
canₛₕ-if-true-lemma x p q θ (epar₂ p' ∷ E) s s∈can-p'∥E⟦p⟧
  with ++⁻ (Canₛₕ p' θ) s∈can-p'∥E⟦p⟧
... | inj₁ s∈can-p' = ++ˡ s∈can-p'
... | inj₂ s∈can-E⟦p⟧ = ++ʳ (Canₛₕ p' θ) (canₛₕ-if-true-lemma x p q θ E s s∈can-E⟦p⟧)
canₛₕ-if-true-lemma x p q θ (eloopˢ q' ∷ E) s s∈can-E⟦p⟧>>q' = canₛₕ-if-true-lemma x p q θ E s s∈can-E⟦p⟧>>q'
canₛₕ-if-true-lemma x p q θ (eseq q' ∷ E) s s∈can-E⟦p⟧>>q'
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ p ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ)
... | yes nothin∈can-E⟦p⟧ | no  nothin∉can-E⟦if⟧ =
  ⊥-elim (nothin∉can-E⟦if⟧ (canₖ-if-true-lemma x p q θ E Code.nothin nothin∈can-E⟦p⟧))
... | no  nothin∉can-E⟦p⟧ | yes nothin∈can-E⟦if⟧ =
  ++ˡ (canₛₕ-if-true-lemma x p q θ E s s∈can-E⟦p⟧>>q')
... | no  nothin∉can-E⟦p⟧ | no  nothin∉can-E⟦if⟧ =
  canₛₕ-if-true-lemma x p q θ E s s∈can-E⟦p⟧>>q'
... | yes nothin∈can-E⟦p⟧ | yes nothin∈can-E⟦if⟧
  with ++⁻ (Canₛₕ (E ⟦ p ⟧e) θ) s∈can-E⟦p⟧>>q'
... | inj₁ s∈can-E⟦p⟧ = ++ˡ (canₛₕ-if-true-lemma x p q θ E s s∈can-E⟦p⟧)
... | inj₂ s∈can-q' = ++ʳ (Canₛₕ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) s∈can-q'
canₛₕ-if-true-lemma x p q θ (esuspend S' ∷ E) s s∈can-E⟦p⟧ =
  canₛₕ-if-true-lemma x p q θ E s s∈can-E⟦p⟧
canₛₕ-if-true-lemma x p q θ (etrap ∷ E) s s∈can-E⟦p⟧ =
  canₛₕ-if-true-lemma x p q θ E s s∈can-E⟦p⟧

canₛₕ-if-true : ∀ {x p q E r} θ →
  r ≐ E ⟦ if x ∣⇒ p ∣⇒ q  ⟧e →
  ∀ s →
    SharedVar.unwrap s ∈ Canₛₕ (E ⟦ p ⟧e) θ →
    SharedVar.unwrap s ∈ Canₛₕ r θ
canₛₕ-if-true {x} {p} {q} {E} θ r≐E⟦if⟧ s s∈can-E⟦p⟧
  rewrite sym (unplug r≐E⟦if⟧)
  = canₛₕ-if-true-lemma x p q θ E (SharedVar.unwrap s) s∈can-E⟦p⟧


canₛₕ-if-false-lemma : ∀ x p q θ E →
  ∀ S →
    S ∈ Canₛₕ (E ⟦ q ⟧e) θ →
    S ∈ Canₛₕ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ
canₛₕ-if-false-lemma x p q θ [] s s∈can-E⟦q⟧ = ++ʳ (Canₛₕ p θ) s∈can-E⟦q⟧
canₛₕ-if-false-lemma x p q θ (epar₁ q' ∷ E) s s∈can-E⟦q⟧∥q'
  with ++⁻ (Canₛₕ (E ⟦ q ⟧e) θ) s∈can-E⟦q⟧∥q'
... | inj₁ s∈can-E⟦q⟧ = ++ˡ (canₛₕ-if-false-lemma x p q θ E s s∈can-E⟦q⟧)
... | inj₂ s∈can-q' = ++ʳ (Canₛₕ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) s∈can-q'
canₛₕ-if-false-lemma x p q θ (epar₂ p' ∷ E) s s∈can-p'∥E⟦q⟧
  with ++⁻ (Canₛₕ p' θ) s∈can-p'∥E⟦q⟧
... | inj₁ s∈can-p' = ++ˡ s∈can-p'
... | inj₂ s∈can-E⟦q⟧ = ++ʳ (Canₛₕ p' θ) (canₛₕ-if-false-lemma x p q θ E s s∈can-E⟦q⟧)
canₛₕ-if-false-lemma x p q θ (eloopˢ q' ∷ E) s s∈can-E⟦q⟧>>q' = canₛₕ-if-false-lemma x p q θ E s s∈can-E⟦q⟧>>q'
canₛₕ-if-false-lemma x p q θ (eseq q' ∷ E) s s∈can-E⟦q⟧>>q'
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ q ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ)
... | yes nothin∈can-E⟦q⟧ | no  nothin∉can-E⟦if⟧ =
  ⊥-elim (nothin∉can-E⟦if⟧ (canₖ-if-false-lemma x p q θ E Code.nothin nothin∈can-E⟦q⟧))
... | no  nothin∉can-E⟦q⟧ | yes nothin∈can-E⟦if⟧ =
  ++ˡ (canₛₕ-if-false-lemma x p q θ E s s∈can-E⟦q⟧>>q')
... | no  nothin∉can-E⟦q⟧ | no  nothin∉can-E⟦if⟧ =
  canₛₕ-if-false-lemma x p q θ E s s∈can-E⟦q⟧>>q'
... | yes nothin∈can-E⟦q⟧ | yes nothin∈can-E⟦if⟧
  with ++⁻ (Canₛₕ (E ⟦ q ⟧e) θ) s∈can-E⟦q⟧>>q'
... | inj₁ s∈can-E⟦q⟧ = ++ˡ (canₛₕ-if-false-lemma x p q θ E s s∈can-E⟦q⟧)
... | inj₂ s∈can-q' = ++ʳ (Canₛₕ (E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) θ) s∈can-q'
canₛₕ-if-false-lemma x p q θ (esuspend S' ∷ E) s s∈can-E⟦q⟧ =
  canₛₕ-if-false-lemma x p q θ E s s∈can-E⟦q⟧
canₛₕ-if-false-lemma x p q θ (etrap ∷ E) s s∈can-E⟦q⟧ =
  canₛₕ-if-false-lemma x p q θ E s s∈can-E⟦q⟧

canₛₕ-if-false : ∀ {x p q E r} θ →
  r ≐ E ⟦ if x ∣⇒ p ∣⇒ q  ⟧e →
  ∀ s →
    SharedVar.unwrap s ∈ Canₛₕ (E ⟦ q ⟧e) θ →
    SharedVar.unwrap s ∈ Canₛₕ r θ
canₛₕ-if-false {x} {p} {q} {E} θ r≐E⟦if⟧ s s∈can-E⟦q⟧
  rewrite sym (unplug r≐E⟦if⟧)
  = canₛₕ-if-false-lemma x p q θ E (SharedVar.unwrap s) s∈can-E⟦q⟧

canθₛ-set-sig-monotonic-absence-lemma : ∀ sigs S'' →
  ∀ p S θ S∈ →
    SigMap.lookup{_}{S} sigs S∈ ≡ Signal.unknown →
    ∀ S' →
      S' ∈ Canθₛ (SigMap.update{_} sigs S Signal.absent) S'' p θ →
      S' ∈ Canθₛ sigs S'' p θ
canθₛ-set-sig-monotonic-absence-lemma [] S'' p (S ₛ) θ () status eq
canθₛ-set-sig-monotonic-absence-lemma (nothing ∷ sigs) S'' p (zero ₛ) θ S∈ eq = ⊥-elim (SigM.0∈S S∈)
canθₛ-set-sig-monotonic-absence-lemma (just Signal.present ∷ sigs) S'' p (zero ₛ) θ S∈ ()
canθₛ-set-sig-monotonic-absence-lemma (just Signal.absent ∷ sigs) S'' p (zero ₛ) θ S∈ ()
canθₛ-set-sig-monotonic-absence-lemma (just Signal.unknown ∷ sigs) S'' p (zero ₛ) θ S∈ eq
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← ([S]-env (S'' ₛ))))
... | no  S∉Cansigs = λ k z → z
... | yes S∈Cansigs
  with canθₛ-set-sig-monotonic sigs (suc S'') p (S'' ₛ) (θ ← [S]-env (S'' ₛ)) (Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ) Signal.absent
                               (Env.sig-stats-1map-right-← (S'' ₛ) Signal.unknown θ ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)))
                               (n∉map-suc-n-+ S'' (SigM.Dom' sigs))
... | r rewrite
          (begin
             (Env.set-sig{(S'' ₛ)} (θ ← [S]-env (S'' ₛ)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)) Signal.absent)
             ≡⟨ sym (Env.sig-switch-right (S'' ₛ) Signal.absent θ ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ))) ⟩
             (θ ← (Env.set-sig{(S'' ₛ)} ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) Signal.absent))
             ≡⟨ cong (_←_ θ) (Env.sig-put-1map-overwrite' (S'' ₛ) Signal.unknown Signal.absent ((Env.sig-∈-single (S'' ₛ) Signal.unknown))) ⟩
             (θ ← [S]-env-absent (S'' ₛ)) ∎)
     = r
canθₛ-set-sig-monotonic-absence-lemma (nothing ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  = canθₛ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) θ ((SigM.n∈S{S}{nothing}{sigs} S∈)) eq
canθₛ-set-sig-monotonic-absence-lemma (just Signal.present ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  = canθₛ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← _) ((SigM.n∈S{S}{just Signal.present}{sigs} S∈)) eq
canθₛ-set-sig-monotonic-absence-lemma (just Signal.absent ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  = canθₛ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← _) ((SigM.n∈S{S}{just Signal.absent}{sigs} S∈)) eq
canθₛ-set-sig-monotonic-absence-lemma (just Signal.unknown ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← ([S]-env (S'' ₛ))))
     | any (_≟_ S'') (Canθₛ (SigMap.update{_} sigs (S ₛ) Signal.absent) (suc S'') p (θ ← ([S]-env (S'' ₛ))))
... | yes S∈Cansigs | yes S∈Cansigs←a
  = canθₛ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq
... | no  S∉Cansigs | no  S∉Cansigs←a
  = canθₛ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env-absent (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq
... | no  S∉Cansigs | yes S∈Cansigs←a
  = ⊥-elim (S∉Cansigs (canθₛ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq S'' S∈Cansigs←a))
... | yes S∈Cansigs | no  S∉Cansigs←a
  with  (canθₛ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env-absent (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq)
... | r rewrite
         sym
          (begin
             (Env.set-sig{(S'' ₛ)} (θ ← [S]-env (S'' ₛ)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)) Signal.absent)
             ≡⟨ sym (Env.sig-switch-right (S'' ₛ) Signal.absent θ ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ))) ⟩
             (θ ← (Env.set-sig{(S'' ₛ)} ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) Signal.absent))
             ≡⟨ cong (_←_ θ) (Env.sig-put-1map-overwrite' (S'' ₛ) Signal.unknown Signal.absent ((Env.sig-∈-single (S'' ₛ) Signal.unknown))) ⟩
             (θ ← [S]-env-absent (S'' ₛ)) ∎)
   = λ k k∈ → canθₛ-set-sig-monotonic sigs (suc S'') p (S'' ₛ) (θ ← [S]-env (S'' ₛ))
                   ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)) Signal.absent
                   ((Env.sig-stats-1map-right-← (S'' ₛ) Signal.unknown θ ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ))))
                   (n∉map-suc-n-+ S'' (SigM.Dom' sigs))
                   k (r k k∈)  

canθₖ-set-sig-monotonic-absence-lemma : ∀ sigs S'' →
  ∀ p S θ S∈ →
    SigMap.lookup{_}{S} sigs S∈ ≡ Signal.unknown →
    ∀ k →
      k ∈ Canθₖ (SigMap.update{_} sigs S Signal.absent) S'' p θ →
      k ∈ Canθₖ sigs S'' p θ
canθₖ-set-sig-monotonic-absence-lemma [] S'' p (x ₛ) θ () eq
canθₖ-set-sig-monotonic-absence-lemma (nothing ∷ sigs) S'' p (zero ₛ) θ S∈ status eq = ⊥-elim (SigM.0∈S S∈)
canθₖ-set-sig-monotonic-absence-lemma (just Signal.present ∷ sigs) S'' p (zero ₛ) θ S∈ ()
canθₖ-set-sig-monotonic-absence-lemma (just Signal.absent ∷ sigs) S'' p (zero ₛ) θ S∈ ()
canθₖ-set-sig-monotonic-absence-lemma (just Signal.unknown ∷ sigs) S'' p (zero ₛ) θ S∈ eq
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← ([S]-env (S'' ₛ))))
... | no  S∉Cansigs = λ k z → z
... | yes S∈Cansigs
  with canθₖ-set-sig-monotonic sigs (suc S'') p (S'' ₛ) (θ ← [S]-env (S'' ₛ)) (Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ) Signal.absent
                               (Env.sig-stats-1map-right-← (S'' ₛ) Signal.unknown θ ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)))
                               (n∉map-suc-n-+ S'' (SigM.Dom' sigs))
... | r rewrite
          (begin
             (Env.set-sig{(S'' ₛ)} (θ ← [S]-env (S'' ₛ)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)) Signal.absent)
             ≡⟨ sym (Env.sig-switch-right (S'' ₛ) Signal.absent θ ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ))) ⟩
             (θ ← (Env.set-sig{(S'' ₛ)} ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) Signal.absent))
             ≡⟨ cong (_←_ θ) (Env.sig-put-1map-overwrite' (S'' ₛ) Signal.unknown Signal.absent ((Env.sig-∈-single (S'' ₛ) Signal.unknown))) ⟩
             (θ ← [S]-env-absent (S'' ₛ)) ∎)
     = r
canθₖ-set-sig-monotonic-absence-lemma (nothing ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  = canθₖ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) θ ((SigM.n∈S{S}{nothing}{sigs} S∈)) eq
canθₖ-set-sig-monotonic-absence-lemma (just Signal.present ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  = canθₖ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← _) ((SigM.n∈S{S}{just Signal.present}{sigs} S∈)) eq
canθₖ-set-sig-monotonic-absence-lemma (just Signal.absent ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  = canθₖ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← _) ((SigM.n∈S{S}{just Signal.absent}{sigs} S∈)) eq
canθₖ-set-sig-monotonic-absence-lemma (just Signal.unknown ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← ([S]-env (S'' ₛ))))
     | any (_≟_ S'') (Canθₛ (SigMap.update{_} sigs (S ₛ) Signal.absent) (suc S'') p (θ ← ([S]-env (S'' ₛ))))
... | yes S∈Cansigs | yes S∈Cansigs←a
  = canθₖ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq
... | no  S∉Cansigs | no  S∉Cansigs←a
  = canθₖ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env-absent (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq
... | no  S∉Cansigs | yes S∈Cansigs←a
  = ⊥-elim (S∉Cansigs (canθₛ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq S'' S∈Cansigs←a))
... | yes S∈Cansigs | no  S∉Cansigs←a
  with  (canθₖ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env-absent (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq)
... | r rewrite
         sym
          (begin
             (Env.set-sig{(S'' ₛ)} (θ ← [S]-env (S'' ₛ)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)) Signal.absent)
             ≡⟨ sym (Env.sig-switch-right (S'' ₛ) Signal.absent θ ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ))) ⟩
             (θ ← (Env.set-sig{(S'' ₛ)} ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) Signal.absent))
             ≡⟨ cong (_←_ θ) (Env.sig-put-1map-overwrite' (S'' ₛ) Signal.unknown Signal.absent ((Env.sig-∈-single (S'' ₛ) Signal.unknown))) ⟩
             (θ ← [S]-env-absent (S'' ₛ)) ∎)
   = λ k k∈ → canθₖ-set-sig-monotonic sigs (suc S'') p (S'' ₛ) (θ ← [S]-env (S'' ₛ))
                   ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)) Signal.absent
                   ((Env.sig-stats-1map-right-← (S'' ₛ) Signal.unknown θ ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ))))
                   (n∉map-suc-n-+ S'' (SigM.Dom' sigs))
                   k (r k k∈)  

canθₛₕ-set-sig-monotonic-absence-lemma : ∀ sigs S'' →
  ∀ p S θ S∈ →
    SigMap.lookup{_}{S} sigs S∈ ≡ Signal.unknown →
    ∀ s →
      s ∈ Canθₛₕ (SigMap.update{_} sigs S Signal.absent) S'' p θ →
      s ∈ Canθₛₕ sigs S'' p θ
canθₛₕ-set-sig-monotonic-absence-lemma [] S'' p (x ₛ) θ () eq
canθₛₕ-set-sig-monotonic-absence-lemma (nothing ∷ sigs) S'' p (zero ₛ) θ S∈ status eq = ⊥-elim (SigM.0∈S S∈)
canθₛₕ-set-sig-monotonic-absence-lemma (just Signal.present ∷ sigs) S'' p (zero ₛ) θ S∈ ()
canθₛₕ-set-sig-monotonic-absence-lemma (just Signal.absent ∷ sigs) S'' p (zero ₛ) θ S∈ ()
canθₛₕ-set-sig-monotonic-absence-lemma (just Signal.unknown ∷ sigs) S'' p (zero ₛ) θ S∈ eq
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← ([S]-env (S'' ₛ))))
... | no  S∉Cansigs = λ k z → z
... | yes S∈Cansigs
  with canθₛₕ-set-sig-monotonic sigs (suc S'') p (S'' ₛ) (θ ← [S]-env (S'' ₛ)) (Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ) Signal.absent
                               (Env.sig-stats-1map-right-← (S'' ₛ) Signal.unknown θ ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)))
                               (n∉map-suc-n-+ S'' (SigM.Dom' sigs))
... | r rewrite
          (begin
             (Env.set-sig{(S'' ₛ)} (θ ← [S]-env (S'' ₛ)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)) Signal.absent)
             ≡⟨ sym (Env.sig-switch-right (S'' ₛ) Signal.absent θ ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ))) ⟩
             (θ ← (Env.set-sig{(S'' ₛ)} ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) Signal.absent))
             ≡⟨ cong (_←_ θ) (Env.sig-put-1map-overwrite' (S'' ₛ) Signal.unknown Signal.absent ((Env.sig-∈-single (S'' ₛ) Signal.unknown))) ⟩
             (θ ← [S]-env-absent (S'' ₛ)) ∎)
     = r
canθₛₕ-set-sig-monotonic-absence-lemma (nothing ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  = canθₛₕ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) θ ((SigM.n∈S{S}{nothing}{sigs} S∈)) eq
canθₛₕ-set-sig-monotonic-absence-lemma (just Signal.present ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  = canθₛₕ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← _) ((SigM.n∈S{S}{just Signal.present}{sigs} S∈)) eq
canθₛₕ-set-sig-monotonic-absence-lemma (just Signal.absent ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  = canθₛₕ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← _) ((SigM.n∈S{S}{just Signal.absent}{sigs} S∈)) eq
canθₛₕ-set-sig-monotonic-absence-lemma (just Signal.unknown ∷ sigs) S'' p (suc S ₛ) θ S∈ eq
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← ([S]-env (S'' ₛ))))
     | any (_≟_ S'') (Canθₛ (SigMap.update{_} sigs (S ₛ) Signal.absent) (suc S'') p (θ ← ([S]-env (S'' ₛ))))
... | yes S∈Cansigs | yes S∈Cansigs←a
  = canθₛₕ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq
... | no  S∉Cansigs | no  S∉Cansigs←a
  = canθₛₕ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env-absent (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq
... | no  S∉Cansigs | yes S∈Cansigs←a
  = ⊥-elim (S∉Cansigs (canθₛ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq S'' S∈Cansigs←a))
... | yes S∈Cansigs | no  S∉Cansigs←a
  with  (canθₛₕ-set-sig-monotonic-absence-lemma sigs (suc S'') p (S ₛ) (θ ← [S]-env-absent (S'' ₛ)) ((SigM.n∈S{S}{just Signal.unknown}{sigs} S∈)) eq)
... | r rewrite
         sym
          (begin
             (Env.set-sig{(S'' ₛ)} (θ ← [S]-env (S'' ₛ)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)) Signal.absent)
             ≡⟨ sym (Env.sig-switch-right (S'' ₛ) Signal.absent θ ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ))) ⟩
             (θ ← (Env.set-sig{(S'' ₛ)} ([S]-env (S'' ₛ)) ((Env.sig-∈-single (S'' ₛ) Signal.unknown)) Signal.absent))
             ≡⟨ cong (_←_ θ) (Env.sig-put-1map-overwrite' (S'' ₛ) Signal.unknown Signal.absent ((Env.sig-∈-single (S'' ₛ) Signal.unknown))) ⟩
             (θ ← [S]-env-absent (S'' ₛ)) ∎)
   = λ k k∈ → canθₛₕ-set-sig-monotonic sigs (suc S'') p (S'' ₛ) (θ ← [S]-env (S'' ₛ))
                   ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ)) Signal.absent
                   ((Env.sig-stats-1map-right-← (S'' ₛ) Signal.unknown θ ((Env.sig-∈-single-right-← (S'' ₛ) Signal.unknown θ))))
                   (n∉map-suc-n-+ S'' (SigM.Dom' sigs))
                   k (r k k∈)  

canθₖ-term-nothin-lemma : ∀ sigs S' → ∀ {r} θ E →
  term-nothin r →
  ∀ k →
    k ∈ Canθₖ sigs S' (E ⟦ nothin ⟧e) θ →
    k ∈ Canθₖ sigs S' (E ⟦ r ⟧e) θ
canθₖ-term-nothin-lemma sigs S' {r} θ E tr
  = canθₖ-subset-lemma sigs S' (E ⟦ nothin ⟧e) (E ⟦ r ⟧e) θ
                       (λ θ' S x → canₛ-term-nothin-lemma θ' E tr S x)
                       (λ θ → canₖ-term-nothin-lemma θ E tnothin tr)

canθₛ-term-nothin-lemma : ∀ sigs S' → ∀ {r} θ E →
  term-nothin r →
  ∀ S →
    S ∈ Canθₛ sigs S' (E ⟦ nothin ⟧e) θ →
    S ∈ Canθₛ sigs S' (E ⟦ r ⟧e) θ
canθₛ-term-nothin-lemma sigs S' {r} θ E tr
  = canθₛ-subset-lemma sigs S' (E ⟦ nothin ⟧e) (E ⟦ r ⟧e) θ (λ θ' S x → canₛ-term-nothin-lemma θ' E tr S x)

