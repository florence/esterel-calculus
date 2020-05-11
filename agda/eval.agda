module _ where

open import utility

open import Function using (_∘_)
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.CanFunction
  using (Canₛ ; Canₛₕ)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; module SigMap ; module ShrMap ; module VarMap ; []env ; sig-stats ; Dom)
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Context.Properties
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)

open import Relation.Nullary
  using (¬_ ; yes ; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)
open import Data.Empty
  using (⊥ ; ⊥-elim)
import Data.FiniteMap
open import Data.List
  using (List ; _∷_ ; [] ; _++_)
open import Data.List.All as All
  using (All ; _∷_ ; [])
open import Data.Nat
  using (ℕ ; zero ; suc ; _+_)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; _,′_ ; ∃ )
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
open import Esterel.Lang.Binding
-- open import coherence
open import blocked
open import sn-calculus
open import par-swap
open import calculus

open _≐_⟦_⟧e
open _≐_⟦_⟧c

open EvaluationContext1
open Context1

open import Data.Maybe

sn≡ₑ-context : ∀ p q C ->
             (∀ p BVp FVp -> CorrectBinding p BVp FVp -> CB (C ⟦ p ⟧c)) ->
             p sn≡ₑ q -> (C ⟦ p ⟧c) sn≡ₑ (C ⟦ q ⟧c)
sn≡ₑ-context p q C CBfill (rstp psn⟶q) = rstp (Context-sn⟶⟦⟧ C psn⟶q)
sn≡ₑ-context p q C CBfill (rsym{p = .q}{BV = BV} {FV} psn≡ₑq CBq) with sn≡ₑ-context q p C CBfill psn≡ₑq 
... | C⟦q⟧csn≡ₑC⟦p⟧c = rsym C⟦q⟧csn≡ₑC⟦p⟧c (CBfill q BV FV CBq) 
sn≡ₑ-context p .p C _ rref = rref
sn≡ₑ-context p q C CBfill (rtrn{r = r} psn≡ₑr rsn≡ₑq) with
    sn≡ₑ-context p r C CBfill psn≡ₑr | sn≡ₑ-context r q C CBfill rsn≡ₑq 
... | C⟦p⟧csn≡ₑC⟦r⟧c | C⟦r⟧csn≡ₑC⟦q⟧c = rtrn {r = C ⟦ r ⟧c} C⟦p⟧csn≡ₑC⟦r⟧c C⟦r⟧csn≡ₑC⟦q⟧c

sn≡ₑ-sn⟶* : ∀ {p q} -> p sn⟶* q -> p sn≡ₑ q
sn≡ₑ-sn⟶* rrefl = rref
sn≡ₑ-sn⟶* (rstep psn⟶q psn⟶*q) = rtrn (rstp psn⟶q) (sn≡ₑ-sn⟶* psn⟶*q)

≡ₑ-context :
  ∀ {p q} -> ∀ C1 C2 ->
   (∀ {r r′ BVp FVp} -> CorrectBinding r BVp FVp -> r′ ≐ C2 ⟦ r ⟧c -> CB r′) ->
   p ≡ₑ q # C1 ->
   p ≡ₑ q # (C2 ++ C1)
≡ₑ-context C C′ CBfill ≡ₑrefl = ≡ₑrefl
≡ₑ-context C C′ CBfill (≡ₑtran p≡ₑr r≡ₑq)
  with ≡ₑ-context C C′ CBfill p≡ₑr
... | p≡ₑr#C
  with ≡ₑ-context C C′ CBfill r≡ₑq
... | r≡ₑq#C = ≡ₑtran p≡ₑr#C r≡ₑq#C
≡ₑ-context C C′ CBfill (≡ₑsymm{q = q} CBq p≡ₑq)
  with ≡ₑ-context C C′ CBfill p≡ₑq
... | q≡ₑp#C = ≡ₑsymm (CBfill CBq (++-is-nesting C′ C _)) q≡ₑp#C
≡ₑ-context C1 C2 CBfill (≡ₑctxt{_}{C''} C′⟦p⟧≐C′⟦p⟧c C′⟦q⟧≐C′⟦q⟧c p≡ₑq)
  with ≡ₑ-context (C1 ++ C'') C2  wrapCBfill p≡ₑq where
      wrapCBfill : ∀ {r r′ BVp FVp} ->
        CorrectBinding r BVp FVp ->
        r′ ≐ C2 ⟦ r ⟧c ->
        CB r′
      wrapCBfill{r} CB C′⟦r⟧c = CBfill CB C′⟦r⟧c
... | p≡ₑq#[C′++C++C''] rewrite sym (++-assoc C2 C1 C'')
  =  ≡ₑctxt C′⟦p⟧≐C′⟦p⟧c C′⟦q⟧≐C′⟦q⟧c p≡ₑq#[C′++C++C'']
≡ₑ-context C C′ CBfill (≡ₑstep p⟶₁q)
  = ≡ₑstep p⟶₁q


θ-present-signals : Env → List Signal
θ-present-signals θ = Data.List.mapMaybe (f ∘ _ₛ) DomS
  where
    DomS = (fst (Env.Dom θ))
    f : Signal → Maybe Signal
    f S with (Env.Sig∈ S θ)
    ... | (no S∈) = nothing
    ... | (yes S∈) with sig-stats{S} θ S∈
    ... | Signal.present = just S
    ... | Signal.absent = nothing
    ... | Signal.unknown = nothing

get-signals : Term → List Signal
get-signals nothin = []
get-signals pause = []
get-signals (signl S p) = []
get-signals (present S ∣⇒ p ∣⇒ p₁) = []
get-signals (emit S) = []
get-signals (p ∥ p₁) = []
get-signals (loop p) = []
get-signals (loopˢ p q) = []
get-signals (p >> p₁) = []
get-signals (suspend p S) = []
get-signals (trap p) = []
get-signals (exit x) = []
get-signals (shared s ≔ e in: p) = []
get-signals (s ⇐ e) = []
get-signals (var x ≔ e in: p) = []
get-signals (x ≔ e) = []
get-signals (if x ∣⇒ p ∣⇒ p₁) = []
get-signals (ρ θ · p) = θ-present-signals θ


data eval-result : Set where
   output : List Signal → eval-result

data non-constructive : Env → Term → Set where
  nc : ∀{p θ} → (Σ (Env × Term) λ {(θq , q) → (ρ θ · p) sn≡ₑ (ρ θq · q) × (manifests-as-non-constructive θq q)})
              → non-constructive θ p

data evalsn≡ₑ : Term → Env → eval-result → Set where
   evalsn-complete : ∀{p q θ θq} →
     (ρθ·p≡q : (ρ θ · p) sn≡ₑ (ρ θq · q)) →
     (complete-q : complete (ρ θq · q)) →
     evalsn≡ₑ p θ (output (get-signals (ρ θq · q)))

data eval∥R∪sn≡ₑ : Term → Env → eval-result → Set where
   eval∥R∪sn-complete : ∀{p q θ θq} →
     (ρθ·p≡q : (ρ θ · p) ∥R∪sn≡ₑ (ρ θq · q)) →
     (complete-q : complete (ρ θq · q)) →
     eval∥R∪sn≡ₑ p θ (output (get-signals (ρ θq · q)))

data eval≡ₑ : Term → Env → eval-result → Set where
   eval-complete : ∀{p q θ θq} →
     (ρθ·p≡q : (ρ θ · p) ≡ₑ (ρ θq · q) # []) →
     (complete-q : complete (ρ θq · q)) →
     eval≡ₑ p θ (output (get-signals (ρ θq · q)))
