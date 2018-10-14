module _ where

open import Data.Nat using (_+_ ;  _≤′_ ; suc)
open import Induction.Nat using (<-rec)
open import Esterel.Lang.CanFunction
open import Function using (_∋_ ; _∘_ ; id ; _$_)
open import Data.Nat.Properties.Simple using ( +-comm ; +-assoc)
open import utility
open import noetherian using (noetherian ; ∥_∥s)
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Environment as Env
open import Esterel.Context
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; subst ; cong ; trans ; module ≡-Reasoning ; cong₂ ; subst₂ ; inspect) 
open import Data.Empty
open import sn-calculus
open import context-properties -- get view, E-views
open import Esterel.Lang.Binding
open import Data.Maybe using ( just )
-- open import coherence
open import Data.List.Any
open import Data.List.Any.Properties
open import Esterel.Lang.CanFunction.Base
open import eval
open import blocked
open import Data.List.All
open import eval

open ≡-Reasoning using (_≡⟨_⟩_ ; _≡⟨⟩_ ; _∎)

open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Data.FiniteMap
import Data.OrderedListMap as OMap
open import Data.Nat as Nat using (ℕ)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import sn-calculus-compatconf using (1-step)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open import binding-preserve

open import sn-calculus-props
open import par-swap
open import par-swap.union-properties
open import calculus
open import calculus.properties

evalsn≡ₑ-consistent : ∀{output output'} θ p → CB (ρ θ · p) → evalsn≡ₑ p θ output → evalsn≡ₑ p θ output' → output ≡ output'
evalsn≡ₑ-consistent θ p ⊢cb-p (evalsn-complete ρθ·p≡q complete-q) (evalsn-complete ρθ·p≡r complete-r)
  with sn≡ₑ-consistent (proj₂ (sn≡ₑ-preserve-cb ⊢cb-p ρθ·p≡q)) (rtrn (rsym ρθ·p≡q  ⊢cb-p) ρθ·p≡r)
... | (s , qsn⟶*s , rsn⟶*s)
  with inescapability-of-complete-sn complete-q qsn⟶*s
... | complete-s
   with ρ-stays-ρ-sn⟶* qsn⟶*s | ρ-stays-ρ-sn⟶* rsn⟶*s
... | θq , _ , refl | θr , _ , refl
   with equality-of-complete-sn⟶* complete-q qsn⟶*s
      | equality-of-complete-sn⟶* complete-r rsn⟶*s
... | refl | refl = refl

eval∥R∪sn≡ₑ-consistent : ∀ {output output'} θ p →
  CB (ρ θ · p) →
  eval∥R∪sn≡ₑ p θ output →
  eval∥R∪sn≡ₑ p θ output' →
  output ≡ output'
eval∥R∪sn≡ₑ-consistent θ p ⊢cb-p (eval∥R∪sn-complete ρθ·p≡q complete-q) (eval∥R∪sn-complete ρθ·p≡r complete-r)
  with ∥R∪sn≡ₑ-consistent (proj₂ (∥R∪sn≡ₑ-preserve-cb ⊢cb-p ρθ·p≡q)) (∪trn (∪sym ρθ·p≡q  ⊢cb-p) ρθ·p≡r)
... | (s , qsn⟶*s , rsn⟶*s)
  with inescapability-of-complete-∪ complete-q qsn⟶*s
... | complete-s
   with ρ-stays-ρ-∪ qsn⟶*s | ρ-stays-ρ-∪ rsn⟶*s
... | θq , _ , refl | θr , _ , refl
   with equality-of-complete-∪ complete-q qsn⟶*s
      | equality-of-complete-∪ complete-r rsn⟶*s
... | refl | refl = refl

eval≡ₑ->eval∥R∪sn≡ : ∀ {p θ output} ->
  eval≡ₑ p θ output →
  eval∥R∪sn≡ₑ p θ output
eval≡ₑ->eval∥R∪sn≡ (eval-complete ρθ·p≡q complete-q) =
  eval∥R∪sn-complete (≡ₑ-to-∥R∪sn≡ₑ ρθ·p≡q) complete-q

eval≡ₑ-consistent : ∀ {output output'} θ p →
  CB (ρ θ · p) →
  eval≡ₑ p θ output →
  eval≡ₑ p θ output' →
  output ≡ output'
eval≡ₑ-consistent θ p CBρp eval≡₁ eval≡₂
  = eval∥R∪sn≡ₑ-consistent θ p CBρp
      (eval≡ₑ->eval∥R∪sn≡ eval≡₁)
      (eval≡ₑ->eval∥R∪sn≡ eval≡₂)

sn≡ₑ=>eval : ∀ p θp outputp q θq outputq → CB (ρ θp · p) → (ρ θp · p) sn≡ₑ (ρ θq · q) → evalsn≡ₑ p θp outputp → evalsn≡ₑ q θq outputq → outputp ≡ outputq
sn≡ₑ=>eval _ _ _ _ _ _ CB eq (evalsn-complete ρθ·p≡q complete-q) (evalsn-complete ρθ·p≡q₁ complete-q₁)
  with sn≡ₑ-consistent (proj₂ (sn≡ₑ-preserve-cb CB ρθ·p≡q)) (rtrn (rsym ρθ·p≡q  CB) (rtrn eq ρθ·p≡q₁))
... | (s , qsn⟶*s , rsn⟶*s)
  with inescapability-of-complete-sn complete-q qsn⟶*s
... | complete-s
   with ρ-stays-ρ-sn⟶* qsn⟶*s | ρ-stays-ρ-sn⟶* rsn⟶*s
... | θq , _ , refl | θr , _ , refl
   with equality-of-complete-sn⟶* complete-q qsn⟶*s
      | equality-of-complete-sn⟶* complete-q₁ rsn⟶*s
... | refl | refl = refl

∥R∪sn≡ₑ=>eval : ∀ p θp outputp q θq outputq →
  CB (ρ θp · p) →
  (ρ θp · p) ∥R∪sn≡ₑ (ρ θq · q) →
  eval∥R∪sn≡ₑ p θp outputp →
  eval∥R∪sn≡ₑ q θq outputq →
  outputp ≡ outputq
∥R∪sn≡ₑ=>eval _ _ _ _ _ _ CB eq (eval∥R∪sn-complete ρθ·p≡q complete-q) (eval∥R∪sn-complete ρθ·p≡q₁ complete-q₁)
  with ∥R∪sn≡ₑ-consistent (proj₂ (∥R∪sn≡ₑ-preserve-cb CB ρθ·p≡q)) (∪trn (∪sym ρθ·p≡q  CB) (∪trn eq ρθ·p≡q₁))
... | (s , qsn⟶*s , rsn⟶*s)
  with inescapability-of-complete-∪ complete-q qsn⟶*s
... | complete-s
   with ρ-stays-ρ-∪ qsn⟶*s | ρ-stays-ρ-∪ rsn⟶*s
... | θq , _ , refl | θr , _ , refl
   with equality-of-complete-∪ complete-q qsn⟶*s
      | equality-of-complete-∪ complete-q₁ rsn⟶*s
... | refl | refl = refl

≡ₑ=>eval : ∀ p θp outputp q θq outputq →
  CB (ρ θp · p) →
  (ρ θp · p) ≡ₑ (ρ θq · q) # [] →
  eval≡ₑ p θp outputp →
  eval≡ₑ q θq outputq →
  outputp ≡ outputq
≡ₑ=>eval p θp outputp q θq outputq CBρp ρp≡ₑρq eval≡₁ eval≡₂
  = ∥R∪sn≡ₑ=>eval p θp outputp q θq outputq CBρp
      (≡ₑ-to-∥R∪sn≡ₑ ρp≡ₑρq)
      (eval≡ₑ->eval∥R∪sn≡ eval≡₁)
      (eval≡ₑ->eval∥R∪sn≡ eval≡₂)
