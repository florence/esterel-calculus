module sn-calculus-compatconf.pot where

open import can-function-preserve
  using (canₖ-monotonic ; canₛ-monotonic ; canₛₕ-monotonic)

open import sn-calculus
open import utility renaming (_U̬_ to _∪_)
open import context-properties
  using (->pot-view)

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.CanFunction
  using (Can ; Canₛ ; Canₛₕ ; Canₖ ; Canθ ; Canθₛ ; Canθₛₕ ; Canθₖ)
open import Esterel.Lang.CanFunction.Properties
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
  using (Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Context.Properties
  using (unplugc)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)

open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; cong ; trans ; subst ; module ≡-Reasoning)
open import Data.Bool
  using (Bool ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; _∷_ ; [] ; _++_)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using ()
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; zero ; suc ; _+_) renaming (_⊔_ to _⊔ℕ_)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; _,′_ ; proj₁ ; proj₂ ; _×_ ; ∃)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_ ; id ; _∋_)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open ->pot-view

open Context1
open _≐_⟦_⟧c

{-
       (p)
  ρθ. C⟦pin⟧   -- sn⟶₁ ->    ρθ' C⟦pin⟧
 (ρθ) C⟦pin⟧   -- sn⟶₁ ->   (ρθ) C⟦qin⟧
-}
1-steplρ-pot-lemma : ∀{C θ p pin qin θ' BV FV A} →
  {ρθpsn⟶₁ρθ'p  :  ρ⟨ θ , A ⟩· p sn⟶₁ ρ⟨ θ' , A ⟩· p} →

  ->pot-view  ρθpsn⟶₁ρθ'p  refl refl →

  CorrectBinding pin BV FV →
  p ≐ C ⟦ pin ⟧c →
  pin sn⟶₁ qin →

  ρ⟨ θ , A ⟩· C ⟦ qin ⟧c   sn⟶₁  ρ⟨ θ' , A ⟩· C ⟦ qin ⟧c

1-steplρ-pot-lemma {C} {θ} {_} {pin} {qin}
  {ρθpsn⟶₁ρθ'p = .(rabsence {S = S} S∈ θS≡unknown S∉can-p-θ)}
  (vabsence S S∈ θS≡unknown S∉can-p-θ)
  cb p≐C⟦pin⟧ pinsn⟶₁qin with sym (unplugc p≐C⟦pin⟧)
... | refl
  = rabsence {S = S} S∈ θS≡unknown
      (λ S∈can-q-θ →
        S∉can-p-θ
          (canθₛ-plug 0 (Env.sig θ) C pin qin
            (λ θ* → canₛ-monotonic θ* _ _ cb pinsn⟶₁qin ∘ _ₛ)
            (λ θ* → canₖ-monotonic θ* _ _ cb pinsn⟶₁qin)
            Env.[]env (Signal.unwrap S) S∈can-q-θ))

1-steplρ-pot-lemma {C} {θ} {_} {pin} {qin}
  {ρθpsn⟶₁ρθ'p = .(rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
  (vreadyness {θ = .θ} s s∈ θs≡old⊎θs≡new s∉can-p-θ)
  cb p≐C⟦pin⟧ pinsn⟶₁qin with sym (unplugc p≐C⟦pin⟧)
... | refl
  = rreadyness {s = s} s∈ θs≡old⊎θs≡new
      (λ s∈can-q-θ →
        s∉can-p-θ
          (canθₛₕ-plug 0 (Env.sig θ) C pin qin
            (λ θ* → canₛₕ-monotonic θ* _ _ cb pinsn⟶₁qin ∘ _ₛₕ)
            (λ θ* → canₖ-monotonic θ* _ _ cb pinsn⟶₁qin)
            (λ θ* → canₛ-monotonic θ* _ _ cb pinsn⟶₁qin ∘ _ₛ)
            Env.[]env (SharedVar.unwrap s)
            s∈can-q-θ))



-- Wrapper around 1-steplρ-pot-lemma.
1-steplρ-pot : ∀{p q θ θ' BV FV A} →
  {ρθpsn⟶₁ρθ'p  :  ρ⟨ θ , A ⟩· p sn⟶₁ ρ⟨ θ' , A ⟩· p} →
  CorrectBinding (ρ⟨ θ , A ⟩· p) BV FV →

  ->pot-view  ρθpsn⟶₁ρθ'p  refl refl →
  p sn⟶ q →

  (ρ⟨ θ' , A ⟩· p  sn⟶*  ρ⟨ θ' , A ⟩· q  ×
   ρ⟨ θ  , A ⟩· q  sn⟶*  ρ⟨ θ' , A ⟩· q)

1-steplρ-pot cb@(CBρ cb') pot psn⟶q@(rcontext _ p≐C⟦pin⟧ pinsn⟶₁qin) =
  sn⟶*-inclusion (rcontext _ (dcenv p≐C⟦pin⟧) pinsn⟶₁qin) ,′
  sn⟶*-inclusion
    (sn⟶-inclusion
      (1-steplρ-pot-lemma pot
        (proj₂ (binding-extractc' cb' p≐C⟦pin⟧))
        p≐C⟦pin⟧ pinsn⟶₁qin))
