module std-reduction.Base where

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open EvaluationContext1
open import Esterel.Environment as Env
  using (Env)

open import Data.List
  using (List; _∷_ ; [] ; mapMaybe)
open import blocked
open import Data.Sum
  using (_⊎_)


blocked-or-done : Env → Ctrl → Term → Set
blocked-or-done θ A p = (done p) ⊎ (blocked θ A p)

data left-most : Env → EvaluationContext → Set where
  lhole : ∀{θ} → left-most θ []
  lseq : ∀{θ E q} → left-most θ E → left-most θ ((eseq q) ∷ E)
  lloopˢ : ∀{θ E q} → left-most θ E → left-most θ ((eloopˢ q) ∷ E) 
  lparl : ∀{θ E q} → left-most θ E → left-most θ ((epar₁ q) ∷ E)
  lparrdone : ∀{θ E p} → done p → left-most θ E → left-most θ ((epar₂ p) ∷ E)
  lparrblocked : ∀{θ A E p} → blocked θ A p → left-most θ E → left-most θ ((epar₂ p) ∷ E)
  lsuspend : ∀{θ E S} → left-most θ E → left-most θ ((esuspend S) ∷ E)
  ltrap : ∀{θ E} → left-most θ E → left-most θ (etrap ∷ E)
