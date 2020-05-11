module par-swap.properties where

open import par-swap
open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Context
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Data.Product

Context1-∥R : ∀{p p'} → (C1 : Context1) → p ∥R p' → ((C1 ∷ []) ⟦ p ⟧c) ∥R ((C1 ∷ []) ⟦ p' ⟧c)
Context1-∥R (ceval (epar₁ q₁)) (∥Rstep dc) = ∥Rstep (dcpar₁ dc)
Context1-∥R (ceval (epar₂ p₂)) (∥Rstep dc) = ∥Rstep (dcpar₂ dc)
Context1-∥R (ceval (eseq q₁)) (∥Rstep dc) = ∥Rstep (dcseq₁ dc)
Context1-∥R (ceval (eloopˢ q₁)) (∥Rstep dc) = ∥Rstep (dcloopˢ₁ dc)
Context1-∥R (ceval (esuspend S)) (∥Rstep dc) = ∥Rstep (dcsuspend dc)
Context1-∥R (ceval etrap) (∥Rstep dc) = ∥Rstep (dctrap dc)
Context1-∥R (csignl S) (∥Rstep dc) = ∥Rstep (dcsignl dc)
Context1-∥R (cpresent₁ S q₁) (∥Rstep dc) = ∥Rstep (dcpresent₁ dc)
Context1-∥R (cpresent₂ S p₂) (∥Rstep dc) = ∥Rstep (dcpresent₂ dc)
Context1-∥R cloop (∥Rstep dc) = ∥Rstep (dcloop dc)
Context1-∥R (cloopˢ₂ p₂) (∥Rstep dc) = ∥Rstep (dcloopˢ₂ dc)
Context1-∥R (cseq₂ p₂) (∥Rstep dc) = ∥Rstep (dcseq₂ dc)
Context1-∥R (cshared s e) (∥Rstep dc) = ∥Rstep (dcshared dc)
Context1-∥R (cvar x e) (∥Rstep dc) = ∥Rstep (dcvar dc)
Context1-∥R (cif₁ x q₁) (∥Rstep dc) = ∥Rstep (dcif₁ dc)
Context1-∥R (cif₂ x p₂) (∥Rstep dc) = ∥Rstep (dcif₂ dc)
Context1-∥R (cenv θ A) (∥Rstep dc) = ∥Rstep (dcenv dc)

Context1-∥R* : ∀ {p q} -> (C1 : Context1) -> p ∥R* q -> ((C1 ∷ []) ⟦ p ⟧c) ∥R* ((C1 ∷ []) ⟦ q ⟧c)
Context1-∥R* C1 ∥R0 = ∥R0
Context1-∥R* C1 (∥Rn p∥Rq q∥R*r) = ∥Rn (Context1-∥R C1 p∥Rq) (Context1-∥R* C1 q∥R*r)
