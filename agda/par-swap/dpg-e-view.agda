module par-swap.dpg-e-view where

open import par-swap
open import par-swap.properties
open import par-swap.confluent
open import par-swap.dpg-pot
open import utility
open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
open import Esterel.Lang.PotentialFunction
open import Esterel.Lang.PotentialFunction.Plug
open import Esterel.Environment as Env
open import Esterel.Context
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Data.Empty
open import sn-calculus
open import context-properties -- get view, E-views

DPG-E-view :
 ∀ {E C r₁ r₂ p q θ θ' pin qin} ->
  (peq : p ≐ E ⟦ pin ⟧e) ->
  (qeq : q ≐ E ⟦ qin ⟧e) ->
  p ≐ C ⟦ r₁ ∥ r₂ ⟧c ->
  (psn⟶₁q : ρ θ · p sn⟶₁ ρ θ' · q) ->
  ->E-view psn⟶₁q peq qeq ->
  Σ[ d ∈ Term ]
  Σ[ sn⟶₁d ∈ ρ θ · C ⟦ r₂ ∥ r₁ ⟧c sn⟶₁ ρ θ' · d ]
  Σ[ ∥Rd ∈ q ∥R* d ]
  Σ[ E′ ∈ List EvaluationContext1 ]
  Σ[ pin′ ∈ Term ]
  Σ[ qin′ ∈ Term ]
  Σ[ peq′ ∈ C ⟦ r₂ ∥ r₁ ⟧c ≐ E′ ⟦ pin′ ⟧e ]
  Σ[ qeq′ ∈ d ≐ E′ ⟦ qin′ ⟧e ]
  ->E-view sn⟶₁d peq′ qeq′

DPG-E-view dehole dehole dchole psn⟶₁q ()
DPG-E-view dehole dehole (dcpar₁ pC) psn⟶₁q ()
DPG-E-view dehole dehole (dcpar₂ pC) psn⟶₁q ()
DPG-E-view dehole dehole (dcseq₁ pC) psn⟶₁q ()
DPG-E-view dehole dehole (dcseq₂ pC) psn⟶₁q ()
DPG-E-view dehole dehole (dcsuspend pC) psn⟶₁q ()
DPG-E-view dehole dehole (dctrap pC) psn⟶₁q ()
DPG-E-view dehole dehole (dcsignl pC) psn⟶₁q ()
DPG-E-view dehole dehole (dcloop pC) psn⟶₁q ()
DPG-E-view dehole dehole (dcloopˢ₁ pC) psn⟶₁q ()
DPG-E-view dehole dehole (dcloopˢ₂ pC) psn⟶₁q ()

DPG-E-view dehole dehole (dcpresent₁ pC)
           (ris-present S∈ s[θ]≡p dehole)
           vis-present
  =  _ , ris-present S∈ s[θ]≡p dehole , ∥Rn (∥Rstep pC) ∥R0 ,
    _ , _ , _ , dehole , dehole , vis-present

DPG-E-view dehole dehole (dcpresent₁ pC)
           (ris-absent S∈ s[θ]≡p dehole)
           vis-absent
 = _ , ris-absent S∈ s[θ]≡p dehole , ∥R0 ,
   _ , _ , _ , dehole , dehole , vis-absent

DPG-E-view dehole dehole (dcpresent₂ pC)
           (ris-present S∈ s[θ]≡a dehole)
           vis-present
 = _ , ris-present S∈ s[θ]≡a dehole , ∥R0 ,
   _ , _ , _ , dehole , dehole , vis-present

DPG-E-view dehole dehole (dcpresent₂ pC)
           (ris-absent S∈ s[θ]≡a dehole)
           vis-absent
 = _ ,  ris-absent S∈ s[θ]≡a dehole , ∥Rn (∥Rstep pC) ∥R0 ,
   _ , _ , _ , dehole , dehole , vis-absent

DPG-E-view dehole dehole (dcshared pC)
           (rraise-shared allready dehole)
           vraise-shared
 = _ , rraise-shared allready dehole ,
       Context1-∥R* (cenv _) (∥Rn (∥Rstep pC) ∥R0) ,
   _ , _ , _ , dehole , dehole , vraise-shared

DPG-E-view dehole dehole (dcvar pC)
           (rraise-var allready dehole)
           vraise-var
 = _ , rraise-var allready dehole ,
       Context1-∥R* (cenv _) (∥Rn (∥Rstep pC) ∥R0) ,
   _ , _ , _ , dehole , dehole , vraise-var

DPG-E-view dehole dehole (dcif₁ pC)
           (rif-false x∈ x[θ]≡0 dehole)
           vif-false
 = _ , rif-false x∈ x[θ]≡0 dehole , ∥R0 ,
   _ , _ , _ , dehole , dehole , vif-false

DPG-E-view dehole dehole (dcif₁ pC)
           (rif-true x∈ x[θ]≡s dehole)
           vif-true
 = _ , rif-true x∈ x[θ]≡s dehole , ∥Rn (∥Rstep pC) ∥R0 ,
   _ , _ , _ , dehole , dehole , vif-true

DPG-E-view dehole dehole (dcif₂ pC)
           (rif-false x∈ x[θ]≡0 dehole)
           vif-false
 = _ , rif-false x∈ x[θ]≡0 dehole , ∥Rn (∥Rstep pC) ∥R0 ,
   _ , _ , _ , dehole , dehole , vif-false

DPG-E-view dehole dehole (dcif₂ pC)
           (rif-true x∈ x[θ]≡s dehole)
           vif-true
 = _ , rif-true x∈ x[θ]≡s dehole , ∥R0 ,
   _ , _ , _ , dehole , dehole , vif-true

DPG-E-view dehole dehole (dcenv pC)
           (rmerge dehole)
           vmerge
 = _ , rmerge dehole , ∥Rn (∥Rstep pC) ∥R0 ,
   _ , _ , _ , dehole , dehole , vmerge

DPG-E-view (depar₁ pE) (depar₁ qE) dchole psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (depar₁ pE) (depar₁ qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with wrap-rho redo-sub pE qE E-view-sub
               _ (depar₂ pE) (depar₂ qE)
... | (redo′ , E-view′)
 = _ , redo′ , ∥Rn (∥Rstep dchole) ∥R0 ,
   _ , _ , _ , depar₂ pE , depar₂ qE , E-view′

DPG-E-view (depar₂ pE) (depar₂ qE) dchole psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (depar₂ pE) (depar₂ qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with wrap-rho redo-sub pE qE E-view-sub
               _ (depar₁ pE) (depar₁ qE)
... | (redo′ , E-view′)
 = _ , redo′ , ∥Rn (∥Rstep dchole) ∥R0 ,
   _ , _ , _ , depar₁ pE , depar₁ qE , E-view′

DPG-E-view {e ∷ _} (depar₁ pE) (depar₁ qE) (dcpar₁ pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (depar₁ pE) (depar₁ qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with DPG-E-view pE qE pC redo-sub E-view-sub
... | (ds , pssn⟶₁ds , qs∥Rds , _ , _ , _ , pE′ , qE′ , E-view-sub′)
 with wrap-rho pssn⟶₁ds pE′ qE′ E-view-sub′ _ (depar₁ pE′) (depar₁ qE′)
... | (redo , E-view′)
 = _ , redo , Context1-∥R* (ceval e) qs∥Rds ,
   _ , _ , _ , depar₁ pE′ , depar₁ qE′ , E-view′

DPG-E-view {e ∷ _} (depar₂ pE) (depar₂ qE) (dcpar₂ pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (depar₂ pE) (depar₂ qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with DPG-E-view pE qE pC redo-sub E-view-sub
... | (ds , pssn⟶₁ds , qs∥Rds , _ , _ , _ , pE′ , qE′ , E-view-sub′)
 with wrap-rho pssn⟶₁ds pE′ qE′ E-view-sub′ _ (depar₂ pE′) (depar₂ qE′)
... | (redo , E-view′)
 = _ , redo , Context1-∥R* (ceval e) qs∥Rds ,
   _ , _ , _ , depar₂ pE′ , depar₂ qE′ , E-view′

DPG-E-view {e ∷ _} (desuspend pE) (desuspend qE) (dcsuspend pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (desuspend pE) (desuspend qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with DPG-E-view pE qE pC redo-sub E-view-sub
... | (ds , pssn⟶₁ds , qs∥Rds , _ , _ , _ , pE′ , qE′ , E-view-sub′)
 with wrap-rho pssn⟶₁ds pE′ qE′ E-view-sub′ _ (desuspend pE′) (desuspend qE′)
... | (redo , E-view′)
 = _ , redo , Context1-∥R* (ceval e) qs∥Rds ,
   _ , _ , _ , desuspend pE′ , desuspend qE′ , E-view′

DPG-E-view {e ∷ _} (detrap pE) (detrap qE) (dctrap pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (detrap pE) (detrap qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with DPG-E-view pE qE pC redo-sub E-view-sub
... | (ds , pssn⟶₁ds , qs∥Rds , _ , _ , _ , pE′ , qE′ , E-view-sub′)
 with wrap-rho pssn⟶₁ds pE′ qE′ E-view-sub′ _ (detrap pE′) (detrap qE′)
... | (redo , E-view′)
 = _ , redo ,  Context1-∥R* (ceval e) qs∥Rds ,
   _ , _ , _ , detrap pE′ , detrap qE′ , E-view′

DPG-E-view {e ∷ _} (deseq pE) (deseq qE) (dcseq₁ pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (deseq pE) (deseq qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with DPG-E-view pE qE pC redo-sub E-view-sub
... | (ds , pssn⟶₁ds , qs∥Rds , _ , _ , _ , pE′ , qE′ , E-view-sub′)
 with wrap-rho pssn⟶₁ds pE′ qE′ E-view-sub′ _ (deseq pE′) (deseq qE′)
... | (redo , E-view′)
 = _ , redo , Context1-∥R* (ceval e) qs∥Rds ,
   _ , _ , _ , deseq pE′ , deseq qE′ , E-view′

DPG-E-view {e ∷ _} (deloopˢ pE) (deloopˢ qE) (dcloopˢ₁ pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (deloopˢ pE) (deloopˢ qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with DPG-E-view pE qE pC redo-sub E-view-sub
... | (ds , pssn⟶₁ds , qs∥Rds , _ , _ , _ , pE′ , qE′ , E-view-sub′)
 with wrap-rho pssn⟶₁ds pE′ qE′ E-view-sub′ _ (deloopˢ pE′) (deloopˢ qE′)
... | (redo , E-view′)
 = _ , redo , Context1-∥R* (ceval e) qs∥Rds ,
   _ , _ , _ , deloopˢ pE′ , deloopˢ qE′ , E-view′

DPG-E-view{_}{_}{r₁}{r₂} (depar₁ pE) (depar₁ qE) (dcpar₂{C = C} pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (depar₁ pE) (depar₁ qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with wrap-rho redo-sub pE qE E-view-sub
               (epar₁ (C ⟦ r₂ ∥ r₁ ⟧c))
               (depar₁ pE) (depar₁ qE)
... | (redo′ , E-view′)
 = _ , redo′ , ∥Rn (Context1-∥R (ceval (epar₂ _)) (∥Rstep pC)) ∥R0 ,
   _ , _ , _ , depar₁ pE , depar₁ qE , E-view′

DPG-E-view{_}{_}{r₁}{r₂} (depar₂ pE) (depar₂ qE) (dcpar₁{C = C} pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (depar₂ pE) (depar₂ qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with wrap-rho redo-sub pE qE E-view-sub
               (epar₂ (C ⟦ r₂ ∥ r₁ ⟧c))
               (depar₂ pE) (depar₂ qE)
... | (redo′ , E-view′)
 = _ , redo′ , ∥Rn (Context1-∥R (ceval (epar₁ _)) (∥Rstep pC)) ∥R0 ,
   _ , _ , _ , depar₂ pE , depar₂ qE , E-view′

DPG-E-view{_}{_}{r₁}{r₂} (deseq pE) (deseq qE) (dcseq₂{C = C} pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (deseq pE) (deseq qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with wrap-rho redo-sub pE qE E-view-sub
               (eseq (C ⟦ r₂ ∥ r₁ ⟧c))
               (deseq pE) (deseq qE)
... | (redo′ , E-view′)
 = _ , redo′ , ∥Rn (Context1-∥R (cseq₂ _) (∥Rstep pC)) ∥R0 ,
   _ , _ , _ , deseq pE , deseq qE , E-view′

DPG-E-view{_}{_}{r₁}{r₂} (deloopˢ pE) (deloopˢ qE) (dcloopˢ₂{C = C} pC) psn⟶₁q E-view
 with unwrap-rho psn⟶₁q (deloopˢ pE) (deloopˢ qE) pE qE E-view
... | (redo-sub , E-view-sub)
 with wrap-rho redo-sub pE qE E-view-sub
               (eloopˢ (C ⟦ r₂ ∥ r₁ ⟧c))
               (deloopˢ pE) (deloopˢ qE)
... | (redo′ , E-view′)
 = _ , redo′ , ∥Rn (Context1-∥R (cloopˢ₂ _) (∥Rstep pC)) ∥R0 ,
   _ , _ , _ , deloopˢ pE , deloopˢ qE , E-view′
