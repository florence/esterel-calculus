module sn-calculus-compatconf.split where

open import sn-calculus-compatconf.base

open import sn-calculus
open import utility renaming (_U̬_ to _∪_)
open import context-properties
  using (unwrap-rho ; wrap-rho ; ->E-view ; plugc ; unplugc)

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.Binding
open import Esterel.Lang.CanFunction
  using (Can ; Canₛ ; Canₛₕ ; Canₖ ; module CodeSet)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
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
  using (_⊎_ ; inj₁ ; inj₂ ; map)
open import Function using (_∘_ ; id ; _∋_)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open ->E-view

open EvaluationContext1
open _≐_⟦_⟧e
open Context1
open _≐_⟦_⟧c

open ListSet Data.Nat._≟_

{-
Base case where (E, C) = ([], _∷_).

  Simply switch the reductions. Note that since E = [], the rmerge rule
  at LHS is actually  ρθ.ρθ'.qin sn⟶₁ ρ(θ←θ').qin.  Since C = _∷_, the
  reduction at RHS must go inside ρθ' so it's easy to handle.

     p
  ρθ. E⟦ qin ⟧   -- sn⟶₁ ->    ρθq. E⟦ qo ⟧
 (ρθ) E⟦C⟦rin⟧⟧   -- sn⟶₁ ->   (ρθ) E⟦C⟦ro⟧⟧
-}
1-steplρ-E-view-ecsplit : ∀{E C p qin q qo rin r ro θ θq BV FV A Aq} →
  {ρθ·psn⟶₁ρθq·q  :  ρ⟨ θ , A ⟩· p sn⟶₁ ρ⟨ θq , Aq ⟩· q} →
  CorrectBinding p BV FV →
  two-roads-diverged E C →

  (p≐E⟦qin⟧  :  p ≐ E ⟦ qin ⟧e) →
  (q≐E⟦qo⟧   :  q ≐ E ⟦ qo ⟧e) →
  ->E-view  ρθ·psn⟶₁ρθq·q  p≐E⟦qin⟧  q≐E⟦qo⟧ →

  (p≐E⟦rin⟧  :  p ≐ C ⟦ rin ⟧c) →
  (r≐E⟦ro⟧   :  r ≐ C ⟦ ro ⟧c) →
  (rinsn⟶₁ro  :  rin sn⟶₁ ro) →

  ∃ λ po →
    -- LHS: 0 or 1 step (ρθ) C⟦qo⟧ sn⟶* (ρθ) C⟦poq⟧ reduction inside ρθ [ ]
    (q ≡ po ⊎ q sn⟶ po)
    ×
    -- RHS: ρθ. E'⟦ro'⟧ sn⟶₁ ρθq. E'⟦por⟧
    Σ (EvaluationContext × Term × Term) λ { (E' , ro' , por) →
      Σ[ r≐E'⟦ro'⟧      ∈  r  ≐ E' ⟦ ro' ⟧e ]
      Σ[ po≐E'⟦por⟧     ∈  po ≐ E' ⟦ por ⟧e ]
      Σ[ ρθ·rsn⟶₁ρθq·po  ∈  ρ⟨ θ , A ⟩· r sn⟶₁ ρ⟨ θq , Aq ⟩· po ]
        ->E-view  ρθ·rsn⟶₁ρθq·po  r≐E'⟦ro'⟧  po≐E'⟦por⟧
      }

1-steplρ-E-view-ecsplit cb divout-disjoint dehole dehole
  vemit () r≐C⟦ro⟧ rinsn⟶₁ro
1-steplρ-E-view-ecsplit cb divout-disjoint dehole dehole
  vset-shared-value-old () r≐C⟦ro⟧ rinsn⟶₁ro
1-steplρ-E-view-ecsplit cb divout-disjoint dehole dehole
  vset-shared-value-new () r≐C⟦ro⟧ rinsn⟶₁ro
1-steplρ-E-view-ecsplit cb divout-disjoint dehole dehole
  vset-var () r≐C⟦ro⟧ rinsn⟶₁ro

1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ρθ·psn⟶₁ρθq·q} cb
  divout-disjoint dehole dehole vmerge
  ρθp≐C⟦rin⟧ ρθr≐C⟦ro⟧ rinsn⟶₁ro
  with ρθp≐C⟦rin⟧ | ρθr≐C⟦ro⟧
... | dcenv p≐C⟦rin⟧ | dcenv r≐C⟦ro⟧  with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ p≐C⟦rin⟧ rinsn⟶₁ro) ,′
   _ , dehole , dehole , rmerge dehole , vmerge


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ris-present {_} {S} S∈ θS≡present dehole} cb
  divout-disjoint dehole dehole vis-present
  (dcpresent₁ p≐C⟦rin⟧) (dcpresent₁ r≐C⟦ro⟧) rinsn⟶₁ro with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ p≐C⟦rin⟧ rinsn⟶₁ro) ,′
   _ , dehole , dehole , ris-present {_} {S} S∈ θS≡present dehole , vis-present


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ris-present {_} {S} S∈ θS≡present dehole} cb
  divout-disjoint dehole dehole vis-present
  (dcpresent₂ p≐C⟦rin⟧) (dcpresent₂ r≐C⟦ro⟧) rinsn⟶₁ro =
  _ , inj₁ refl ,′
  _ , dehole , dehole , ris-present {_} {S} S∈ θS≡present dehole , vis-present


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ris-absent {_} {S} S∈ θS≡absent dehole} cb
  divout-disjoint dehole dehole vis-absent
  (dcpresent₁ p≐C⟦rin⟧) (dcpresent₁ r≐C⟦ro⟧) rinsn⟶₁ro =
  _ , inj₁ refl ,′
  _ , dehole , dehole , ris-absent {_} {S} S∈ θS≡absent dehole , vis-absent


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ris-absent {_} {S} S∈ θS≡absent dehole} cb
  divout-disjoint dehole dehole vis-absent
  (dcpresent₂ p≐C⟦rin⟧) (dcpresent₂ r≐C⟦ro⟧) rinsn⟶₁ro with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ p≐C⟦rin⟧ rinsn⟶₁ro) ,′
   _ , dehole , dehole , ris-absent {_} {S} S∈ θS≡absent dehole , vis-absent


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = rraise-shared {_} {_} {s} _ _} cb
  divout-disjoint dehole dehole vraise-shared
  (dcshared p≐C⟦rin⟧) (dcshared r≐C⟦ro⟧) rinsn⟶₁ro with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ (dcenv p≐C⟦rin⟧) rinsn⟶₁ro) ,′
   _ , dehole , dehole , rraise-shared {_} {_} {s} _ _ , vraise-shared


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = rraise-var {_} {_} {x} _ _} cb
  divout-disjoint dehole dehole vraise-var
  (dcvar p≐C⟦rin⟧) (dcvar r≐C⟦ro⟧) rinsn⟶₁ro with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ (dcenv p≐C⟦rin⟧) rinsn⟶₁ro) ,′
   _ , dehole , dehole , rraise-var {_} {_} {x} _ _ , vraise-var


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = rif-false {x = x} x∈ θx≡zero dehole} cb
  divout-disjoint dehole dehole vif-false
  (dcif₁ p≐C⟦rin⟧) (dcif₁ r≐C⟦ro⟧) rinsn⟶₁ro =
  _ , inj₁ refl ,′
  _ , dehole , dehole , rif-false {x = x} x∈ θx≡zero dehole , vif-false


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = rif-false {x = x} x∈ θx≡zero dehole} cb
  divout-disjoint dehole dehole vif-false
  (dcif₂ p≐C⟦rin⟧) (dcif₂ r≐C⟦ro⟧) rinsn⟶₁ro with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ p≐C⟦rin⟧ rinsn⟶₁ro) ,′
   _ , dehole , dehole , rif-false {x = x} x∈ θx≡zero dehole , vif-false


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = rif-true {θ} {x = x} x∈ θx≡suc dehole} cb
  divout-disjoint dehole dehole vif-true
  (dcif₁ p≐C⟦rin⟧) (dcif₁ r≐C⟦ro⟧) rinsn⟶₁ro with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ p≐C⟦rin⟧ rinsn⟶₁ro) ,′
   _ , dehole , dehole , rif-true {x = x} x∈ θx≡suc dehole , vif-true


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = rif-true {x = x} x∈ θx≡suc dehole} cb
  divout-disjoint dehole dehole vif-true
  (dcif₂ p≐C⟦rin⟧) (dcif₂ r≐C⟦ro⟧) rinsn⟶₁ro =
  _ , inj₁ refl ,′
  _ , dehole , dehole , rif-true {x = x} x∈ θx≡suc dehole , vif-true




1-steplρ-E-view-ecsplit cb divpar-split₁
  (depar₁ p₁≐E⟦qin⟧) (depar₁ q≐E⟦qo⟧) e-view
  (dcpar₂ p≐C⟦rin⟧) (dcpar₂ r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho _ _ _ p₁≐E⟦qin⟧ q≐E⟦qo⟧ e-view
... | ρθ·p₁sn⟶₁ρθq·q , e-view' with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ (dcpar₂ p≐C⟦rin⟧) rinsn⟶₁ro) ,′
   _ , _ , _ , wrap-rho ρθ·p₁sn⟶₁ρθq·q _ _ e-view' _ (depar₁ p₁≐E⟦qin⟧) (depar₁ q≐E⟦qo⟧)


1-steplρ-E-view-ecsplit cb divpar-split₂
  (depar₂ p₂≐E⟦qin⟧) (depar₂ q≐E⟦qo⟧) e-view
  (dcpar₁ p≐C⟦rin⟧) (dcpar₁ r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho _ _ _ p₂≐E⟦qin⟧ q≐E⟦qo⟧ e-view
... | ρθ·p₂sn⟶₁ρθq·q , e-view' with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ (dcpar₁ p≐C⟦rin⟧) rinsn⟶₁ro) ,′
   _ , _ , _ , wrap-rho ρθ·p₂sn⟶₁ρθq·q _ _ e-view' _ (depar₂ p₂≐E⟦qin⟧) (depar₂ q≐E⟦qo⟧)


1-steplρ-E-view-ecsplit cb divseq-split
  (deseq p₁≐E⟦qin⟧) (deseq q≐E⟦qo⟧) e-view
  (dcseq₂ p≐C⟦rin⟧) (dcseq₂ r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho _ _ _ p₁≐E⟦qin⟧ q≐E⟦qo⟧ e-view
... | ρθ·p₁sn⟶₁ρθq·q , e-view' with sym (unplugc r≐C⟦ro⟧)
... | refl
  = _ , inj₂ (rcontext _ (dcseq₂ p≐C⟦rin⟧) rinsn⟶₁ro) ,′
    _ , _ , _ , wrap-rho ρθ·p₁sn⟶₁ρθq·q _ _ e-view' _ (deseq p₁≐E⟦qin⟧) (deseq q≐E⟦qo⟧)


1-steplρ-E-view-ecsplit cb divloopˢ-split
  (deloopˢ p₁≐E⟦qin⟧) (deloopˢ q≐E⟦qo⟧) e-view
  (dcloopˢ₂ p≐C⟦rin⟧) (dcloopˢ₂ r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho _ _ _ p₁≐E⟦qin⟧ q≐E⟦qo⟧ e-view
... | ρθ·p₁sn⟶₁ρθq·q , e-view' with sym (unplugc r≐C⟦ro⟧)
... | refl
 = _ , inj₂ (rcontext _ (dcloopˢ₂ p≐C⟦rin⟧) rinsn⟶₁ro) ,′
   _ , _ , _ , wrap-rho ρθ·p₁sn⟶₁ρθq·q _ _ e-view' _ (deloopˢ p₁≐E⟦qin⟧) (deloopˢ q≐E⟦qo⟧)


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBpar cbp cbq _ _ _ _) (divin div)
  (depar₁ p≐E⟦qin⟧) (depar₁ q≐E⟦qo⟧) e-view-E₁
  (dcpar₁ p≐C⟦rin⟧) (dcpar₁ r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (depar₁ p≐E⟦qin⟧) (depar₁ q≐E⟦qo⟧) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view)
  with 1-steplρ-E-view-ecsplit cbp div p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro
... | _ , qsn⟶po? , _ , r≐E'⟦qin⟧ , po≐E'⟦qo⟧ , _ , e-view' =
  _ , map (cong _) (Context1-sn⟶ (ceval (epar₁ _))) qsn⟶po? ,′
  _ , depar₁ r≐E'⟦qin⟧ , depar₁ po≐E'⟦qo⟧ , wrap-rho _ _ _ e-view' _ _ _


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBpar cbp cbq _ _ _ _) (divin div)
  (depar₂ p≐E⟦qin⟧) (depar₂ q≐E⟦qo⟧) e-view-E₁
  (dcpar₂ p≐C⟦rin⟧) (dcpar₂ r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (depar₂ p≐E⟦qin⟧) (depar₂ q≐E⟦qo⟧) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view)
  with 1-steplρ-E-view-ecsplit cbq div p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro
... | _ , qsn⟶po? , _ , r≐E'⟦qin⟧ , po≐E'⟦qo⟧ , _ , e-view' =
  _ , map (cong _) (Context1-sn⟶ (ceval (epar₂ _))) qsn⟶po? ,′
  _ , depar₂ r≐E'⟦qin⟧ , depar₂ po≐E'⟦qo⟧ , wrap-rho _ _ _ e-view' _ _ _


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBseq cbp cbq _) (divin div)
  (deseq p≐E⟦qin⟧) (deseq q≐E⟦qo⟧) e-view-E₁
  (dcseq₁ p≐C⟦rin⟧) (dcseq₁ r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (deseq p≐E⟦qin⟧) (deseq q≐E⟦qo⟧) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view)
  with 1-steplρ-E-view-ecsplit cbp div p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro
... | _ , qsn⟶po? , _ , r≐E'⟦qin⟧ , po≐E'⟦qo⟧ , _ , e-view' =
  _ , map (cong _) (Context1-sn⟶ (ceval (eseq _))) qsn⟶po? ,′
  _ , deseq r≐E'⟦qin⟧ , deseq po≐E'⟦qo⟧ , wrap-rho _ _ _ e-view' _ _ _


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBloopˢ cbp cbq _ _) (divin div)
  (deloopˢ p≐E⟦qin⟧) (deloopˢ q≐E⟦qo⟧) e-view-E₁
  (dcloopˢ₁ p≐C⟦rin⟧) (dcloopˢ₁ r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (deloopˢ p≐E⟦qin⟧) (deloopˢ q≐E⟦qo⟧) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view)
  with 1-steplρ-E-view-ecsplit cbp div p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro
... | _ , qsn⟶po? , _ , r≐E'⟦qin⟧ , po≐E'⟦qo⟧ , _ , e-view' =
  _ , map (cong _) (Context1-sn⟶ (ceval (eloopˢ _))) qsn⟶po? ,′
  _ , deloopˢ r≐E'⟦qin⟧ , deloopˢ po≐E'⟦qo⟧ , wrap-rho _ _ _ e-view' _ _ _


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBsusp cb' _) (divin div)
  (desuspend p≐E⟦qin⟧) (desuspend q≐E⟦qo⟧) e-view-E₁
  (dcsuspend p≐C⟦rin⟧) (dcsuspend r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (desuspend p≐E⟦qin⟧) (desuspend q≐E⟦qo⟧) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view)
  with 1-steplρ-E-view-ecsplit cb' div p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro
... | _ , qsn⟶po? , _ , r≐E'⟦qin⟧ , po≐E'⟦qo⟧ , _ , e-view' =
  _ , map (cong _) (Context1-sn⟶ (ceval (esuspend _))) qsn⟶po? ,′
  _ , desuspend r≐E'⟦qin⟧ , desuspend po≐E'⟦qo⟧ , wrap-rho _ _ _ e-view' _ _ _


1-steplρ-E-view-ecsplit {ρθ·psn⟶₁ρθq·q = ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧}
  cb@(CBtrap cb') (divin div)
  (detrap p≐E⟦qin⟧) (detrap q≐E⟦qo⟧) e-view-E₁
  (dctrap p≐C⟦rin⟧) (dctrap r≐C⟦ro⟧) rinsn⟶₁ro
  with unwrap-rho ρθ·E₁⟦p⟧sn⟶₁ρθq·E₁⟦q⟧ (detrap p≐E⟦qin⟧) (detrap q≐E⟦qo⟧) p≐E⟦qin⟧ q≐E⟦qo⟧ e-view-E₁
... | (ρθ·psn⟶₁ρθq·q , e-view)
  with 1-steplρ-E-view-ecsplit cb' div p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro
... | _ , qsn⟶po? , _ , r≐E'⟦qin⟧ , po≐E'⟦qo⟧ , _ , e-view' =
  _ , map (cong _) (Context1-sn⟶ (ceval etrap)) qsn⟶po? ,′
  _ , detrap r≐E'⟦qin⟧ , detrap po≐E'⟦qo⟧ , wrap-rho _ _ _ e-view' _ _ _
