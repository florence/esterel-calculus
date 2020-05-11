module sn-calculus-compatconf.same where

open import sn-calculus-compatconf.base

open import sn-calculus
open import sn-calculus-confluence.helper
  using (ready-irr-on-irr-θʳ)
open import utility renaming (_U̬_ to _∪_)
open import context-properties
  using (get-view ; wrap-rho
       ; ->E-view ; ->pot-view ; wrap-rho-pot' ; unwrap-rho
       )

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.Binding
open import Esterel.Lang.CanFunction
  using (Can ; Canₛ ; Canₛₕ ; Canₖ ; Canθ ; Canθₛ ; Canθₛₕ ; module CodeSet)
open import Esterel.Lang.CanFunction.Properties
  using (canθₛ-mergeʳ ; canθₛₕ-mergeʳ)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Context.Properties
  using (unplug ; unplugc ; plug ; plugc ; unplug-eq ; ⟦⟧c-to-⟦⟧e)
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
  using (_≡_ ; refl ; sym ; cong ; trans ; subst ; subst₂ ; module ≡-Reasoning)
open import Data.Bool
  using (Bool ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; _∷_ ; [] ; _++_ ; map)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using ()
  renaming ( ++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ )
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; zero ; suc ; _+_) renaming (_⊔_ to _⊔ℕ_)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; _,′_ ; proj₁ ; proj₂ ; _×_ ; ∃)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_ ; id ; _∋_ ; _$_)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open ->E-view
open ->pot-view

open EvaluationContext1
open _≐_⟦_⟧e
open Context1
open _≐_⟦_⟧c

open ListSet Data.Nat._≟_

open ≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)


{-
Modified proof from the old E-lift C-any confluence lemma.
Basically this is arbitrary multi-wrap-rho given the correct binding
of p: from a reduction (where E ⟦ ρ θ · qin ⟧ has correct binding)

    E ⟦ ρ θ · qin ⟧ sn⟶₁ E ⟦ ρ θr · ro ⟧

construct the E-wrapped reduction

    ρ θ · E ⟦ qin ⟧ sn⟶₁ ρ θr · E ⟦ ro ⟧
          ( = q )             ( = r )
-}
conf-lift-lemma : ∀ {E qin ro p q θ θr BV FV A Ar} →
  CorrectBinding p BV FV →

  p ≐ E ⟦ ρ⟨ θ , A ⟩· qin ⟧e →
  q ≐ E ⟦ qin ⟧e →

  ρ⟨ θ , A ⟩· qin sn⟶₁ ρ⟨ θr , Ar ⟩· ro →

  ∃ λ r →
    r ≐ E ⟦ ro ⟧e ×
    ρ⟨ θ , A ⟩· q sn⟶₁ ρ⟨ θr , Ar ⟩· r

conf-lift-lemma cb dehole dehole ρθ·pinsn⟶₁ρθq·qin = _ , dehole , ρθ·pinsn⟶₁ρθq·qin 


conf-lift-lemma cb@(CBpar cbp' cbq' _ _ _ _) (depar₁ p≐E⟦ρθ·pin⟧) (depar₁ r≐E⟦pin⟧) ρθ·pinsn⟶₁ρθq·qin
  with conf-lift-lemma cbp' p≐E⟦ρθ·pin⟧ r≐E⟦pin⟧ ρθ·pinsn⟶₁ρθq·qin
... | q , q≐E⟦qin⟧ , ρθ·rsn⟶₁ρθq·q
  with get-view ρθ·rsn⟶₁ρθq·q
... | inj₁ (E' , pin' , qin' , r≐E'⟦pin'⟧ , q≐E'⟦qin'⟧ , e-view) =
  _ , depar₁ q≐E⟦qin⟧ ,′
  proj₁ (wrap-rho ρθ·rsn⟶₁ρθq·q r≐E'⟦pin'⟧ q≐E'⟦qin'⟧ e-view _
          (depar₁ r≐E'⟦pin'⟧) (depar₁ q≐E'⟦qin'⟧))
... | inj₂ (refl , refl , pot) with wrap-rho-pot' (depar₁ p≐E⟦ρθ·pin⟧) cb ρθ·rsn⟶₁ρθq·q pot
... | _ , depar₁ dehole , ρθ·p'∥tsn⟶₁ρθq·p'∥t , pot' = -- need pattern matching for LHS of sn⟶₁
  _ , depar₁ q≐E⟦qin⟧ ,′
    ρθ·p'∥tsn⟶₁ρθq·p'∥t


conf-lift-lemma cb@(CBpar cbp' cbq' _ _ _ _) (depar₂ p≐E⟦ρθ·pin⟧) (depar₂ r≐E⟦pin⟧) ρθ·pinsn⟶₁ρθq·qin
  with conf-lift-lemma cbq' p≐E⟦ρθ·pin⟧ r≐E⟦pin⟧ ρθ·pinsn⟶₁ρθq·qin
... | q , q≐E⟦qin⟧ , ρθ·rsn⟶₁ρθq·q
  with get-view ρθ·rsn⟶₁ρθq·q
... | inj₁ (E' , pin' , qin' , r≐E'⟦pin'⟧ , q≐E'⟦qin'⟧ , e-view) =
  _ , depar₂ q≐E⟦qin⟧ ,′
  proj₁ (wrap-rho ρθ·rsn⟶₁ρθq·q r≐E'⟦pin'⟧ q≐E'⟦qin'⟧ e-view _
          (depar₂ r≐E'⟦pin'⟧) (depar₂ q≐E'⟦qin'⟧))
... | inj₂ (refl , refl , pot) with wrap-rho-pot' (depar₂ p≐E⟦ρθ·pin⟧) cb ρθ·rsn⟶₁ρθq·q pot
... | _ , depar₂ dehole , ρθ·t∥q'sn⟶₁ρθq·t∥q' , pot' =
  _ , depar₂ q≐E⟦qin⟧ ,′
    ρθ·t∥q'sn⟶₁ρθq·t∥q'


conf-lift-lemma cb@(CBseq cbp' cbq' _) (deseq p≐E⟦ρθ·pin⟧) (deseq r≐E⟦pin⟧) ρθ·pinsn⟶₁ρθq·qin
  with conf-lift-lemma cbp' p≐E⟦ρθ·pin⟧ r≐E⟦pin⟧ ρθ·pinsn⟶₁ρθq·qin
... | q , q≐E⟦qin⟧ , ρθ·rsn⟶₁ρθq·q
  with get-view ρθ·rsn⟶₁ρθq·q
... | inj₁ (E' , pin' , qin' , r≐E'⟦pin'⟧ , q≐E'⟦qin'⟧ , e-view) =
  _ , deseq q≐E⟦qin⟧ ,′
  proj₁ (wrap-rho ρθ·rsn⟶₁ρθq·q r≐E'⟦pin'⟧ q≐E'⟦qin'⟧ e-view _
          (deseq r≐E'⟦pin'⟧) (deseq q≐E'⟦qin'⟧))
... | inj₂ (refl , refl , pot) with wrap-rho-pot' (deseq p≐E⟦ρθ·pin⟧) cb ρθ·rsn⟶₁ρθq·q pot
... | _ , deseq dehole , ρθ·t>>q'sn⟶₁ρθq·t>>q' , pot' =
  _ , deseq q≐E⟦qin⟧ ,′
    ρθ·t>>q'sn⟶₁ρθq·t>>q'


conf-lift-lemma cb@(CBloopˢ cbp' cbq' _ _) (deloopˢ p≐E⟦ρθ·pin⟧) (deloopˢ r≐E⟦pin⟧) ρθ·pinsn⟶₁ρθq·qin
  with conf-lift-lemma cbp' p≐E⟦ρθ·pin⟧ r≐E⟦pin⟧ ρθ·pinsn⟶₁ρθq·qin
... | q , q≐E⟦qin⟧ , ρθ·rsn⟶₁ρθq·q
  with get-view ρθ·rsn⟶₁ρθq·q
... | inj₁ (E' , pin' , qin' , r≐E'⟦pin'⟧ , q≐E'⟦qin'⟧ , e-view) =
  _ , deloopˢ q≐E⟦qin⟧ ,′
  proj₁ (wrap-rho ρθ·rsn⟶₁ρθq·q r≐E'⟦pin'⟧ q≐E'⟦qin'⟧ e-view _
          (deloopˢ r≐E'⟦pin'⟧) (deloopˢ q≐E'⟦qin'⟧))
... | inj₂ (refl , refl , pot) with wrap-rho-pot' (deloopˢ p≐E⟦ρθ·pin⟧) cb ρθ·rsn⟶₁ρθq·q pot
... | _ , deloopˢ dehole , ρθ·t>>q'sn⟶₁ρθq·t>>q' , pot' =
  _ , deloopˢ q≐E⟦qin⟧ ,′
    ρθ·t>>q'sn⟶₁ρθq·t>>q'


conf-lift-lemma cb@(CBsusp cb' _) (desuspend p≐E⟦ρθ·pin⟧) (desuspend r≐E⟦pin⟧) ρθ·pinsn⟶₁ρθq·qin
  with conf-lift-lemma cb' p≐E⟦ρθ·pin⟧ r≐E⟦pin⟧ ρθ·pinsn⟶₁ρθq·qin
... | q , q≐E⟦qin⟧ , ρθ·rsn⟶₁ρθq·q
  with get-view ρθ·rsn⟶₁ρθq·q
... | inj₁ (E' , pin' , qin' , r≐E'⟦pin'⟧ , q≐E'⟦qin'⟧ , e-view) =
  _ , desuspend q≐E⟦qin⟧ ,′
  proj₁ (wrap-rho ρθ·rsn⟶₁ρθq·q r≐E'⟦pin'⟧ q≐E'⟦qin'⟧ e-view _
          (desuspend r≐E'⟦pin'⟧) (desuspend q≐E'⟦qin'⟧))
... | inj₂ (refl , refl , pot) with wrap-rho-pot' (desuspend p≐E⟦ρθ·pin⟧) cb ρθ·rsn⟶₁ρθq·q pot
... | _ , desuspend dehole , ρθ·susptsn⟶₁ρθq·suspt , pot' =
  _ , desuspend q≐E⟦qin⟧ ,′
    ρθ·susptsn⟶₁ρθq·suspt


conf-lift-lemma cb@(CBtrap cb') (detrap p≐E⟦ρθ·pin⟧) (detrap r≐E⟦pin⟧) ρθ·pinsn⟶₁ρθq·qin
  with conf-lift-lemma cb' p≐E⟦ρθ·pin⟧ r≐E⟦pin⟧ ρθ·pinsn⟶₁ρθq·qin
... | q , q≐E⟦qin⟧ , ρθ·rsn⟶₁ρθq·q
  with get-view ρθ·rsn⟶₁ρθq·q
... | inj₁ (E' , pin' , qin' , r≐E'⟦pin'⟧ , q≐E'⟦qin'⟧ , e-view) =
  _ , detrap q≐E⟦qin⟧ ,′
  proj₁ (wrap-rho ρθ·rsn⟶₁ρθq·q r≐E'⟦pin'⟧ q≐E'⟦qin'⟧ e-view _
          (detrap r≐E'⟦pin'⟧) (detrap q≐E'⟦qin'⟧))
... | inj₂ (refl , refl , pot) with wrap-rho-pot' (detrap p≐E⟦ρθ·pin⟧) cb ρθ·rsn⟶₁ρθq·q pot
... | _ , detrap dehole , ρθ·traptsn⟶₁ρθq·trapt , pot' =
  _ , detrap q≐E⟦qin⟧ ,′
    ρθ·traptsn⟶₁ρθq·trapt


{-
Base case where (E, C) = ([], []).

  The most complicated case where LHS is  ρθ.ρθ'.qin sn⟶₁ ρ(θ←θ').qin   (qin = ρθ'.rin)
  and RHS is  (ρθ.) ρθ'.rin sn⟶₁ (ρθ.) ρθr.ro,  i.e. arbitrary ->E-view and ->pot-view.

     p
  ρθ. E⟦ρθ'.qin⟧   -- sn⟶₁ ->    ρ(θ←θ'). E⟦qin⟧
 (ρθ) E⟦ρθ'.qin⟧   -- sn⟶₁ ->   (ρθ)      E⟦ρθr.ro⟧
-}
1-steplρ-E-view-ecsame : ∀{E p qin q qo rin r ro θ θ←θ' BV FV A A⊓A'} →
  {ρθ·psn⟶₁ρθ←θ'·q  :  ρ⟨ θ , A ⟩· p sn⟶₁ ρ⟨ θ←θ' , A⊓A' ⟩· q} →
  CorrectBinding p BV FV →

  (p≐E⟦qin⟧  :  p ≐ E ⟦ qin ⟧e) →
  (q≐E⟦qo⟧   :  q ≐ E ⟦ qo ⟧e) →
  ->E-view  ρθ·psn⟶₁ρθ←θ'·q  p≐E⟦qin⟧  q≐E⟦qo⟧ →

  (p≐E⟦rin⟧  :  p ≐ (map ceval E) ⟦ rin ⟧c) →
  (r≐E⟦ro⟧   :  r ≐ (map ceval E) ⟦ ro ⟧c) →
  -- rinsn⟶₁ro can only be  (ρ⟨ θ' , A' ⟩· qin) sn⟶₁ (ρ⟨ θr , Ar ⟩· ro)
  (rinsn⟶₁ro  :  rin sn⟶₁ ro) →

  Σ ((Env × Ctrl × Term) × EvaluationContext × Term × Term) λ { ((θo , Ao , po) , E' , roin , poin) →
    ρ⟨ θ←θ' , A⊓A' ⟩· q sn⟶₁ ρ⟨ θo , Ao ⟩· po ×
    Σ[ ρθ·rsn⟶₁ρθo·po  ∈  ρ⟨ θ , A ⟩·    r sn⟶₁ ρ⟨ θo , Ao ⟩· po ]
    Σ[ r≐E'⟦roin⟧     ∈  r ≐ E' ⟦ roin ⟧e ]
    Σ[ po≐E'⟦poin⟧    ∈  po ≐ E' ⟦ poin ⟧e ]
      ->E-view  ρθ·rsn⟶₁ρθo·po  r≐E'⟦roin⟧  po≐E'⟦poin⟧
    }

1-steplρ-E-view-ecsame cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ e-view p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro
  with unplug-eq p≐E⟦ρθ'·qin⟧ (⟦⟧c-to-⟦⟧e p≐C⟦rin⟧)
1-steplρ-E-view-ecsame cb _ _ vis-present           _ _ () | refl
1-steplρ-E-view-ecsame cb _ _ vis-absent            _ _ () | refl
1-steplρ-E-view-ecsame cb _ _ vemit                 _ _ () | refl
1-steplρ-E-view-ecsame cb _ _ vraise-shared         _ _ () | refl
1-steplρ-E-view-ecsame cb _ _ vset-shared-value-old _ _ () | refl
1-steplρ-E-view-ecsame cb _ _ vset-shared-value-new _ _ () | refl
1-steplρ-E-view-ecsame cb _ _ vraise-var            _ _ () | refl
1-steplρ-E-view-ecsame cb _ _ vset-var              _ _ () | refl
1-steplρ-E-view-ecsame cb _ _ vif-false             _ _ () | refl
1-steplρ-E-view-ecsame cb _ _ vif-true              _ _ () | refl


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} .p≐E⟦ρθ'·qin⟧}
  cb
  p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge
  p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl
  with ρ-stays-ρ-sn⟶₁ rinsn⟶₁ro
... | θr , roin , Ar , refl
  with conf-lift-lemma cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ rinsn⟶₁ro
... | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r' -- q ≐ E ⟦ qin ⟧
  with get-view ρθ'·qsn⟶₁ρθr·r'


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , .q≐E'⟦present⟧ , r'≐E⟦roin'⟧ ,
          vis-present {.θ'} {S} {E = .E'} {S∈Domθ'} {θ'S≡present} {q≐E'⟦present⟧}) =
  _ ,
      (ris-present {S = S}
        (Env.sig-←-monoʳ S θr θ S∈Domθ')
        (trans
          (SigMap.get-U-right-irr-m {_} S (Env.sig θ) (Env.sig θr)
            (Env.sig-←-monoʳ S θr θ S∈Domθ') S∈Domθ')
          θ'S≡present)
        q≐E'⟦present⟧) ,′
      (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge))


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , q≐E⟦qo'⟧ , r'≐E⟦roin'⟧ ,
          vis-absent {.θ'} {S} {E = .E'} {S∈Domθ'} {θ'S≡absent} {q≐E'⟦absent⟧}) =
  _ ,
      (ris-absent {S = S}
        (Env.sig-←-monoʳ S θr θ S∈Domθ')
        (trans
          (SigMap.get-U-right-irr-m {_} S (Env.sig θ) (Env.sig θr)
            (Env.sig-←-monoʳ S θr θ S∈Domθ') S∈Domθ')
          θ'S≡absent)
        q≐E'⟦absent⟧) ,′
      (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge))


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , .q≐E'⟦if⟧ , r'≐E⟦roin'⟧ ,
          vif-false {x = x} {.E'} {x∈Domθ'} {θ'x≡zero} {q≐E'⟦if⟧}) =
  _ ,
      (rif-false {x = x}
        (Env.seq-←-monoʳ x θr θ x∈Domθ')
        (trans
          (VarMap.get-U-right-irr-m {_} x (Env.var θ) (Env.var θr)
            (Env.seq-←-monoʳ x θr θ x∈Domθ') x∈Domθ')
          θ'x≡zero)
        q≐E'⟦if⟧) ,′
      (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge))


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , .q≐E'⟦if⟧ , r'≐E⟦roin'⟧ ,
          vif-true {x = x} {.E'} {_} {x∈Domθ'} {θ'x≡suc} {q≐E'⟦if⟧}) =
  _ ,
      (rif-true {x = x}
        (Env.seq-←-monoʳ x θr θ x∈Domθ')
        (trans
          (Env.var-vals-←-right-irr' x θ θr x∈Domθ' (Env.seq-←-monoʳ x θr θ x∈Domθ'))
          θ'x≡suc)
        q≐E'⟦if⟧) ,′
      (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge))


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , .q≐E'⟦shared⟧ , r'≐E⟦roin'⟧ ,
          vraise-shared {s = s} {E = .E'} {e'} {q≐E'⟦shared⟧})
  with ready-irr-on-irr-θʳ θ e'
... | e'' , δe'≡δe'' rewrite δe'≡δe'' =
  _ ,
      rraise-shared e'' q≐E'⟦shared⟧ ,′
      (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge))


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , .q≐E'⟦var⟧ , r'≐E⟦roin'⟧ ,
            vraise-var {E = .E'} {e'} {q≐E'⟦var⟧})
  with ready-irr-on-irr-θʳ θ e'
... | e'' , δe'≡δe'' rewrite δe'≡δe'' =
  _ ,
      rraise-var e'' q≐E'⟦var⟧ ,′
      (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge))


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} {A₁ = A} {.GO} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , .q≐E'⟦emit⟧ , r'≐E⟦roin'⟧ ,
            vemit {S = S} {.E'} {S∈Domθ'} {θ'S≢absent} {q≐E'⟦emit⟧}) =
  _ ,
       (subst₂ (λ θ* go → ρ⟨ (θ ← θ') , go ⟩· E ⟦ qin ⟧e sn⟶₁ ρ⟨ θ* , go ⟩· E' ⟦ nothin ⟧e)
        (begin
            Env.set-sig {S} (θ ← θ') S∈Domθ←θ' Signal.present
          ≡⟨ Env.sig-set=← (θ ← θ') S Signal.present S∈Domθ←θ' ⟩
            (θ ← θ') ← [S↦present]
          ≡⟨ sym (Env.←-assoc θ θ' [S↦present]) ⟩
            θ ← (θ' ← [S↦present])
          ≡⟨ cong (θ ←_) (sym (Env.sig-set=← θ' S Signal.present S∈Domθ')) ⟩
            θ ← (Env.set-sig {S} θ' S∈Domθ' Signal.present)
         ∎)
         (sym $ A-max-GO-≡-right A)
        (remit {θ ← θ'} {S = S} S∈Domθ←θ'
          (θ'S≢absent ∘ trans (sym ⟨θ←θ'⟩S≡θ'S))
          q≐E'⟦emit⟧))   ,′
       (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge)) 
  where
    [S↦present] = Θ SigMap.[ S ↦ Signal.present ] ShrMap.empty VarMap.empty
    S∈Domθ←θ'   = Env.sig-←-monoʳ S θ' θ S∈Domθ'
    ⟨θ←θ'⟩S≡θ'S = Env.sig-stats-←-right-irr' S θ θ' S∈Domθ' S∈Domθ←θ'


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} {A₁ = A} {.GO} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , .q≐E'⟦s⇐e⟧ , r'≐E⟦roin'⟧ ,
          vset-shared-value-old {s = s} {E = .E'} {e'} {s∈Domθ'} {θ's≡old} {q≐E'⟦s⇐e⟧})
  with ready-irr-on-irr-θʳ θ e'
... | e'' , δe'≡δe'' rewrite δe'≡δe'' =
  _ ,
       (subst₂ (λ θ* go → ρ⟨ (θ ← θ') , go ⟩· E ⟦ qin ⟧e sn⟶₁ ρ⟨ θ* , go ⟩· E' ⟦ nothin ⟧e)
        (begin
            Env.set-shr {s} (θ ← θ') s∈Domθ←θ' SharedVar.new (δ e'')
          ≡⟨ Env.shr-set=← (θ ← θ') s SharedVar.new (δ e'') s∈Domθ←θ' ⟩
            (θ ← θ') ← [s↦new,δe'']
          ≡⟨ sym (Env.←-assoc θ θ' [s↦new,δe'']) ⟩
            θ ← (θ' ← [s↦new,δe''])
          ≡⟨ cong (θ ←_) (sym (Env.shr-set=← θ' s SharedVar.new (δ e'') s∈Domθ')) ⟩
            θ ← (Env.set-shr {s} θ' s∈Domθ' SharedVar.new (δ e''))
         ∎)
         (sym $ A-max-GO-≡-right A)
        (rset-shared-value-old {θ ← θ'} e'' s∈Domθ←θ'
          (trans (Env.shr-stats-←-right-irr' s θ θ' s∈Domθ' s∈Domθ←θ') θ's≡old)
          q≐E'⟦s⇐e⟧))   ,′
       (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge)) 
 where
    [s↦new,δe''] = [s,δe-new]-env s (δ e'')
    s∈Domθ←θ'   = Env.shr-←-monoʳ s θ' θ s∈Domθ'


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E}  {A₁ = A} {.GO} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , .q≐E'⟦s⇐e⟧ , r'≐E⟦roin'⟧ ,
          vset-shared-value-new {s = s} {E = .E'} {e'} {s∈Domθ'} {θ's≡old} {q≐E'⟦s⇐e⟧})
  with ready-irr-on-irr-θʳ θ e'
... | e'' , δe'≡δe'' rewrite δe'≡δe'' =
  _ ,
       (subst₂ (λ θ* go → ρ⟨ (θ ← θ') , go ⟩· E ⟦ qin ⟧e sn⟶₁ ρ⟨ θ* , go ⟩· E' ⟦ nothin ⟧e)
        (begin
            Env.set-shr {s} (θ ← θ') s∈Domθ←θ' SharedVar.new (⟨θ←θ'⟩s + δ e'')
          ≡⟨ cong(Env.set-shr{s}(θ ← θ')s∈Domθ←θ' SharedVar.new ∘ (_+ δ e''))⟨θ←θ'⟩s≡θ's ⟩
            Env.set-shr {s} (θ ← θ') s∈Domθ←θ' SharedVar.new (θ's + δ e'')
          ≡⟨ Env.shr-set=← (θ ← θ') s SharedVar.new (θ's + δ e'') s∈Domθ←θ' ⟩
            (θ ← θ') ← [s↦new,θ's+δe'']
          ≡⟨ sym (Env.←-assoc θ θ' [s↦new,θ's+δe'']) ⟩
            θ ← (θ' ← [s↦new,θ's+δe''])
          ≡⟨ cong (θ ←_) (sym (Env.shr-set=← θ' s SharedVar.new (θ's + δ e'') s∈Domθ')) ⟩
            θ ← (Env.set-shr {s} θ' s∈Domθ' SharedVar.new (θ's + δ e''))
         ∎)
         (sym $ A-max-GO-≡-right A)
        (rset-shared-value-new {θ ← θ'} e'' s∈Domθ←θ'
          (trans (Env.shr-stats-←-right-irr' s θ θ' s∈Domθ' s∈Domθ←θ') θ's≡old)
          q≐E'⟦s⇐e⟧))  ,′
       (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge)) 
 where
    s∈Domθ←θ'   = Env.shr-←-monoʳ s θ' θ s∈Domθ'
    θ's = Env.shr-vals {s} θ' s∈Domθ'
    ⟨θ←θ'⟩s = Env.shr-vals {s} (θ ← θ') s∈Domθ←θ'
    ⟨θ←θ'⟩s≡θ's = Env.shr-vals-←-right-irr' s θ θ' s∈Domθ' s∈Domθ←θ'
    [s↦new,θ's+δe''] = [s,δe-new]-env s (θ's + δ e'')


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} {A₁ = A} {A'} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , q≐E⟦qo'⟧ , r'≐E⟦roin'⟧ ,
          vset-var {x = x} {E = .E'} {x∈Domθ'} {e'} {q≐E'⟦x≔e⟧})
  with ready-irr-on-irr-θʳ θ e'
... | e'' , δe'≡δe'' rewrite δe'≡δe'' =
  _ ,
      (subst (λ θ* → ρ⟨ (θ ← θ') , A-max A A' ⟩· E ⟦ qin ⟧e sn⟶₁ ρ⟨ θ* , A-max A A' ⟩· E' ⟦ nothin ⟧e)
        (begin
            Env.set-var {x} (θ ← θ') x∈Domθ←θ' (δ e'')
          ≡⟨ Env.seq-set=← (θ ← θ') x (δ e'') x∈Domθ←θ' ⟩
            (θ ← θ') ← [x↦δe'']
          ≡⟨ sym (Env.←-assoc θ θ' [x↦δe'']) ⟩
            θ ← (θ' ← [x↦δe''])
          ≡⟨ cong (θ ←_) (sym (Env.seq-set=← θ' x (δ e'') x∈Domθ')) ⟩
            θ ← (Env.set-var {x} θ' x∈Domθ' (δ e''))
         ∎)
        (rset-var {θ ← θ'} x∈Domθ←θ' e'' q≐E'⟦x≔e⟧)) ,′
      (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge))
 where
    [x↦δe'']  = [x,δe]-env x (δ e'')
    x∈Domθ←θ' = Env.seq-←-monoʳ x θ' θ x∈Domθ'


1-steplρ-E-view-ecsame {E} {A = A} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} {A₂ = A'} .p≐E⟦ρθ'·qin⟧}  
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | (.(θ' ← θr) , roin , .(A-max A' Ar) , refl)
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₁ (E' , qo' , roin' , q≐E⟦qo'⟧ , r'≐E⟦roin'⟧ ,
          vmerge {.θ'} {θr} {_} {.roin'} {.E'} {_} {Ar} {q≐E'⟦ρθr·roin'⟧}) =
  ((_ , (A-max A (A-max A' Ar)) , _) , _) ,
       (subst₂ (λ θ* A* → ρ⟨ (θ ← θ') , A-max A A' ⟩· E ⟦ qin ⟧e sn⟶₁ ρ⟨ θ* , A* ⟩· E' ⟦ roin' ⟧e)
         (sym (Env.←-assoc θ θ' θr))
         (sym (A-max-assoc A A' Ar))
         (rmerge {θ ← θ'} {θr} {A₁ = A-max A A'} {Ar} q≐E'⟦ρθr·roin'⟧))   ,′
       (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge)) 


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₂ (refl , refl , vabsence S S∈Domθ' θ'S≡unknown S∉canθ-θ'-q-[]) =
  _ ,
      (subst (λ θ* → ρ⟨ (θ ← θ') , _ ⟩· E ⟦ qin ⟧e sn⟶₁ ρ⟨ θ* , _ ⟩· E ⟦ qin ⟧e)
        (begin
            Env.set-sig {S} (θ ← θ') S∈Domθ←θ' Signal.absent
          ≡⟨ Env.sig-set=← (θ ← θ') S Signal.absent S∈Domθ←θ' ⟩
            (θ ← θ') ← [S↦absent]
          ≡⟨ sym (Env.←-assoc θ θ' [S↦absent]) ⟩
            θ ← (θ' ← [S↦absent])
          ≡⟨ cong (θ ←_) (sym (Env.sig-set=← θ' S Signal.absent S∈Domθ')) ⟩
            θ ← (Env.set-sig {S} θ' S∈Domθ' Signal.absent)
         ∎)
        (rabsence {θ ← θ'} {S = S} S∈Domθ←θ'
          (trans (Env.sig-stats-←-right-irr' S θ θ' S∈Domθ' S∈Domθ←θ') θ'S≡unknown)
          (λ S∈canθ-θ←θ''-q-[] →
            S∉canθ-θ'-q-[]
              (canθₛ-mergeʳ (Env.sig θ) θ' (E ⟦ qin ⟧e) Env.[]env (λ _ ())
                 S S∈canθ-θ←θ''-q-[])))) ,′
      (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge))
  where
    [S↦absent] = Θ SigMap.[ S ↦ Signal.absent ] ShrMap.empty VarMap.empty
    S∈Domθ←θ'   = Env.sig-←-monoʳ S θ' θ S∈Domθ'


1-steplρ-E-view-ecsame {E} {ρθ·psn⟶₁ρθ←θ'·q = rmerge {θ} {θ'} {_} {qin} {.E} .p≐E⟦ρθ'·qin⟧}
  cb p≐E⟦ρθ'·qin⟧ q≐E⟦qin⟧ vmerge p≐C⟦rin⟧ r≐C⟦ro⟧ rinsn⟶₁ro | refl | θr , roin , Ar , refl
  | r' , r'≐E⟦roin⟧ , ρθ'·qsn⟶₁ρθr·r'
  | inj₂ (refl , refl , vreadyness s s∈Domθ' θ's≡old⊎θ's≡new s∉canθ-θ'-q-[]) =
  _ ,
      (subst (λ θ* → ρ⟨ (θ ← θ') , _ ⟩· E ⟦ qin ⟧e sn⟶₁ ρ⟨ θ* , _ ⟩· E ⟦ qin ⟧e)
        (begin
            Env.set-shr {s} (θ ← θ') s∈Domθ←θ' SharedVar.ready ⟨θ←θ'⟩s
          ≡⟨ cong (Env.set-shr {s} (θ ← θ') s∈Domθ←θ' SharedVar.ready) ⟨θ←θ'⟩s≡θ's ⟩
            Env.set-shr {s} (θ ← θ') s∈Domθ←θ' SharedVar.ready θ's
          ≡⟨ Env.shr-set=← (θ ← θ') s SharedVar.ready θ's s∈Domθ←θ' ⟩
            (θ ← θ') ← [s↦ready,θ's]
          ≡⟨ sym (Env.←-assoc θ θ' [s↦ready,θ's]) ⟩
            θ ← (θ' ← [s↦ready,θ's])
          ≡⟨ cong (θ ←_) (sym (Env.shr-set=← θ' s SharedVar.ready θ's s∈Domθ')) ⟩
            θ ← (Env.set-shr {s} θ' s∈Domθ' SharedVar.ready θ's)
         ∎)
        (rreadyness {θ ← θ'} {s = s} s∈Domθ←θ'
          (Data.Sum.map
            (trans (Env.shr-stats-←-right-irr' s θ θ' s∈Domθ' s∈Domθ←θ'))
            (trans (Env.shr-stats-←-right-irr' s θ θ' s∈Domθ' s∈Domθ←θ'))
            θ's≡old⊎θ's≡new)
          (λ s∈canθ-θ←θ''-q-[] →
            s∉canθ-θ'-q-[]
              (canθₛₕ-mergeʳ (Env.sig θ) θ' (E ⟦ qin ⟧e) Env.[]env (λ _ ())
                 s s∈canθ-θ←θ''-q-[])))) ,′
      (subst (λ po* → Σ[ r ∈ ρ⟨ _ , _ ⟩· _ sn⟶₁ ρ⟨ _ , _ ⟩· po* ]
                      Σ[ a ∈ _ ≐ _ ⟦ _ ⟧e ]
                      Σ[ b ∈ po* ≐ _ ⟦ _ ⟧e ]
                        ->E-view r a b)
        (unplug r'≐E⟦roin⟧)
        (rmerge (⟦⟧c-to-⟦⟧e r≐C⟦ro⟧) ,
         _ , plug refl , vmerge))
  where
    s∈Domθ←θ'   = Env.shr-←-monoʳ s θ' θ s∈Domθ'
    θ's = Env.shr-vals {s} θ' s∈Domθ'
    ⟨θ←θ'⟩s = Env.shr-vals {s} (θ ← θ') s∈Domθ←θ'
    ⟨θ←θ'⟩s≡θ's = Env.shr-vals-←-right-irr' s θ θ' s∈Domθ' s∈Domθ←θ'
    [s↦ready,θ's] =
      Θ ShrMap.empty ShrMap.[ s ↦ (SharedVar.ready , θ's) ] VarMap.empty
