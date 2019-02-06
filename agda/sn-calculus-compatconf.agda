module sn-calculus-compatconf where

open import sn-calculus
open import utility renaming (_U̬_ to _∪_)
open import context-properties
  using (get-view ; ->E-view ; ->pot-view)

open import sn-calculus-compatconf.eview
  using (1-steplρ-E-view)
open import sn-calculus-compatconf.pot
  using (1-steplρ-pot)
open import sn-calculus-confluence
  using (R-confluent)

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; module SigMap ; module ShrMap ; module VarMap)
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
  using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_ ; id ; _∋_)

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

1-step-sn⟶₁ : ∀{p q r BV FV} →
  CorrectBinding p BV FV →
  p sn⟶₁ q →
  p sn⟶₁ r →
  Σ[ p' ∈ Term ] (q sn⟶* p'  ×  r sn⟶* p')
1-step-sn⟶₁ cb psn⟶₁q psn⟶₁r with R-confluent cb psn⟶₁q psn⟶₁r
... | inj₁ refl = _ , rrefl ,′ rrefl
... | inj₂ (inj₁ (_ , qsn⟶₁s , rsn⟶₁s)) =
  _ , sn⟶*-inclusion (sn⟶-inclusion qsn⟶₁s) ,′ sn⟶*-inclusion (sn⟶-inclusion rsn⟶₁s)
... | inj₂ (inj₂ (inj₁ qsn⟶₁r)) =
  _ , sn⟶*-inclusion (sn⟶-inclusion qsn⟶₁r) ,′ rrefl
... | inj₂ (inj₂ (inj₂ rsn⟶₁q)) =
  _ , rrefl ,′ sn⟶*-inclusion (sn⟶-inclusion rsn⟶₁q)


1-steplρ : ∀{p q r θ θq BV FV} →
  CorrectBinding (ρ θ · p) BV FV →
  ρ θ · p sn⟶₁ ρ θq · q →
  p sn⟶ r →
  Σ[ p' ∈ Term ] ((ρ θq · q) sn⟶* p'   ×    (ρ θ · r) sn⟶* p')
1-steplρ {p} {q} {r} cb
  ρθ·psn⟶₁ρθq·q psn⟶r@(rcontext {.p} {rin} {ro} C p≐C⟦rin⟧ rinsn⟶₁ro)
  with get-view ρθ·psn⟶₁ρθq·q
... | inj₂ (refl , pot) =
  _ ,  1-steplρ-pot cb pot psn⟶r
... | inj₁ (E , qin , qo , p≐E⟦qin⟧ , q≐E⟦qo⟧ , e-view) =
  _ ,  proj₂ (1-steplρ-E-view cb p≐E⟦qin⟧ q≐E⟦qo⟧ e-view p≐C⟦rin⟧ rinsn⟶₁ro)

1-stepl : ∀{p q r BV FV} →
  CorrectBinding p BV FV →
  p sn⟶₁ q →
  p sn⟶ r →
  Σ[ p' ∈ Term ] (q sn⟶* p'  ×  r sn⟶* p')
1-stepl cb psn⟶₁q
        (rcontext [] dchole psn⟶₁r) =
  1-step-sn⟶₁ cb psn⟶₁q psn⟶₁r
1-stepl cb (rpar-done-right p' q')
        (rcontext (ceval (epar₁ _) ∷ crs) (dcpar₁ dcr) psn⟶₁r) =
  ⊥-elim (halted-¬sn⟶ p' (rcontext _ dcr psn⟶₁r))
1-stepl cb (rpar-done-left (dhalted p') q')
        (rcontext (ceval (epar₁ _) ∷ crs) (dcpar₁ dcr) psn⟶₁r) =
  ⊥-elim (halted-¬sn⟶ p' (rcontext _ dcr psn⟶₁r))
1-stepl cb (rpar-done-left (dpaused p') hnothin)
        (rcontext (ceval (epar₁ _) ∷ crs) (dcpar₁ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ dcr psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ dchole
                   (rpar-done-left
                    (dpaused (paused-sn⟶ p' (rcontext _ dcr psn⟶₁r)))
                    hnothin))
1-stepl cb (rpar-done-left (dpaused p') (hexit n))
        (rcontext (ceval (epar₁ _) ∷ crs) (dcpar₁ dcr) psn⟶₁r) =
  _ ,
  rrefl  ,′
  sn⟶*-inclusion (rcontext _ dchole
                   (rpar-done-left
                    (dpaused (paused-sn⟶ p' (rcontext _ dcr psn⟶₁r)))
                    (hexit n)))
1-stepl cb (rpar-done-right p' (dhalted q'))
        (rcontext (ceval (epar₂ p₁) ∷ crs) (dcpar₂ dcr) psn⟶₁r) =
  ⊥-elim (halted-¬sn⟶ q' (rcontext _ dcr psn⟶₁r))
1-stepl cb (rpar-done-right hnothin (dpaused q'))
        (rcontext (ceval (epar₂ .nothin) ∷ crs) (dcpar₂ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ dcr psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ dchole
                   (rpar-done-right
                    hnothin
                    (dpaused (paused-sn⟶ q' (rcontext _ dcr psn⟶₁r)))))
1-stepl cb (rpar-done-right (hexit n) (dpaused q'))
        (rcontext (ceval (epar₂ .(exit n)) ∷ crs) (dcpar₂ dcr) psn⟶₁r) =
  _ ,
  rrefl  ,′
  sn⟶*-inclusion (rcontext _ dchole
                   (rpar-done-right
                    (hexit n)
                    (dpaused (paused-sn⟶ q' (rcontext _ dcr psn⟶₁r)))))
1-stepl cb (rpar-done-left p' q')
        (rcontext (ceval (epar₂ p₁) ∷ crs) (dcpar₂ dcr) psn⟶₁r) =
  ⊥-elim (halted-¬sn⟶ q' (rcontext _ dcr psn⟶₁r))
1-stepl cb rseq-done
        (rcontext _ (dcseq₁ dchole) psn⟶₁r) =
  ⊥-elim (halted-¬sn⟶₁ hnothin psn⟶₁r)
1-stepl cb rseq-exit
        (rcontext _ (dcseq₁ dchole) psn⟶₁r) =
  ⊥-elim (halted-¬sn⟶₁ (hexit _) psn⟶₁r)
1-stepl cb rloopˢ-exit
        (rcontext _ (dcloopˢ₁ dchole) psn⟶₁r) =
  ⊥-elim (halted-¬sn⟶₁ (hexit _) psn⟶₁r)
1-stepl cb (rsuspend-done p')
        (rcontext (ceval (esuspend S) ∷ crs) (dcsuspend dcr) psn⟶₁r) =
  ⊥-elim (halted-¬sn⟶₁ (halted-⟦⟧c p' dcr) psn⟶₁r)
1-stepl cb (rtrap-done p')
        (rcontext (ceval etrap ∷ crs) (dctrap dcr) psn⟶₁r) =
  ⊥-elim (halted-¬sn⟶₁ (halted-⟦⟧c p' dcr) psn⟶₁r)
1-stepl cb rraise-signal (rcontext (csignl S ∷ crs) (dcsignl dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcenv dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ dchole rraise-signal)
1-stepl cb rloop-unroll
        (rcontext (cloop ∷ crs) (dcloop dcr) psn⟶₁r) =

  _ ,
  rstep (rcontext _ (dcloopˢ₁ dcr) psn⟶₁r)
        (rstep (rcontext _ (dcloopˢ₂ dcr) psn⟶₁r) rrefl) ,′
  sn⟶*-inclusion (rcontext [] dchole rloop-unroll)

1-stepl cb rseq-done
        (rcontext (cseq₂ .nothin ∷ crs) (dcseq₂ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ dcr psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ dchole rseq-done)
1-stepl cb rseq-exit
        (rcontext (cseq₂ .(exit _) ∷ crs) (dcseq₂ dcr) psn⟶₁r) =
  _ ,
  rrefl  ,′
  sn⟶*-inclusion (rcontext _ dchole rseq-exit)
1-stepl cb rloopˢ-exit
        (rcontext (cloopˢ₂ .(exit _) ∷ crs) (dcloopˢ₂ dcr) psn⟶₁r) =
  _ ,
  rrefl  ,′
  sn⟶*-inclusion (rcontext _ dchole rloopˢ-exit)
1-stepl {ρ .θ · p} cb
        ρθpsn⟶₁q
        ρθpsn⟶r@(rcontext {p = p₂} {p' = r} (cenv θ ∷ crs) (dcenv p≐crs⟦p₂⟧) p₂sn⟶₁r)
  with ρ-stays-ρ-sn⟶₁ ρθpsn⟶₁q
... | θ' , qin , refl =
  1-steplρ cb ρθpsn⟶₁q (rcontext crs p≐crs⟦p₂⟧ p₂sn⟶₁r)

1-step : ∀{p q r BV FV} →
  CorrectBinding p BV FV →
  p sn⟶ q →
  p sn⟶ r →
  Σ[ p' ∈ Term ] (q  sn⟶* p'  ×  r sn⟶* p')
1-step cb   (rcontext [] dchole psn⟶₁q) psn⟶r =  1-stepl cb psn⟶₁q psn⟶r
1-step cb
       psn⟶q@(rcontext (_ ∷ _) _ _) (rcontext [] dchole psn⟶₁r) with 1-stepl cb psn⟶₁r psn⟶q
... | _ , rsn⟶*p' , qsn⟶*p' =  _ , qsn⟶*p' ,′ rsn⟶*p'
1-step cb@(CBpar cbp cbq _ _ _ _)
       (rcontext (cq ∷ cqs) (dcpar₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcpar₁ dcr) psn⟶₁r)
  with 1-step cbp (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBpar cbp cbq _ _ _ _)
       (rcontext (cq ∷ cqs) (dcpar₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcpar₂ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcpar₂ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcpar₁ dcq) psn⟶₁q)
1-step cb@(CBpar cbp cbq _ _ _ _)
       (rcontext (cq ∷ cqs) (dcpar₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcpar₁ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcpar₁ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcpar₂ dcq) psn⟶₁q)
1-step cb@(CBpar cbp cbq _ _ _ _)
       (rcontext (cq ∷ cqs) (dcpar₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcpar₂ dcr) psn⟶₁r)
  with 1-step cbq (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBseq cbp cbq _)
       (rcontext (cq ∷ cqs) (dcseq₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcseq₁ dcr) psn⟶₁r)
  with 1-step cbp (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb
       (rcontext (cq ∷ cqs) (dcseq₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcseq₂ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcseq₂ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcseq₁ dcq) psn⟶₁q)
1-step cb
       (rcontext (cq ∷ cqs) (dcseq₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcseq₁ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcseq₁ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcseq₂ dcq) psn⟶₁q)
1-step cb@(CBseq cbp cbq _)
       (rcontext (cq ∷ cqs) (dcseq₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcseq₂ dcr) psn⟶₁r)
  with 1-step cbq (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBloopˢ cbp cbq _ _)
       (rcontext (cq ∷ cqs) (dcloopˢ₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcloopˢ₁ dcr) psn⟶₁r)
  with 1-step cbp (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''

1-step cb
       (rcontext (cq ∷ cqs) (dcloopˢ₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcloopˢ₂ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcloopˢ₂ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcloopˢ₁ dcq) psn⟶₁q)
1-step cb
       (rcontext (cq ∷ cqs) (dcloopˢ₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcloopˢ₁ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcloopˢ₁ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcloopˢ₂ dcq) psn⟶₁q)
1-step cb@(CBloopˢ cbp cbq _ _)
       (rcontext (cq ∷ cqs) (dcloopˢ₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcloopˢ₂ dcr) psn⟶₁r)
  with 1-step cbq (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''

1-step cb@(CBsusp cb' _)
       (rcontext (cq ∷ cqs) (dcsuspend dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcsuspend dcr) psn⟶₁r)
  with 1-step cb' (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBtrap cb')
       (rcontext (cq ∷ cqs) (dctrap dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dctrap dcr) psn⟶₁r)
  with 1-step cb' (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBsig cb')
       (rcontext (cq ∷ cqs) (dcsignl dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcsignl dcr) psn⟶₁r)
  with 1-step cb' (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBpresent cbp cbq)
       (rcontext (cq ∷ cqs) (dcpresent₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcpresent₁ dcr) psn⟶₁r)
  with 1-step cbp (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb
       (rcontext (cq ∷ cqs) (dcpresent₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcpresent₂ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcpresent₂ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcpresent₁ dcq) psn⟶₁q)
1-step cb
       (rcontext (cq ∷ cqs) (dcpresent₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcpresent₁ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcpresent₁ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcpresent₂ dcq) psn⟶₁q)
1-step cb@(CBpresent cbp cbq)
       (rcontext (cq ∷ cqs) (dcpresent₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcpresent₂ dcr) psn⟶₁r)
  with 1-step cbq (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBloop cb' _)
       (rcontext (cq ∷ cqs) (dcloop dcq) psn⟶₁q) (rcontext (cr ∷ crs) (dcloop dcr) psn⟶₁r)
  with 1-step cb' (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBshared cb')
       (rcontext (cq ∷ cqs) (dcshared dcq) psn⟶₁q) (rcontext (cr ∷ crs) (dcshared dcr) psn⟶₁r)
  with 1-step cb' (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBvar cb')
       (rcontext (cq ∷ cqs) (dcvar dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcvar dcr) psn⟶₁r)
  with 1-step cb' (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBif cbp cbq)
       (rcontext (cq ∷ cqs) (dcif₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcif₁ dcr) psn⟶₁r)
  with 1-step cbp (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb
       (rcontext (cq ∷ cqs) (dcif₁ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcif₂ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcif₂ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcif₁ dcq) psn⟶₁q)
1-step cb
       (rcontext (cq ∷ cqs) (dcif₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcif₁ dcr) psn⟶₁r) =
  _ ,
  sn⟶*-inclusion (rcontext _ (dcif₁ dcr) psn⟶₁r) ,′
  sn⟶*-inclusion (rcontext _ (dcif₂ dcq) psn⟶₁q)
1-step cb@(CBif cbp cbq)
       (rcontext (cq ∷ cqs) (dcif₂ dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcif₂ dcr) psn⟶₁r)
  with 1-step cbq (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
1-step cb@(CBρ cb')
       (rcontext (cq ∷ cqs) (dcenv dcq) psn⟶₁q)
       (rcontext (cr ∷ crs) (dcenv dcr) psn⟶₁r)
  with 1-step cb' (rcontext cqs dcq psn⟶₁q) (rcontext crs dcr psn⟶₁r)
... | p'' , q'sn⟶*p'' , r'sn⟶*p'' = _ , Context1-sn⟶* cq q'sn⟶*p'' ,′ Context1-sn⟶* cr r'sn⟶*p''
