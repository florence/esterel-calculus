module par-swap.confluent where

open import par-swap
open import par-swap.properties
open import Data.Nat using (_+_ ;  _≤′_ ; _<′_ ; suc ; zero ; ≤′-refl)
open import Esterel.Lang.CanFunction
open import utility
open import Esterel.Lang
open import Esterel.Context
open import Data.Product
open import Data.Sum
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; subst ; cong ; trans ;
         module ≡-Reasoning ; cong₂ ; subst₂ ; inspect)
open import sn-calculus
open import context-properties -- get view, E-views
open import Esterel.Lang.Binding
open import binding-preserve using (sn⟶-maintains-binding ; sn⟶*-maintains-binding)

open import sn-calculus-props

∥R-confluent : CB-CONFLUENT _∥R_
∥R-confluent CBp
  (∥Rstep dchole)
  (∥Rstep dchole) =
  _ , ∥Rstep dchole , ∥Rstep dchole
∥R-confluent CBp
  (∥Rstep dchole)
  (∥Rstep (dcpar₁ d≐C⟦p∥q⟧c₂)) =
  _ , ∥Rstep (dcpar₂ d≐C⟦p∥q⟧c₂) , ∥Rstep dchole
∥R-confluent CBp
  (∥Rstep dchole)
  (∥Rstep (dcpar₂ d≐C⟦p∥q⟧c₂)) =
  _ , ∥Rstep (dcpar₁ d≐C⟦p∥q⟧c₂) , ∥Rstep dchole
∥R-confluent CBp
  (∥Rstep (dcpar₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep dchole) =
  _ , ∥Rstep dchole , ∥Rstep (dcpar₂ d≐C⟦p∥q⟧c₁)
∥R-confluent (CBpar CBs _ _ _ _ _)
  (∥Rstep {c₁ ∷ C₁} (dcpar₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcpar₁ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent CBp
  (∥Rstep (dcpar₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcpar₂ d≐C⟦p∥q⟧c₂)) =
  _ ,  ∥Rstep (dcpar₂ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcpar₁ d≐C⟦p∥q⟧c₁)
∥R-confluent CBp
  (∥Rstep (dcpar₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep dchole) =
  _ , ∥Rstep dchole , ∥Rstep (dcpar₁ d≐C⟦p∥q⟧c₁)
∥R-confluent CBp
  (∥Rstep (dcpar₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcpar₁ d≐C⟦p∥q⟧c₂)) =
  _ , ∥Rstep (dcpar₁ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcpar₂ d≐C⟦p∥q⟧c₁)
∥R-confluent (CBpar _ CBs _ _ _ _)
  (∥Rstep {c₁ ∷ C₁} (dcpar₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcpar₂ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBseq CBs _ _)
  (∥Rstep {c₁ ∷ C₁} (dcseq₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcseq₁ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent CBp
  (∥Rstep (dcseq₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcseq₂ d≐C⟦p∥q⟧c₂)) =
  _ , ∥Rstep (dcseq₂ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcseq₁ d≐C⟦p∥q⟧c₁)
∥R-confluent CBp
  (∥Rstep (dcseq₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcseq₁ d≐C⟦p∥q⟧c₂)) =
  _ , ∥Rstep (dcseq₁ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcseq₂ d≐C⟦p∥q⟧c₁)
∥R-confluent (CBseq _ CBs _)
  (∥Rstep {c₁ ∷ C₁} (dcseq₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcseq₂ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBsusp CBs _)
  (∥Rstep {c₁ ∷ C₁} (dcsuspend d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcsuspend d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBtrap CBs)
  (∥Rstep {c₁ ∷ C₁} (dctrap d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dctrap d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBsig CBs)
  (∥Rstep {c₁ ∷ C₁} (dcsignl d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcsignl d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBpresent CBs _)
  (∥Rstep {c₁ ∷ C₁} (dcpresent₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcpresent₁ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent CBp
  (∥Rstep (dcpresent₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcpresent₂ d≐C⟦p∥q⟧c₂)) =
   _ , ∥Rstep (dcpresent₂ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcpresent₁ d≐C⟦p∥q⟧c₁)
∥R-confluent CBp
  (∥Rstep (dcpresent₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcpresent₁ d≐C⟦p∥q⟧c₂)) =
  _ , ∥Rstep (dcpresent₁ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcpresent₂ d≐C⟦p∥q⟧c₁)
∥R-confluent (CBpresent _ CBs)
  (∥Rstep {c₁ ∷ C₁} (dcpresent₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcpresent₂ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBloop CBs _)
  (∥Rstep {c₁ ∷ C₁} (dcloop d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcloop d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBloopˢ CBs _ _ _)
  (∥Rstep {c₁ ∷ C₁} (dcloopˢ₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcloopˢ₁ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent CBp
  (∥Rstep (dcloopˢ₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcloopˢ₂ d≐C⟦p∥q⟧c₂)) =
   _ , ∥Rstep (dcloopˢ₂ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcloopˢ₁ d≐C⟦p∥q⟧c₁)
∥R-confluent CBp
  (∥Rstep (dcloopˢ₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcloopˢ₁ d≐C⟦p∥q⟧c₂)) =
  _ , ∥Rstep (dcloopˢ₁ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcloopˢ₂ d≐C⟦p∥q⟧c₁)
∥R-confluent (CBloopˢ _ CBs _ _)
  (∥Rstep {c₁ ∷ C₁} (dcloopˢ₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcloopˢ₂ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBshared CBs)
  (∥Rstep {c₁ ∷ C₁} (dcshared d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcshared d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBvar CBs)
  (∥Rstep {c₁ ∷ C₁} (dcvar d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcvar d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBif CBs _)
  (∥Rstep {c₁ ∷ C₁} (dcif₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcif₁ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent _
  (∥Rstep (dcif₁ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcif₂ d≐C⟦p∥q⟧c₂)) =
  _ , ∥Rstep (dcif₂ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcif₁ d≐C⟦p∥q⟧c₁)
∥R-confluent CBp
  (∥Rstep (dcif₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep (dcif₁ d≐C⟦p∥q⟧c₂)) =
  _ , ∥Rstep (dcif₁ d≐C⟦p∥q⟧c₂) , ∥Rstep (dcif₂ d≐C⟦p∥q⟧c₁)
∥R-confluent (CBif _ CBs)
  (∥Rstep {c₁ ∷ C₁} (dcif₂ d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcif₂ d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz
∥R-confluent (CBρ CBs)
  (∥Rstep {c₁ ∷ C₁} (dcenv d≐C⟦p∥q⟧c₁))
  (∥Rstep {c₂ ∷ C₂} (dcenv d≐C⟦p∥q⟧c₂))
  with ∥R-confluent CBs (∥Rstep d≐C⟦p∥q⟧c₁) (∥Rstep d≐C⟦p∥q⟧c₂)
... | z , C₁⟦q₁∥p₁⟧c∥Rz , C₂⟦q₂∥p₂⟧c∥Rz  =
  _ , Context1-∥R c₁ C₁⟦q₁∥p₁⟧c∥Rz , Context1-∥R c₂ C₂⟦q₂∥p₂⟧c∥Rz

∥R-maintains-binding :
  ∀ {p BV FV q} →
  CorrectBinding p BV FV →
  p ∥R q →
  CorrectBinding q (BVars q) (FVars q)
∥R-maintains-binding = thm where

  thm :
    ∀ {p BV FV q} →
     CorrectBinding p BV FV →
     p ∥R q →
     CorrectBinding q (BVars q) (FVars q)
  thm{p}{BVp}{FVp}{q} CBp (∥Rstep{C}{r₁}{r₂}{d} d≐C⟦p∥q⟧c)
    with binding-extractc' CBp d≐C⟦p∥q⟧c
  ... | (BVr₁∥r₂ , FVr₁∥r₂) ,
        CBpar{.r₁}{.r₂}{BVr₁}{FVr₁}{BVr₂}{FVr₂}
             CBr₁ CBr₂ BVr₁≠BVr₂ FVr₁≠BVr₂ BVr₁≠FVr₂ Xr₁≠Xr₂
     with CBpar{r₂}{r₁}{BVr₂}{FVr₂}{BVr₁}{FVr₁}
               CBr₂ CBr₁
               (distinct-sym BVr₁≠BVr₂) (distinct-sym BVr₁≠FVr₂)
               (distinct-sym FVr₁≠BVr₂) (dist'-sym Xr₁≠Xr₂)
  ... | CBr₂∥r₁
    with binding-substc' CBp d≐C⟦p∥q⟧c
            (CBpar CBr₁ CBr₂ BVr₁≠BVr₂ FVr₁≠BVr₂
                   BVr₁≠FVr₂ Xr₁≠Xr₂)
            (∪-comm-⊆-right BVr₁ ⊆-refl)
            (∪-comm-⊆-right FVr₁ ⊆-refl)
            CBr₂∥r₁
  ... | (BVq , FVq) , (_ , CBq)
    with BVFVcorrect _ BVq FVq CBq
  ... | (refl , refl) = CBq

∥R*-maintains-binding :
  ∀ {p BV FV q} →
  CorrectBinding p BV FV →
  p ∥R* q →
  CorrectBinding q (BVars q) (FVars q)
∥R*-maintains-binding = thm where

  thm : ∀ {p BV FV q} →
   CorrectBinding p BV FV →
   p ∥R* q →
   CorrectBinding q (BVars q) (FVars q)
  thm CBp ∥R0 with BVFVcorrect _ _ _ CBp
  ... | refl , refl = CBp
  thm CBp (∥Rn p∥Rq₁ q₁∥R*q)
    with ∥R-maintains-binding CBp p∥Rq₁
  ... | CBq₁ = thm CBq₁ q₁∥R*q

∥R*-semi-confluent :
  ∀ {p q r BV FV} ->
  CorrectBinding p BV FV ->
  p ∥R q ->
  p ∥R* r ->
 ∃ λ {z → (q ∥R* z × r ∥R* z)}
∥R*-semi-confluent CBp p∥Rq ∥R0 = _ , ∥R0 , (∥Rn p∥Rq ∥R0)
∥R*-semi-confluent CBp p∥Rq (∥Rn p∥Rq₁ q₁∥R*r)
  with ∥R-confluent CBp p∥Rq p∥Rq₁
... | z , q∥Rz , q₁∥Rz
  with ∥R*-semi-confluent (∥R-maintains-binding CBp p∥Rq₁) q₁∥Rz q₁∥R*r
... | z₁ , z∥R*z₁ , r∥R*z₁ = z₁ , ∥Rn q∥Rz z∥R*z₁ , r∥R*z₁

∥R*-confluent : CB-CONFLUENT _∥R*_
∥R*-confluent CBp ∥R0 p∥R*r = _ , p∥R*r , ∥R0
∥R*-confluent CBp (∥Rn p∥Rp₁ p₁∥R*q) p∥R*r
  with ∥R*-semi-confluent CBp p∥Rp₁ p∥R*r
... | z₁ , p₁∥R*z₁ , r∥R*z₁
  with ∥R*-confluent (∥R-maintains-binding CBp p∥Rp₁) p₁∥R*q p₁∥R*z₁
... | z  , q∥R*z , z₁∥R*z = z , q∥R*z , ∥R*-concat r∥R*z₁ z₁∥R*z
