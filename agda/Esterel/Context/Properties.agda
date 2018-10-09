module Esterel.Context.Properties where

open import Esterel.Lang
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)

open import Data.List
  using (List ; _∷_ ; [] ; map ; _++_)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; _,′_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; cong ; subst ; trans)

open _≐_⟦_⟧e
open _≐_⟦_⟧c
open EvaluationContext1
open Context1

plug : ∀{p E q} → E ⟦ q ⟧e ≡ p → p ≐ E ⟦ q ⟧e
plug {E = []}             refl = dehole
plug {E = epar₁ q ∷ E}    refl = depar₁    (plug {E = E} refl)
plug {E = epar₂ p₁ ∷ E}   refl = depar₂    (plug {E = E} refl)
plug {E = eseq q ∷ E}     refl = deseq     (plug {E = E} refl)
plug {E = eloopˢ q ∷ E}   refl = deloopˢ   (plug {E = E} refl) 
plug {E = esuspend S ∷ E} refl = desuspend (plug {E = E} refl)
plug {E = etrap ∷ E}      refl = detrap    (plug {E = E} refl)

unplug : ∀{p E q} → p ≐ E ⟦ q ⟧e → E ⟦ q ⟧e ≡ p
unplug dehole                           = refl
unplug (depar₁ eq)    rewrite unplug eq = refl
unplug (depar₂ eq)    rewrite unplug eq = refl
unplug (deseq eq)     rewrite unplug eq = refl
unplug (deloopˢ eq)   rewrite unplug eq = refl
unplug (desuspend eq) rewrite unplug eq = refl
unplug (detrap eq)    rewrite unplug eq = refl

plugc : ∀ {C q p} → C ⟦ q ⟧c ≡ p → p ≐ C ⟦ q ⟧c
plugc {[]}                     refl = dchole
plugc {ceval (epar₁ q) ∷ C}    refl = dcpar₁     (plugc {C} refl)
plugc {ceval (epar₂ p) ∷ C}    refl = dcpar₂     (plugc {C} refl)
plugc {ceval (eseq q) ∷ C}     refl = dcseq₁     (plugc {C} refl)
plugc {ceval (eloopˢ q) ∷ C}   refl = dcloopˢ₁   (plugc {C} refl)
plugc {ceval (esuspend S) ∷ C} refl = dcsuspend  (plugc {C} refl)
plugc {ceval etrap ∷ C}        refl = dctrap     (plugc {C} refl)
plugc {csignl S ∷ C}           refl = dcsignl    (plugc {C} refl)
plugc {cpresent₁ S q ∷ C}      refl = dcpresent₁ (plugc {C} refl)
plugc {cpresent₂ S p ∷ C}      refl = dcpresent₂ (plugc {C} refl)
plugc {cloop ∷ C}              refl = dcloop     (plugc {C} refl)
plugc {cloopˢ₂ p ∷ C}          refl = dcloopˢ₂   (plugc {C} refl) 
plugc {cseq₂ p ∷ C}            refl = dcseq₂     (plugc {C} refl)
plugc {cshared s e ∷ C}        refl = dcshared   (plugc {C} refl)
plugc {cvar x e ∷ C}           refl = dcvar      (plugc {C} refl)
plugc {cif₁ x q ∷ C}           refl = dcif₁      (plugc {C} refl)
plugc {cif₂ x p ∷ C}           refl = dcif₂      (plugc {C} refl)
plugc {cenv θ ∷ C}             refl = dcenv      (plugc {C} refl)

unplugc : ∀{p C q} → p ≐ C ⟦ q ⟧c → C ⟦ q ⟧c ≡ p
unplugc dchole                             = refl
unplugc (dcpar₁ eq)     rewrite unplugc eq = refl
unplugc (dcpar₂ eq)     rewrite unplugc eq = refl
unplugc (dcseq₁ eq)     rewrite unplugc eq = refl
unplugc (dcseq₂ eq)     rewrite unplugc eq = refl
unplugc (dcsuspend eq)  rewrite unplugc eq = refl
unplugc (dctrap eq)     rewrite unplugc eq = refl
unplugc (dcsignl eq)    rewrite unplugc eq = refl
unplugc (dcpresent₁ eq) rewrite unplugc eq = refl
unplugc (dcpresent₂ eq) rewrite unplugc eq = refl
unplugc (dcloop eq)     rewrite unplugc eq = refl
unplugc (dcloopˢ₁ eq)   rewrite unplugc eq = refl
unplugc (dcloopˢ₂ eq)   rewrite unplugc eq = refl 
unplugc (dcshared eq)   rewrite unplugc eq = refl
unplugc (dcvar eq)      rewrite unplugc eq = refl
unplugc (dcif₁ eq)      rewrite unplugc eq = refl
unplugc (dcif₂ eq)      rewrite unplugc eq = refl
unplugc (dcenv eq)      rewrite unplugc eq = refl

plug-sym : ∀{E E' p q} → E ⟦ p ⟧e ≐ E' ⟦ q ⟧e → E' ⟦ q ⟧e ≐ E ⟦ p ⟧e
plug-sym eq = plug (sym (unplug eq))

unplug-eq : ∀{p q r E} → p ≐ E ⟦ q ⟧e → p ≐ E ⟦ r ⟧e → q ≡ r
unplug-eq dehole          dehole          = refl
unplug-eq (depar₁ qeq)    (depar₁ req)    = unplug-eq qeq req
unplug-eq (depar₂ qeq)    (depar₂ req)    = unplug-eq qeq req
unplug-eq (deseq qeq)     (deseq req)     = unplug-eq qeq req
unplug-eq (deloopˢ qeq)   (deloopˢ req)   = unplug-eq qeq req 
unplug-eq (desuspend qeq) (desuspend req) = unplug-eq qeq req
unplug-eq (detrap qeq)    (detrap req)    = unplug-eq qeq req

plug-eq : ∀{p q r E} → p ≐ E ⟦ r ⟧e → q ≐ E ⟦ r ⟧e → p ≡ q
plug-eq peq qeq = trans (sym (unplug peq)) (unplug qeq)

Erefl : ∀{E p} → E ⟦ p ⟧e ≐ E ⟦ p ⟧e
Erefl = plug refl

Crefl : ∀{C p} → C ⟦ p ⟧c ≐ C ⟦ p ⟧c
Crefl = plugc refl

⟦⟧e-to-⟦⟧c : ∀ {E p q} -> p ≐ E ⟦ q ⟧e -> p ≐ (map ceval E) ⟦ q ⟧c
⟦⟧e-to-⟦⟧c dehole             = dchole
⟦⟧e-to-⟦⟧c (depar₁ decomp)    = dcpar₁    (⟦⟧e-to-⟦⟧c decomp)
⟦⟧e-to-⟦⟧c (depar₂ decomp)    = dcpar₂    (⟦⟧e-to-⟦⟧c decomp)
⟦⟧e-to-⟦⟧c (deseq decomp)     = dcseq₁    (⟦⟧e-to-⟦⟧c decomp)
⟦⟧e-to-⟦⟧c (deloopˢ decomp)   = dcloopˢ₁  (⟦⟧e-to-⟦⟧c decomp) 
⟦⟧e-to-⟦⟧c (desuspend decomp) = dcsuspend (⟦⟧e-to-⟦⟧c decomp)
⟦⟧e-to-⟦⟧c (detrap decomp)    = dctrap    (⟦⟧e-to-⟦⟧c decomp)

⟦⟧c-to-⟦⟧e : ∀ {E p q} → p ≐ (map ceval E) ⟦ q ⟧c → p ≐ E ⟦ q ⟧e
⟦⟧c-to-⟦⟧e {[]}    dchole             = dehole
⟦⟧c-to-⟦⟧e {_ ∷ _} (dcpar₁ p≐E⟦q⟧)    = depar₁    (⟦⟧c-to-⟦⟧e p≐E⟦q⟧)
⟦⟧c-to-⟦⟧e {_ ∷ _} (dcpar₂ p≐E⟦q⟧)    = depar₂    (⟦⟧c-to-⟦⟧e p≐E⟦q⟧)
⟦⟧c-to-⟦⟧e {_ ∷ _} (dcseq₁ p≐E⟦q⟧)    = deseq     (⟦⟧c-to-⟦⟧e p≐E⟦q⟧)
⟦⟧c-to-⟦⟧e {_ ∷ _} (dcloopˢ₁ p≐E⟦q⟧)  = deloopˢ   (⟦⟧c-to-⟦⟧e p≐E⟦q⟧) 
⟦⟧c-to-⟦⟧e {_ ∷ _} (dcsuspend p≐E⟦q⟧) = desuspend (⟦⟧c-to-⟦⟧e p≐E⟦q⟧)
⟦⟧c-to-⟦⟧e {_ ∷ _} (dctrap p≐E⟦q⟧)    = detrap    (⟦⟧c-to-⟦⟧e p≐E⟦q⟧)


C++ : ∀ {C1 C2 p1 p2 p3} ->
  p1 ≐ C1 ⟦ p2 ⟧c ->
  p2 ≐ C2 ⟦ p3 ⟧c ->
  p1 ≐ C1 ++ C2 ⟦ p3 ⟧c
C++ dchole p2C = p2C
C++ (dcpar₁ p1C) p2C = dcpar₁ (C++ p1C p2C)
C++ (dcpar₂ p1C) p2C = dcpar₂ (C++ p1C p2C)
C++ (dcseq₁ p1C) p2C = dcseq₁ (C++ p1C p2C)
C++ (dcseq₂ p1C) p2C = dcseq₂ (C++ p1C p2C)
C++ (dcsuspend p1C) p2C = dcsuspend (C++ p1C p2C)
C++ (dctrap p1C) p2C = dctrap (C++ p1C p2C)
C++ (dcsignl p1C) p2C = dcsignl (C++ p1C p2C)
C++ (dcpresent₁ p1C) p2C = dcpresent₁ (C++ p1C p2C)
C++ (dcpresent₂ p1C) p2C = dcpresent₂ (C++ p1C p2C)
C++ (dcloop p1C) p2C = dcloop (C++ p1C p2C)
C++ (dcloopˢ₁ p1C) p2C = dcloopˢ₁ (C++ p1C p2C)
C++ (dcloopˢ₂ p1C) p2C = dcloopˢ₂ (C++ p1C p2C)
C++ (dcshared p1C) p2C = dcshared (C++ p1C p2C)
C++ (dcvar p1C) p2C = dcvar (C++ p1C p2C)
C++ (dcif₁ p1C) p2C = dcif₁ (C++ p1C p2C)
C++ (dcif₂ p1C) p2C = dcif₂ (C++ p1C p2C)
C++ (dcenv p1C) p2C = dcenv (C++ p1C p2C)

++-is-nesting : ∀ C′ C q ->
 (C′ ++ C) ⟦ q ⟧c ≐ C′ ⟦ C ⟦ q ⟧c ⟧c
++-is-nesting [] C q = dchole
++-is-nesting (ceval (epar₁ q) ∷ C′) C q₁ = dcpar₁ (++-is-nesting C′ C q₁)
++-is-nesting (ceval (epar₂ p) ∷ C′) C q = dcpar₂ (++-is-nesting C′ C q)
++-is-nesting (ceval (eseq q) ∷ C′) C q₁ = dcseq₁ (++-is-nesting C′ C q₁)
++-is-nesting (ceval (eloopˢ q) ∷ C′) C q₁ = dcloopˢ₁ (++-is-nesting C′ C q₁)
++-is-nesting (ceval (esuspend S) ∷ C′) C q = dcsuspend (++-is-nesting C′ C q)
++-is-nesting (ceval etrap ∷ C′) C q = dctrap (++-is-nesting C′ C q)
++-is-nesting (csignl S ∷ C′) C q = dcsignl (++-is-nesting C′ C q)
++-is-nesting (cpresent₁ S q ∷ C′) C q₁ = dcpresent₁ (++-is-nesting C′ C q₁)
++-is-nesting (cpresent₂ S p ∷ C′) C q = dcpresent₂ (++-is-nesting C′ C q)
++-is-nesting (cloop ∷ C′) C q = dcloop (++-is-nesting C′ C q)
++-is-nesting (cloopˢ₂ p ∷ C′) C q = dcloopˢ₂ (++-is-nesting C′ C q)
++-is-nesting (cseq₂ p ∷ C′) C q = dcseq₂ (++-is-nesting C′ C q)
++-is-nesting (cshared s e ∷ C′) C q = dcshared (++-is-nesting C′ C q)
++-is-nesting (cvar x e ∷ C′) C q = dcvar (++-is-nesting C′ C q)
++-is-nesting (cif₁ x q ∷ C′) C q₁ = dcif₁ (++-is-nesting C′ C q₁)
++-is-nesting (cif₂ x p ∷ C′) C q = dcif₂ (++-is-nesting C′ C q)
++-is-nesting (cenv θ ∷ C′) C q = dcenv (++-is-nesting C′ C q)
