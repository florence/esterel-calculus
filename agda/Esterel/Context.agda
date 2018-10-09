module Esterel.Context where

open import Esterel.Lang
open import Esterel.Environment
  using (Env)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ) renaming (_≟ₛₜ_ to _≟ₛₜₛ_)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ) renaming (_≟ₛₜ_ to _≟ₛₜₛₕ_)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)

open import Data.List
  using (List ; _∷_ ; [])

infix   7 _⟦_⟧e
infix   7 _⟦_⟧c
infix   4 _≐_⟦_⟧e
infix   4 _≐_⟦_⟧c

data EvaluationContext1 : Set where
  epar₁    : (q : Term)    → EvaluationContext1
  epar₂    : (p : Term)    → EvaluationContext1
  eseq     : (q : Term)    → EvaluationContext1
  eloopˢ   : (q : Term)    → EvaluationContext1
  esuspend : (S : Signal)  → EvaluationContext1
  etrap    :                 EvaluationContext1

EvaluationContext : Set
EvaluationContext = List EvaluationContext1

_⟦_⟧e : EvaluationContext → Term → Term
[]               ⟦ p ⟧e = p
(epar₁ q ∷ E)    ⟦ p ⟧e = (E ⟦ p ⟧e) ∥  q
(epar₂ p ∷ E)    ⟦ q ⟧e = p          ∥  (E ⟦ q ⟧e)
(eseq q ∷ E)     ⟦ p ⟧e = (E ⟦ p ⟧e) >> q
(eloopˢ q ∷ E)   ⟦ p ⟧e = loopˢ (E ⟦ p ⟧e) q
(esuspend S ∷ E) ⟦ p ⟧e = suspend (E ⟦ p ⟧e) S
(etrap ∷ E)      ⟦ p ⟧e = trap (E ⟦ p ⟧e)

data _≐_⟦_⟧e : Term → EvaluationContext → Term → Set where
  dehole    : ∀{p}                        → (p           ≐  []               ⟦ p ⟧e)
  depar₁    : ∀{p r q E} → (p ≐ E ⟦ r ⟧e) → (p ∥ q       ≐  (epar₁ q ∷ E)    ⟦ r ⟧e)
  depar₂    : ∀{p r q E} → (q ≐ E ⟦ r ⟧e) → (p ∥ q       ≐  (epar₂ p ∷ E)    ⟦ r ⟧e)
  deseq     : ∀{p r q E} → (p ≐ E ⟦ r ⟧e) → (p >> q      ≐  (eseq q ∷ E)     ⟦ r ⟧e)
  deloopˢ   : ∀{p r q E} → (p ≐ E ⟦ r ⟧e) → (loopˢ p q   ≐  (eloopˢ q ∷ E)   ⟦ r ⟧e)
  desuspend : ∀{p E r S} → (p ≐ E ⟦ r ⟧e) → (suspend p S ≐  (esuspend S ∷ E) ⟦ r ⟧e)
  detrap    : ∀{p E r}   → (p ≐ E ⟦ r ⟧e) → (trap p      ≐  (etrap ∷ E)      ⟦ r ⟧e)


-- Should we just not use inclusion from EvaluationContext?
data Context1 : Set where
  ceval     : (E1 : EvaluationContext1) → Context1
  csignl    : (S : Signal) → Context1
  cpresent₁ : (S : Signal) → (q : Term) → Context1
  cpresent₂ : (S : Signal) → (p : Term) → Context1
  cloop     : Context1
  cloopˢ₂   : (p : Term) → Context1
  cseq₂     : (p : Term) → Context1
  cshared   : (s : SharedVar) → (e : Expr) → Context1
  cvar      : (x : SeqVar) → (e : Expr) → Context1
  cif₁      : (x : SeqVar) → (q : Term) → Context1
  cif₂      : (x : SeqVar) → (p : Term) → Context1
  cenv      : (θ : Env) → Context1

Context : Set
Context = List Context1

_⟦_⟧c : Context → Term → Term
[]                       ⟦ p ⟧c = p
(ceval (epar₁ q) ∷ C)    ⟦ p ⟧c = (C ⟦ p ⟧c) ∥ q
(ceval (epar₂ p) ∷ C)    ⟦ q ⟧c = p          ∥ (C ⟦ q ⟧c)
(ceval (eseq q) ∷ C)     ⟦ p ⟧c = (C ⟦ p ⟧c) >> q
(ceval (eloopˢ q) ∷ C)   ⟦ p ⟧c = loopˢ (C ⟦ p ⟧c) q
(cseq₂ p ∷ C)            ⟦ q ⟧c = p          >> (C ⟦ q ⟧c)
(ceval (esuspend S) ∷ C) ⟦ p ⟧c = suspend (C ⟦ p ⟧c) S
(ceval etrap ∷ C)        ⟦ p ⟧c = trap (C ⟦ p ⟧c)
(csignl S ∷ C)           ⟦ p ⟧c = signl S (C ⟦ p ⟧c)
(cpresent₁ S q ∷ C)      ⟦ p ⟧c = present S ∣⇒ (C ⟦ p ⟧c) ∣⇒ q
(cpresent₂ S p ∷ C)      ⟦ q ⟧c = present S ∣⇒ p          ∣⇒ (C ⟦ q ⟧c)
(cloop ∷ C)              ⟦ p ⟧c = loop (C ⟦ p ⟧c)
(cloopˢ₂ p ∷ C)          ⟦ q ⟧c = loopˢ p (C ⟦ q ⟧c)
(cshared s e ∷ C)        ⟦ p ⟧c = shared s ≔ e in: (C ⟦ p ⟧c)
(cvar x e ∷ C)           ⟦ p ⟧c = var x ≔ e in: (C ⟦ p ⟧c)
(cif₁ x q ∷ C)           ⟦ p ⟧c = if x ∣⇒ (C ⟦ p ⟧c) ∣⇒ q
(cif₂ x p ∷ C)           ⟦ q ⟧c = if x ∣⇒ p          ∣⇒ (C ⟦ q ⟧c)
(cenv θ ∷ C)             ⟦ p ⟧c = ρ θ · (C ⟦ p ⟧c)

data _≐_⟦_⟧c : Term → Context → Term → Set where
  dchole     : ∀{p}                            → (p                    ≐  []                       ⟦ p ⟧c)
  dcpar₁     : ∀{p r q C}     → (p ≐ C ⟦ r ⟧c) → (p ∥ q                ≐  (ceval (epar₁ q) ∷ C)    ⟦ r ⟧c)
  dcpar₂     : ∀{p r q C}     → (q ≐ C ⟦ r ⟧c) → (p ∥ q                ≐  (ceval (epar₂ p) ∷ C)    ⟦ r ⟧c)
  dcseq₁     : ∀{p r q C}     → (p ≐ C ⟦ r ⟧c) → (p >> q               ≐  (ceval (eseq q) ∷ C)     ⟦ r ⟧c)
  dcseq₂     : ∀{p r q C}     → (q ≐ C ⟦ r ⟧c) → (p >> q               ≐  (cseq₂ p ∷ C)            ⟦ r ⟧c)
  dcsuspend  : ∀{p C r S}     → (p ≐ C ⟦ r ⟧c) → (suspend p S          ≐  (ceval (esuspend S) ∷ C) ⟦ r ⟧c)
  dctrap     : ∀{p C r}       → (p ≐ C ⟦ r ⟧c) → (trap p               ≐  (ceval etrap ∷ C)        ⟦ r ⟧c)
  dcsignl    : ∀{p C r S}     → (p ≐ C ⟦ r ⟧c) → (signl S p            ≐  (csignl S ∷ C)           ⟦ r ⟧c)
  dcpresent₁ : ∀{p r q C S}   → (p ≐ C ⟦ r ⟧c) → (present S ∣⇒ p ∣⇒ q   ≐  (cpresent₁ S q ∷ C)      ⟦ r ⟧c)
  dcpresent₂ : ∀{p r q C S}   → (q ≐ C ⟦ r ⟧c) → (present S ∣⇒ p ∣⇒ q   ≐  (cpresent₂ S p ∷ C)      ⟦ r ⟧c)
  dcloop     : ∀{p C r}       → (p ≐ C ⟦ r ⟧c) → (loop p               ≐  (cloop ∷ C)              ⟦ r ⟧c)
  dcloopˢ₁   : ∀{p q C r}     → (p ≐ C ⟦ r ⟧c) → (loopˢ p q            ≐  (ceval (eloopˢ q) ∷ C)   ⟦ r ⟧c)
  dcloopˢ₂   : ∀{p q C r}     → (q ≐ C ⟦ r ⟧c) → (loopˢ p q            ≐  (cloopˢ₂ p ∷ C)          ⟦ r ⟧c)
  dcshared   : ∀{p C r s e}   → (p ≐ C ⟦ r ⟧c) → (shared s ≔ e in: p   ≐  (cshared s e ∷ C)        ⟦ r ⟧c)
  dcvar      : ∀{p C r x e}   → (p ≐ C ⟦ r ⟧c) → (var x ≔ e in: p      ≐  (cvar x e ∷ C)           ⟦ r ⟧c)
  dcif₁      : ∀{p r q x C}   → (p ≐ C ⟦ r ⟧c) → (if x ∣⇒ p ∣⇒ q        ≐  (cif₁ x q ∷ C)           ⟦ r ⟧c)
  dcif₂      : ∀{p r q x C}   → (q ≐ C ⟦ r ⟧c) → (if x ∣⇒ p ∣⇒ q        ≐  (cif₂ x p ∷ C)           ⟦ r ⟧c)
  dcenv      : ∀{p C r θ}     → (p ≐ C ⟦ r ⟧c) → (ρ θ · p              ≐  (cenv θ ∷ C)             ⟦ r ⟧c)
