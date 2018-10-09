module context-properties where

open import utility
open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
open import Esterel.Lang.PotentialFunction
open import Esterel.Lang.PotentialFunction.Properties
  using (canₛ-⊆-FV ; canₛₕ-⊆-FV ; canθₛ-E₁⟦p⟧⊆canθₛ-p ; canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p)
open import Esterel.Environment
open import Esterel.Context
open import Esterel.Context.Properties public  -- 'public' for backward compatibility
open import Data.Product
  using (Σ ; Σ-syntax ; ∃ ; proj₁ ; proj₂ ; _,_ ; _,′_ ; _×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Data.Bool
  using (Bool ; true ; false ; if_then_else_)
open import Data.List
  using (List ; _∷_ ; [] ; _++_ ; map)
open import Data.List.Properties
  using (map-id ; map-cong ; map-compose)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using (++ˡ ; ++ʳ)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; zero ; suc ; _+_ ; _≟_)
open import Data.Nat.Properties.Simple
  using (+-comm)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import sn-calculus
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Function
  using (_∘_ ; id ; _∋_)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

infix 20 _~_
infix 20 _a~_


data _~_ : EvaluationContext → EvaluationContext → Set where
  hole  : [] ~ []
  parr  : ∀{p p' E E'} → E ~ E' → (epar₁ p ∷ E) ~ (epar₁ p' ∷ E')
  parl  : ∀{p p' E E'} → E ~ E' → (epar₂ p ∷ E) ~ (epar₂ p' ∷ E')
  seq   : ∀{p p' E E'} → E ~ E' → (eseq p ∷ E) ~ (eseq p' ∷ E')
  loopˢ : ∀{p p' E E'} → E ~ E' → (eloopˢ p ∷ E) ~ (eloopˢ p' ∷ E')
  susp  : ∀{S E E'} → E ~ E' → (esuspend S ∷ E) ~ (esuspend S ∷ E')
  trp   : ∀{E E'} → E ~ E' → (etrap ∷ E) ~ (etrap ∷ E')

data R : Term → Set where
  mit  : ∀{S} → R (emit S)
  <==  : ∀{s e} → R (s ⇐ e)
  :==  : ∀{x e} → R (x ≔ e)
  pres : ∀{S p q} → R (present S ∣⇒ p ∣⇒ q)
  iff  : ∀{x p q} → R (if x ∣⇒ p ∣⇒ q)
  shrd : ∀{s e p} → R (shared s ≔ e in: p)
  varr : ∀{x e p} → R (var x ≔ e in: p)

~ref : (E : EvaluationContext) → E ~ E
~ref [] = hole
~ref (epar₁ q ∷ E) = parr (~ref E)
~ref (epar₂ p ∷ E) = parl (~ref E)
~ref (eseq q ∷ E) = seq (~ref E)
~ref (eloopˢ q ∷ E) = loopˢ (~ref E)
~ref (esuspend S ∷ E) = susp (~ref E)
~ref (etrap ∷ E) = trp (~ref E)

~sym : ∀{E1 E2} → E1 ~ E2 → E2 ~ E1
~sym hole = hole
~sym (parr eq) = parr (~sym eq)
~sym (parl eq) = parl (~sym eq)
~sym (seq eq) = seq (~sym eq)
~sym (loopˢ eq) = loopˢ (~sym eq)
~sym (susp eq) = susp (~sym eq)
~sym (trp eq) = trp (~sym eq)

~:: : ∀{E E' Ei} → (Ei ∷ E) ~ (Ei ∷ E') → E ~ E'
~:: (parr ~) = ~
~:: (parl ~) = ~
~:: (seq ~) = ~
~:: (loopˢ ~) = ~
~:: (susp ~) = ~
~:: (trp ~) = ~


CB-rho-rho-imp-dist : ∀{p q θ θ' BV FV} → CorrectBinding ((ρ θ · p) ∥ (ρ θ' · q)) BV FV → distinct (Dom θ) (Dom θ')
CB-rho-rho-imp-dist (CBpar{BVp = BVp}{BVq = BVq} (CBρ cb) (CBρ cb₁) x x₁ x₂ x₃) = dist++b x

ddb-r-rec : ∀{E' q BV FV θ θ' r s} → CorrectBinding ((ρ θ · r) ∥ q) BV FV → q ≐ E' ⟦ (ρ θ' · s) ⟧e → (distinct (Dom θ) (Dom θ'))

ddb-r-rec {[]} {ρ θ' · p} (CBpar cb cb₁ x x₁ x₂ x₃) dehole = CB-rho-rho-imp-dist (CBpar cb cb₁ x x₁ x₂ x₃)
ddb-r-rec {.(epar₁ _) ∷ E'} (CBpar cb (CBpar cb₁ cb₂ x x₁ x₂ x₃) x₄ x₅ x₆ x₇) (depar₁ eq2)
  = ddb-r-rec {E'} (CBpar cb cb₁ (dist++ˡ x₄) (dist++ˡ x₅) (dist++ˡ x₆) (dist'++ˡ x₇)) eq2
ddb-r-rec {.(epar₂ _) ∷ E'} (CBpar cb (CBpar{BVp = BVp}{FVp = FVp@(S , s , xs)} cb₁ cb₂ x x₁ x₂ x₃) x₄ x₅ x₆ x₇) (depar₂ eq2)
  = ddb-r-rec {E'} (CBpar cb cb₂ (dist++ʳ{VL2 = BVp} x₄) (dist++ʳ{VL2 = BVp} x₅) (dist++ʳ{VL2 = FVp} x₆) (dist'++ʳ{V2 = xs} x₇)) eq2
ddb-r-rec {.(esuspend _) ∷ E'}{q = (suspend _ S)} (CBpar cb (CBsusp cb₁ x) x₁ x₂ x₃ x₄) (desuspend eq2)
  = ddb-r-rec {E'} (CBpar cb cb₁ x₁ x₂ (dist::{S = S} x₃) x₄) eq2
ddb-r-rec {.etrap ∷ E'} (CBpar cb (CBtrap cb₁) x₁ x₂ x₃ x₄) (detrap eq2)
  = ddb-r-rec {E'} (CBpar cb cb₁ x₁ x₂ x₃ x₄) eq2
ddb-r-rec {.(eseq _) ∷ E'} (CBpar cb (CBseq cb₁ cb₂ x) x₁ x₂ x₃ x₄) (deseq eq2)
  = ddb-r-rec ((CBpar cb cb₁ (dist++ˡ x₁) (dist++ˡ x₂) (dist++ˡ x₃) (dist'++ˡ x₄))) eq2
ddb-r-rec {.(eloopˢ _) ∷ E'} (CBpar cb (CBloopˢ cb₁ cb₂ x _) x₁ x₂ x₃ x₄) (deloopˢ eq2)
  = ddb-r-rec ((CBpar cb cb₁ (dist++ˡ x₁) (dist++ˡ x₂) (dist++ˡ x₃) (dist'++ˡ x₄))) eq2

dist++l2 : ∀{VL1 VL2 VL3} → (distinct (VL2 U̬ VL3) VL1) → (distinct VL2 VL1)
dist++l2 d = (distinct-sym (dist++ˡ (distinct-sym d)))
dist'++l2 : ∀{A VL1 VL2 VL3} → (distinct'{A} (VL2 ++ VL3) VL1) → (distinct' VL2 VL1)
dist'++l2 d = (distinct'-sym (dist'++ˡ (distinct'-sym d)))
dist++r2 : ∀{VL1 VL2 VL3} → (distinct (VL2 U̬ VL3) VL1) → (distinct VL3 VL1)
dist++r2{VL2 = VL2} d = (distinct-sym (dist++ʳ{VL2 = VL2} (distinct-sym d)))
dist'++r2 : ∀{A VL1 VL2 VL3} → (distinct'{A} (VL2 ++ VL3) VL1) → (distinct' VL3 VL1)
dist'++r2{VL2 = VL2} d = (distinct'-sym (dist'++ʳ{V2 = VL2} (distinct'-sym d)))

dist::2 :  ∀{VL1 VL2 S} → (distinct (+S S VL1) VL2) → (distinct VL1 VL2)
dist::2{S = S} d = (distinct-sym ( dist::{S = S} (distinct-sym d) ))

decomp-distinct-binding : ∀{E E' p q BV FV θ θ' r s} → CorrectBinding (p ∥ q) BV FV → p ≐ E ⟦ (ρ θ · r) ⟧e → q ≐ E' ⟦ (ρ θ' · s) ⟧e → (distinct (Dom θ) (Dom θ'))
decomp-distinct-binding {[]} {E} (CBpar cb cb₁ x₁ x₂ x₃ x₄) dehole eq2 = ddb-r-rec (CBpar cb cb₁ x₁ x₂ x₃ x₄) eq2
decomp-distinct-binding {x ∷ E} {[]} (CBpar cb cb₁ x₁ x₂ x₃ x₄) eq1 dehole = distinct-sym (ddb-r-rec {x ∷ E} (CBpar cb₁ cb (distinct-sym x₁) (distinct-sym x₃) (distinct-sym x₂) (distinct'-sym x₄)) eq1)
decomp-distinct-binding {.(epar₁ _) ∷ E} {x₁ ∷ E'} (CBpar{BVq = BVq} (CBpar cb cb₁ x x₂ x₃ x₄) cb₂ x₅ x₆ x₇ x₈) (depar₁ eq1) eq2
  = decomp-distinct-binding (CBpar cb cb₂ (dist++l2 x₅)  (dist++l2 x₆) (dist++l2 x₇) (dist'++l2 x₈)) eq1 eq2
decomp-distinct-binding {.(epar₂ _) ∷ E} {x₁ ∷ E'} (CBpar (CBpar{BVp = BVp}{FVp = FVp@(S , s , xs)}{BVq = BVq} cb cb₁ x x₂ x₃ x₄) cb₂ x₅ x₆ x₇ x₈) (depar₂ eq1) eq2
  = decomp-distinct-binding (CBpar cb₁ cb₂ (dist++r2{VL2 = BVp} x₅)  (dist++r2{VL2 = FVp} x₆) (dist++r2{VL2 = BVp} x₇) (dist'++r2{VL2 = xs} x₈)) eq1 eq2
decomp-distinct-binding {.(eseq _) ∷ E} {x₁ ∷ E'} (CBpar (CBseq cb cb₁ x) cb₂ x₂ x₃ x₄ x₅) (deseq eq1) eq2
  = decomp-distinct-binding {E} ((CBpar cb cb₂ (dist++l2 x₂) (dist++l2 x₃) (dist++l2 x₄) (dist'++l2 x₅))) eq1 eq2
decomp-distinct-binding {.(eloopˢ _) ∷ E} {x₁ ∷ E'} (CBpar (CBloopˢ cb cb₁ x _) cb₂ x₂ x₃ x₄ x₅) (deloopˢ eq1) eq2
  = decomp-distinct-binding {E} ((CBpar cb cb₂ (dist++l2 x₂) (dist++l2 x₃) (dist++l2 x₄) (dist'++l2 x₅))) eq1 eq2
decomp-distinct-binding {.(esuspend _) ∷ E} {x₁ ∷ E'} {p = (suspend _ S)}  (CBpar (CBsusp cb x) cb₁ x₂ x₃ x₄ x₅) (desuspend eq1) eq2
  = decomp-distinct-binding {E} (CBpar cb cb₁ x₂ ( (dist::2{S = S} x₃) ) x₄ x₅) eq1 eq2
decomp-distinct-binding {.etrap ∷ E} {x₁ ∷ E'} (CBpar (CBtrap cb) cb₁ x₂ x₃ x₄ x₅) (detrap eq1) eq2
  = decomp-distinct-binding ((CBpar cb cb₁ x₂ x₃ x₄ x₅)) eq1 eq2

data _a~_ : EvaluationContext → EvaluationContext → Set where
  parr  : ∀{p p' E E'} → E a~ E' → (epar₁ p ∷ E) a~ (epar₁ p' ∷ E')
  parl  : ∀{p p' E E'} → E a~ E' → (epar₂ p ∷ E) a~ (epar₂ p' ∷ E')
  seq   : ∀{p p' E E'} → E a~ E' → (eseq p ∷ E) a~ (eseq p' ∷ E')
  loopˢ : ∀{p p' E E'} → E a~ E' → (eloopˢ p ∷ E) a~ (eloopˢ p' ∷ E')
  susp  : ∀{S E E'} → E a~ E' → (esuspend S ∷ E) a~ (esuspend S ∷ E')
  trp   : ∀{E E'} → E a~ E' → (etrap ∷ E) a~ (etrap ∷ E')

  par   : ∀{p q E E'}  → (epar₂ p ∷ E) a~ (epar₁ q ∷ E')
  par2  : ∀{p q E E'}  → (epar₁ p ∷ E) a~ (epar₂ q ∷ E')

a~-sym : ∀{E E'} → E a~ E' → E' a~ E
a~-sym (parr ~) = parr (a~-sym ~)
a~-sym (parl ~) = parl (a~-sym ~)
a~-sym (seq ~) = seq (a~-sym ~)
a~-sym (loopˢ ~) = loopˢ (a~-sym ~)
a~-sym (susp ~) = susp (a~-sym ~)
a~-sym (trp ~) = trp (a~-sym ~)
a~-sym par = par2
a~-sym par2 = par

decomp-maint-bind : ∀{E E' p r s θ θ' BV FV} → CorrectBinding p BV FV
                      → p ≐ E ⟦ (ρ θ · r ) ⟧e
                      → p ≐ E' ⟦ (ρ θ' · s ) ⟧e
                      → (E ≡ E' × r ≡ s × θ ≡ θ') ⊎ ((distinct (Dom θ) (Dom θ')) × E a~ E')

decomp-maint-bind {[]} {[]} {.(ρ _ · _)} bv dehole dehole = inj₁ (refl , refl , refl)
decomp-maint-bind {[]} {x ∷ E'} {.(ρ _ · _)} bv dehole ()
decomp-maint-bind {.(epar₁ _) ∷ E} {[]} {.(_ ∥ _)} bv (depar₁ d1) ()

decomp-maint-bind {.(epar₂ _) ∷ E} {[]} {.(_ ∥ _)} bv (depar₂ d1) ()
decomp-maint-bind {.(eseq _) ∷ E} {[]} {.(_ >> _)} bv (deseq d1) ()
decomp-maint-bind {.(eloopˢ _) ∷ E} {[]} {.(loopˢ _ _)} bv (deloopˢ d1) ()
decomp-maint-bind {.(esuspend _) ∷ E} {[]} {.(suspend _ _)} bv (desuspend d1) ()
decomp-maint-bind {.etrap ∷ E} {[]} {.(trap _)} bv (detrap d1) ()
decomp-maint-bind {(epar₁ q) ∷ E} {(epar₂ p) ∷ E'} {.(_ ∥ _)} bv (depar₁ d1) (depar₂ d2) = inj₂ ((decomp-distinct-binding bv d1 d2) ,  par2 )
decomp-maint-bind {.(epar₂ _) ∷ E} {.(epar₁ _) ∷ E'} {.(_ ∥ _)} bv (depar₂ d1) (depar₁ d2) with (decomp-distinct-binding bv d2 d1)
... | c = inj₂ ((distinct-sym c) , par)
decomp-maint-bind {.(epar₁ _) ∷ E} {.(epar₁ _) ∷ E'} {.(_ ∥ _)} (CBpar bv bv₁ x x₁ x₂ x₃) (depar₁ d1) (depar₁ d2) with decomp-maint-bind bv d1 d2
... | inj₁ (eq1 , eq2 , eq3) rewrite eq1 | eq2 | eq3 = inj₁ (refl , refl , refl)
... | inj₂ (y , neg) = inj₂ (y , parr neg)
decomp-maint-bind {.(epar₂ _) ∷ E} {.(epar₂ _) ∷ E'} {.(_ ∥ _)} (CBpar bv bv₁ x x₁ x₂ x₃) (depar₂ d1) (depar₂ d2) with decomp-maint-bind bv₁ d1 d2
... | inj₁ (eq1 , eq2 , eq3) rewrite eq1 | eq2 | eq3 = inj₁ (refl , refl , refl)
... | inj₂ (y , neg) = inj₂ (y , parl neg)
decomp-maint-bind {.(eseq _) ∷ E} {.(eseq _) ∷ E'} {.(_ >> _)} (CBseq bv bv₁ x) (deseq d1) (deseq d2) with decomp-maint-bind bv d1 d2
... | inj₁ (eq1 , eq2 , eq3) rewrite eq1 | eq2 | eq3 = inj₁ (refl , refl , refl)
... | inj₂ (y , neg) = inj₂ (y , seq neg)
decomp-maint-bind {.(eloopˢ _) ∷ E} {.(eloopˢ _) ∷ E'} {.(loopˢ _ _)} (CBloopˢ bv bv₁ x _) (deloopˢ d1) (deloopˢ d2) with decomp-maint-bind bv d1 d2
... | inj₁ (eq1 , eq2 , eq3) rewrite eq1 | eq2 | eq3 = inj₁ (refl , refl , refl)
... | inj₂ (y , neg) = inj₂ (y , loopˢ neg)
decomp-maint-bind {.(esuspend _) ∷ E} {.(esuspend _) ∷ E'} {.(suspend _ _)} (CBsusp bv x) (desuspend d1) (desuspend d2) with decomp-maint-bind bv d1 d2
... | inj₁ (eq1 , eq2 , eq3) rewrite eq1 | eq2 | eq3 = inj₁ (refl , refl , refl)
... | inj₂ (y , neg) = inj₂ (y , susp neg)
decomp-maint-bind {.etrap ∷ E} {.etrap ∷ E'} {.(trap _)} (CBtrap bv) (detrap d1) (detrap d2) with decomp-maint-bind bv d1 d2
... | inj₁ (eq1 , eq2 , eq3) rewrite eq1 | eq2 | eq3 = inj₁ (refl , refl , refl)
... | inj₂ (y , neg) = inj₂ (y , trp neg)

data ->E-view : ∀{p q pin qin E θ θ'} → (ρ θ · p) sn⟶₁ (ρ θ' · q) → p ≐ E ⟦ pin ⟧e →  q ≐ E ⟦ qin ⟧e → Set where
  vmerge :  ∀{θ₁ θ₂ r p E dec} → ∀{dec2 : E ⟦ p ⟧e ≐ E ⟦ p ⟧e} → (->E-view (rmerge{θ₁}{θ₂}{r}{p}{E} dec) dec dec2)
  vis-present : ∀{θ S r p q E S∈ ineq dec} → ∀{dec2 : E ⟦ p ⟧e ≐ E ⟦ p ⟧e} → (->E-view (ris-present{θ}{S}{r}{p}{q}{E} S∈ ineq dec) dec dec2)
  vis-absent : ∀{θ S r p q E S∈ ineq dec} → ∀{dec2 : E ⟦ q ⟧e ≐ E ⟦ q ⟧e} → (->E-view (ris-absent{θ}{S}{r}{p}{q}{E} S∈ ineq dec) dec dec2)
  vemit : ∀{θ r S E S∈ ¬S≡a dec} → ∀{dec2 : E ⟦ nothin ⟧e ≐ E ⟦ nothin ⟧e} → (->E-view (remit{θ}{r}{S}{E} S∈ ¬S≡a dec) dec dec2)
  vraise-shared : ∀{θ r s e p E e' dec} → ∀{dec2 : E ⟦ (ρ (Θ SigMap.empty ShrMap.[ s ↦ (SharedVar.old ,′ (δ e'))] VarMap.empty) · p) ⟧e ≐ E ⟦ (ρ (Θ SigMap.empty ShrMap.[ s ↦ (SharedVar.old ,′ (δ e'))] VarMap.empty) · p) ⟧e}
                  → (->E-view (rraise-shared{θ}{r}{s}{e}{p}{E} e' dec) dec dec2)
  vset-shared-value-old :  ∀{θ r s e E e' s∈ ineq dec} → ∀{dec2 : E ⟦ nothin ⟧e ≐ E ⟦ nothin ⟧e} → (->E-view (rset-shared-value-old{θ}{r}{s}{e}{E} e' s∈ ineq dec) dec dec2)
  vset-shared-value-new :  ∀{θ r s e E e' s∈ ineq dec} → ∀{dec2 : E ⟦ nothin ⟧e ≐ E ⟦ nothin ⟧e} → (->E-view (rset-shared-value-new{θ}{r}{s}{e}{E} e' s∈ ineq dec) dec dec2)
  vraise-var : ∀{θ r x p e E e' dec} → ∀{dec2 : E ⟦ (ρ (Θ SigMap.empty ShrMap.empty VarMap.[ x ↦ δ e' ]) · p) ⟧e ≐ E ⟦ (ρ (Θ SigMap.empty ShrMap.empty VarMap.[ x ↦ δ e' ]) · p) ⟧e}
               → (->E-view (rraise-var{θ}{r}{x}{p}{e}{E} e' dec) dec dec2)

  vset-var : ∀{θ r x e E x∈ e' dec} → ∀{dec2 : E ⟦ nothin ⟧e ≐ E ⟦ nothin ⟧e}→  (->E-view (rset-var{θ}{r}{x}{e}{E} x∈ e' dec) dec dec2)
  vif-false : ∀{θ r p q x E x∈ ineq dec} → ∀{dec2 : E ⟦ q ⟧e ≐ E ⟦ q ⟧e} → (->E-view (rif-false{θ}{r}{p}{q}{x}{E} x∈ ineq dec) dec dec2)
  vif-true : ∀{θ r p q x E n x∈ ineq dec} → ∀{dec2 : E ⟦ p ⟧e ≐ E ⟦ p ⟧e} → (->E-view (rif-true{θ}{r}{p}{q}{x}{E}{n} x∈ ineq dec) dec dec2)

data ->pot-view : ∀{p θ q θ'} → (ρ θ · p) sn⟶₁ (ρ θ' · q) → p ≡ q → Set where
  vabsence : ∀{θ p} S S∈ θS≡unknown S∉can-p-θ → (->pot-view (rabsence{θ}{p}{S} S∈ θS≡unknown S∉can-p-θ) refl)
  vreadyness : ∀{θ p} s s∈ θs≡old⊎θs≡new s∉can-p-θ → (->pot-view (rreadyness{θ}{p}{s} s∈ θs≡old⊎θs≡new s∉can-p-θ) refl)

data ->θview :  ∀{p θ q θ'} → (ρ θ · p) sn⟶₁ (ρ θ' · q) → Set where
  ->θE-view   :  ∀{p q pin qin E θ θ'}
               → ∀{red : (ρ θ · p) sn⟶₁ (ρ θ' · q)}
               → ∀{pin : p ≐ E ⟦ pin ⟧e}
               → ∀{qin : q ≐ E ⟦ qin ⟧e}
               → ->E-view red pin qin
               → ->θview red

  ->θpot-view : ∀{p θ q θ'}
                → ∀{red : (ρ θ · p) sn⟶₁ (ρ θ' · q)}
                → ∀{eq : p ≡ q}
                → ->pot-view red eq
                → ->θview red

-- views for the term inside an ->E-view reduction
data ->E-view-term : Term → Set where
  evt-merge        : ∀ {θ p}   → ->E-view-term (ρ θ · p)
  evt-present      : ∀ {S p q} → ->E-view-term (present S ∣⇒ p ∣⇒ q)
  evt-emit         : ∀ {S}     → ->E-view-term (emit S)
  evt-raise-shared : ∀ {s e p} → ->E-view-term (shared s ≔ e in: p)
  evt-set-shared   : ∀ {s e}   → ->E-view-term (s ⇐ e)
  evt-raise-var    : ∀ {x e p} → ->E-view-term (var x ≔ e in: p)
  evt-set-var      : ∀ {x e}   → ->E-view-term (x ≔ e)
  evt-if           : ∀ {x p q} → ->E-view-term (if x ∣⇒ p ∣⇒ q)


->E-view-inner-term : ∀ {E pin poin p po θ θo} →
  { p≐E⟦pin⟧       :  p  ≐ E ⟦ pin  ⟧e } →
  { po≐E⟦poin⟧     :  po ≐ E ⟦ poin ⟧e } →
  { ρθ·psn⟶₁ρθo·po  :  ρ θ · p sn⟶₁ ρ θo · po } →
  ->E-view  ρθ·psn⟶₁ρθo·po  p≐E⟦pin⟧  po≐E⟦poin⟧ →
  ->E-view-term pin
->E-view-inner-term vmerge                = evt-merge
->E-view-inner-term vis-present           = evt-present
->E-view-inner-term vis-absent            = evt-present
->E-view-inner-term vemit                 = evt-emit
->E-view-inner-term vraise-shared         = evt-raise-shared
->E-view-inner-term vset-shared-value-old = evt-set-shared
->E-view-inner-term vset-shared-value-new = evt-set-shared
->E-view-inner-term vraise-var            = evt-raise-var
->E-view-inner-term vset-var              = evt-set-var
->E-view-inner-term vif-false             = evt-if
->E-view-inner-term vif-true              = evt-if


-- terms inside the hole of an ->E-view cannot be done
done-E-view-term-disjoint : ∀ {p} → done p → ->E-view-term p → ⊥
done-E-view-term-disjoint (dhalted hnothin) ()
done-E-view-term-disjoint (dhalted (hexit n)) ()
done-E-view-term-disjoint (dpaused ppause) ()
done-E-view-term-disjoint (dpaused (pseq p/paused)) ()
done-E-view-term-disjoint (dpaused (ploopˢ p/paused)) ()
done-E-view-term-disjoint (dpaused (ppar p/paused q/paused)) ()
done-E-view-term-disjoint (dpaused (psuspend p/paused)) ()
done-E-view-term-disjoint (dpaused (ptrap p/paused)) ()


unwrap-rho : ∀{E₁ E p θ θ' pin q qin po qo}
             → (red : (ρ θ · p) sn⟶₁ (ρ θ' · q))
             → (peq : p ≐ (E₁ ∷ E) ⟦ pin ⟧e)
             → (qeq : q ≐ (E₁ ∷ E) ⟦ qin ⟧e)
             → (poeq : po ≐ E ⟦ pin ⟧e)
             → (qoeq : qo ≐ E ⟦ qin ⟧e)
             → (->E-view red peq qeq)
             → Σ[ redo ∈ (ρ θ · po) sn⟶₁ (ρ θ' · qo) ] (->E-view redo poeq qoeq)
unwrap-rho{E = E}{θ = θ}{θ' = θ'}{qin = qin}{po = po} red@(rmerge{θ₁}{θ₂} .peq) peq qeq poeq qoeq (vmerge) with sym (unplug qoeq)
... | refl = rmerge poeq , vmerge{θ}{_}{po}{qin}{E}{poeq}
unwrap-rho (ris-present S∈ ineq .peq) peq qeq poeq qoeq vis-present with sym (unplug qoeq)
... | refl = (ris-present S∈ ineq poeq) , vis-present
unwrap-rho (ris-absent S∈ ineq .peq) peq qeq poeq qoeq vis-absent with sym (unplug qoeq)
... | refl = (ris-absent S∈ ineq poeq) , vis-absent
unwrap-rho (remit x eq .peq) peq qeq poeq qoeq vemit with sym (unplug qoeq)
... | refl = (remit x eq poeq) , vemit
unwrap-rho (rraise-shared x .peq) peq qeq poeq qoeq vraise-shared with sym (unplug qoeq)
... | refl = rraise-shared x poeq , vraise-shared
unwrap-rho (rset-shared-value-old a b c .peq) peq qeq poeq qoeq vset-shared-value-old with sym (unplug qoeq)
... | refl = (rset-shared-value-old a b c poeq) , vset-shared-value-old
unwrap-rho (rset-shared-value-new a b c .peq) peq qeq poeq qoeq vset-shared-value-new with sym (unplug qoeq)
... | refl = (rset-shared-value-new a b c poeq) , vset-shared-value-new
unwrap-rho (rraise-var a .peq) peq qeq poeq qoeq vraise-var with sym (unplug qoeq)
... | refl = (rraise-var a poeq) , vraise-var
unwrap-rho (rset-var a b .peq) peq qeq poeq qoeq vset-var with sym (unplug qoeq)
... | refl =  (rset-var a b poeq)  ,  vset-var
unwrap-rho (rif-false a b .peq) peq qeq poeq qoeq vif-false with sym (unplug qoeq)
... | refl = rif-false a b poeq , vif-false
unwrap-rho (rif-true a b .peq) peq qeq poeq qoeq vif-true with sym (unplug qoeq)
... | refl = rif-true a b poeq , vif-true

wrap-rho : ∀{θ θ' pout qout pin qin E po qo}
           → (red : (ρ θ · pout) sn⟶₁ (ρ θ' · qout))
           → (peq : pout ≐ E ⟦ pin ⟧e)
           → (qeq : qout ≐ E ⟦ qin ⟧e)
           → ->E-view red peq qeq
           → (E₁ : EvaluationContext1)
           → (poeq : po ≐ (E₁ ∷ E) ⟦ pin ⟧e)
           → (qoeq : qo ≐ (E₁ ∷ E) ⟦ qin ⟧e)
           → Σ[ redo ∈ (ρ θ · po) sn⟶₁ (ρ θ' · qo) ] ->E-view redo poeq qoeq
wrap-rho .(rmerge peq) peq qeq vmerge Eo poeq qoeq with sym (unplug qoeq)
... | refl = rmerge poeq , vmerge
wrap-rho (ris-present S∈ ineq .peq) peq qeq vis-present Eo poeq qoeq with sym (unplug qoeq)
... | refl = ris-present S∈ ineq poeq , vis-present
wrap-rho (ris-absent S∈ ineq .peq) peq qeq vis-absent Eo poeq qoeq with sym (unplug qoeq)
... | refl = ris-absent S∈ ineq poeq , vis-absent
wrap-rho (remit S∈ eq .peq) peq qeq vemit Eo poeq qoeq with sym (unplug qoeq)
... | refl = remit S∈ eq poeq , vemit
wrap-rho (rraise-shared a .peq) peq qeq vraise-shared Eo poeq qoeq with sym (unplug qoeq)
... | refl = rraise-shared a poeq , vraise-shared
wrap-rho (rset-shared-value-old a b c .peq) peq qeq vset-shared-value-old Eo poeq qoeq with sym (unplug qoeq)
... | refl = rset-shared-value-old a b c poeq , vset-shared-value-old
wrap-rho (rset-shared-value-new a b c .peq) peq qeq vset-shared-value-new Eo poeq qoeq with sym (unplug qoeq)
... | refl = rset-shared-value-new a b c poeq , vset-shared-value-new
wrap-rho (rraise-var a .peq) peq qeq vraise-var Eo poeq qoeq with sym (unplug qoeq)
... | refl = rraise-var a poeq , vraise-var
wrap-rho (rset-var a b .peq) peq qeq vset-var Eo poeq qoeq with sym (unplug qoeq)
... | refl = rset-var a b poeq , vset-var
wrap-rho (rif-false a b .peq) peq qeq vif-false Eo poeq qoeq with sym (unplug qoeq)
... | refl = rif-false a b poeq , vif-false
wrap-rho (rif-true a b .peq) peq qeq vif-true Eo poeq qoeq with sym (unplug qoeq)
... | refl = rif-true a b poeq , vif-true


wrap-rho-pot : ∀ {E₁ pin θ θ' pin≡pin E₁⟦nothin⟧ BV FV} →
  -- distinct (Dom θ) (FV (E₁ ⟦ nothin ⟧))
  E₁⟦nothin⟧ ≐ (E₁ ∷ []) ⟦ nothin ⟧e →
  CorrectBinding E₁⟦nothin⟧ BV FV →
  distinct (Dom θ) FV →

  (ρθpinsn⟶₁ρθ'qin  :  ρ θ · pin sn⟶₁ ρ θ' · pin) →
  ->pot-view  ρθpinsn⟶₁ρθ'qin  pin≡pin →

  ∃ λ po →
    Σ[ po≐E₁⟦pin⟧             ∈  po ≐ (E₁ ∷ []) ⟦ pin ⟧e ]
    Σ[ ρθE₁⟦pin⟧sn⟶₁ρθ'E₁⟦pin⟧  ∈  ρ θ · po sn⟶₁ ρ θ' · po ]
      ->pot-view  ρθE₁⟦pin⟧sn⟶₁ρθ'E₁⟦pin⟧ refl
wrap-rho-pot {epar₁ q} {pin} {θ} {FV = FV} (depar₁ dehole) cb Domθ≠FV
  .(rabsence {S = S} S∈ θS≡unknown S∉canθ-θ-p)
  (vabsence S S∈ θS≡unknown S∉canθ-θ-p)
  = _ , depar₁ dehole ,
    rabsence {S = S} S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env ,
    vabsence S S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env
  where
    S∉canθ-θ-E₁⟦p⟧-[]env =
      S∉canθ-θ-p ∘
      canθₛ-E₁⟦p⟧⊆canθₛ-p (sig θ) 0 []env (depar₁ dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        S (proj₁ Domθ≠FV (Signal.unwrap S) S∈)
wrap-rho-pot {epar₂ p} {pin} {θ} {FV = FV} (depar₂ dehole) cb Domθ≠FV
  .(rabsence {S = S} S∈ θS≡unknown S∉can-p-θ)
  (vabsence S S∈ θS≡unknown S∉can-p-θ)
  = _ , depar₂ dehole ,
    rabsence {S = S} S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env ,
    vabsence S S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env
  where
    S∉canθ-θ-E₁⟦p⟧-[]env =
      S∉can-p-θ ∘
      canθₛ-E₁⟦p⟧⊆canθₛ-p (sig θ) 0 []env (depar₂ dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        S (proj₁ Domθ≠FV (Signal.unwrap S) S∈)
wrap-rho-pot {eseq q} {pin} {θ} {FV = FV} (deseq dehole) cb Domθ≠FV
  .(rabsence {S = S} S∈ θS≡unknown S∉can-p-θ)
  (vabsence S S∈ θS≡unknown S∉can-p-θ)
  = _ , deseq dehole ,
    rabsence {S = S} S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env ,
    vabsence S S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env
  where
    S∉canθ-θ-E₁⟦p⟧-[]env =
      S∉can-p-θ ∘
      canθₛ-E₁⟦p⟧⊆canθₛ-p (sig θ) 0 []env (deseq dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        S (proj₁ Domθ≠FV (Signal.unwrap S) S∈)
wrap-rho-pot {eloopˢ q} {pin} {θ} {FV = FV} (deloopˢ dehole) cb Domθ≠FV
  .(rabsence {S = S} S∈ θS≡unknown S∉can-p-θ)
  (vabsence S S∈ θS≡unknown S∉can-p-θ)
  = _ , deloopˢ dehole ,
    rabsence {S = S} S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env ,
    vabsence S S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env
  where
    S∉canθ-θ-E₁⟦p⟧-[]env =
      S∉can-p-θ ∘
      canθₛ-E₁⟦p⟧⊆canθₛ-p (sig θ) 0 []env (deloopˢ dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        S (proj₁ Domθ≠FV (Signal.unwrap S) S∈) 
wrap-rho-pot {esuspend S'} {pin} {θ} {FV = FV} (desuspend dehole) cb Domθ≠FV
  .(rabsence {S = S} S∈ θS≡unknown S∉can-p-θ)
  (vabsence S S∈ θS≡unknown S∉can-p-θ)
  = _ , desuspend dehole ,
    rabsence {S = S} S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env ,
    vabsence S S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env
  where
    S∉canθ-θ-E₁⟦p⟧-[]env =
      S∉can-p-θ ∘
      canθₛ-E₁⟦p⟧⊆canθₛ-p (sig θ) 0 []env (desuspend dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        S (proj₁ Domθ≠FV (Signal.unwrap S) S∈)
wrap-rho-pot {etrap} {pin} {θ} {FV = FV} (detrap dehole) cb Domθ≠FV
  .(rabsence {S = S} S∈ θS≡unknown S∉can-p-θ)
  (vabsence S S∈ θS≡unknown S∉can-p-θ)
  = _ , detrap dehole ,
    rabsence {S = S} S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env ,
    vabsence S S∈ θS≡unknown S∉canθ-θ-E₁⟦p⟧-[]env
  where
    S∉canθ-θ-E₁⟦p⟧-[]env =
      S∉can-p-θ ∘
      canθₛ-E₁⟦p⟧⊆canθₛ-p (sig θ) 0 []env (detrap dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        S (proj₁ Domθ≠FV (Signal.unwrap S) S∈)
wrap-rho-pot {epar₁ q} {pin} {θ} {FV = FV} (depar₁ dehole) cb Domθ≠FV
  .(rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉can-p-θ)
  (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
  = _ , depar₁ dehole ,
    rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env ,
    vreadyness s s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env
  where
    s∉canθ-θ-E₁⟦p⟧-[]env =
      s∉can-p-θ ∘
      canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p (sig θ) 0 []env (depar₁ dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        s (proj₁ (proj₂ Domθ≠FV) (SharedVar.unwrap s) s∈)
wrap-rho-pot {epar₂ p} {pin} {θ} {FV = FV} (depar₂ dehole) cb Domθ≠FV
  .(rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉can-p-θ)
  (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
  = _ , depar₂ dehole ,
    rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env ,
    vreadyness s s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env
  where
    s∉canθ-θ-E₁⟦p⟧-[]env =
      s∉can-p-θ ∘
      canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p (sig θ) 0 []env (depar₂ dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        s (proj₁ (proj₂ Domθ≠FV) (SharedVar.unwrap s) s∈)
wrap-rho-pot {eseq q} {pin} {θ} {FV = FV} (deseq dehole) cb Domθ≠FV
  .(rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉can-p-θ)
  (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
  = _ , deseq dehole ,
    rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env ,
    vreadyness s s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env
  where
    s∉canθ-θ-E₁⟦p⟧-[]env =
      s∉can-p-θ ∘
      canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p (sig θ) 0 []env (deseq dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        s (proj₁ (proj₂ Domθ≠FV) (SharedVar.unwrap s) s∈)
wrap-rho-pot {eloopˢ q} {pin} {θ} {FV = FV} (deloopˢ dehole) cb Domθ≠FV
  .(rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉can-p-θ)
  (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
  = _ , deloopˢ dehole ,
    rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env ,
    vreadyness s s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env
  where
    s∉canθ-θ-E₁⟦p⟧-[]env =
      s∉can-p-θ ∘
      canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p (sig θ) 0 []env (deloopˢ dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        s (proj₁ (proj₂ Domθ≠FV) (SharedVar.unwrap s) s∈)
wrap-rho-pot {esuspend S} {pin} {θ} {FV = FV} (desuspend dehole) cb Domθ≠FV
  .(rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉can-p-θ)
  (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
  = _ , desuspend dehole ,
    rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env ,
    vreadyness s s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env
  where
    s∉canθ-θ-E₁⟦p⟧-[]env =
      s∉can-p-θ ∘
      canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p (sig θ) 0 []env (desuspend dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        s (proj₁ (proj₂ Domθ≠FV) (SharedVar.unwrap s) s∈)
wrap-rho-pot {etrap} {pin} {θ} {FV = FV} (detrap dehole) cb Domθ≠FV
  .(rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉can-p-θ)
  (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
  = _ , detrap dehole ,
    rreadyness {s = s} s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env ,
    vreadyness s s∈ θs≡old⊎θs≡new s∉canθ-θ-E₁⟦p⟧-[]env
  where
    s∉canθ-θ-E₁⟦p⟧-[]env =
      s∉can-p-θ ∘
      canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p (sig θ) 0 []env (detrap dehole) cb
        (subst (λ dom → distinct' dom (proj₁ FV))
          (sym (map-id (proj₁ (Dom θ))))
          (proj₁ Domθ≠FV))
        s (proj₁ (proj₂ Domθ≠FV) (SharedVar.unwrap s) s∈)


-- p and p' are not important at all; we use them to extract the
-- distinctness condition of FV E₁ and Dom θ
wrap-rho-pot' : ∀ {θ θ' E₁ E pin p p' BV FV} →
  p ≐ (E₁ ∷ E) ⟦ ρ θ · p' ⟧e →
  CorrectBinding p BV FV →

  (ρθpinsn⟶₁ρθ'pin  :  ρ θ · pin sn⟶₁ ρ θ' · pin) →
  ->pot-view  ρθpinsn⟶₁ρθ'pin  refl →

  ∃ λ po →
    Σ[ po≐E₁⟦pin⟧             ∈  po ≐ (E₁ ∷ []) ⟦ pin ⟧e ]
    Σ[ ρθE₁⟦pin⟧sn⟶₁ρθ'E₁⟦pin⟧  ∈  ρ θ · po sn⟶₁ ρ θ' · po ]
      ->pot-view  ρθE₁⟦pin⟧sn⟶₁ρθ'E₁⟦pin⟧ refl
wrap-rho-pot' {θ} (depar₁ p≐E⟦ρθp'⟧) (CBpar cbp cbq _ _ BVp≠FVq _) ρθpinsn⟶₁ρθ'pin pot
  with binding-extract cbp p≐E⟦ρθp'⟧
... | (BVρθ , _) , (BVρθ⊆BVp , _) , CBρ _ =
  wrap-rho-pot (depar₁ dehole) cb' (⊆-respect-distinct-left (∪-unjoin-⊆ˡ {xs³ = Dom θ} BVρθ⊆BVp) BVp≠FVq) ρθpinsn⟶₁ρθ'pin pot
  where cb' = CBpar CBnothing cbq distinct-empty-left distinct-empty-left distinct-empty-left (λ _ ())
wrap-rho-pot' {θ} (depar₂ q≐E⟦ρθp'⟧) (CBpar cbp cbq _ FVp≠BVq _ _) ρθpinsn⟶₁ρθ'pin pot
  with binding-extract cbq q≐E⟦ρθp'⟧
... | (BVρθ , _) , (BVρθ⊆BVq , _) , CBρ _ = -- Test your eyesight :  1) ⊃   2) ∪   3) ⊂   4) ∩
  wrap-rho-pot (depar₂ dehole) cb' -- hack to delete (_∪ base) in (distinct  (FVq ∪ base))
    (⊆-respect-distinct-right (∪-join-⊆ ⊆-refl ⊆-empty-left) -- using (FVq ∪ base) ⊆ FVq here
      (⊆-respect-distinct-left (∪-unjoin-⊆ˡ {xs³ = Dom θ} BVρθ⊆BVq) (distinct-sym FVp≠BVq)))
    ρθpinsn⟶₁ρθ'pin pot
  where cb' = CBpar cbp CBnothing distinct-empty-right distinct-empty-right distinct-empty-right (λ _ _ ())
wrap-rho-pot' {θ} (deseq p≐E⟦ρθp'⟧) (CBseq cbp cbq BVp≠FVq) ρθpinsn⟶₁ρθ'pin pot
  with binding-extract cbp p≐E⟦ρθp'⟧
... | (BVρθ , _) , (BVρθ⊆BVp , _) , CBρ _ =
  wrap-rho-pot (deseq dehole) cb' (⊆-respect-distinct-left (∪-unjoin-⊆ˡ {xs³ = Dom θ} BVρθ⊆BVp) BVp≠FVq) ρθpinsn⟶₁ρθ'pin pot
  where cb' = CBseq CBnothing cbq distinct-empty-left
wrap-rho-pot' {θ} (deloopˢ p≐E⟦ρθp'⟧) (CBloopˢ cbp cbq BVp≠FVq BVq≠FVq) ρθpinsn⟶₁ρθ'pin pot
  with binding-extract cbp p≐E⟦ρθp'⟧
... | (BVρθ , _) , (BVρθ⊆BVp , _) , CBρ _ =
  wrap-rho-pot (deloopˢ dehole) cb' (⊆-respect-distinct-left (∪-unjoin-⊆ˡ {xs³ = Dom θ} BVρθ⊆BVp) BVp≠FVq) ρθpinsn⟶₁ρθ'pin pot
  where cb' = CBloopˢ CBnothing cbq distinct-empty-left BVq≠FVq
wrap-rho-pot' {θ} (desuspend p≐E⟦ρθp'⟧) (CBsusp cb [S]≠BVp) ρθpinsn⟶₁ρθ'pin pot
  with binding-extract cb p≐E⟦ρθp'⟧
... | (BVρθ , _) , (BVρθ⊆BVp , _) , CBρ _ =
  wrap-rho-pot (desuspend dehole) cb'
    ((distinct'-sym (⊆¹-respect-distinct'-right
                      (proj₁ (∪¹-unjoin-⊆¹ (proj₁ (Dom θ)) (proj₁ BVρθ⊆BVp))) [S]≠BVp)) ,′
     (λ _ _ ()) ,′ (λ _ _ ()))
    ρθpinsn⟶₁ρθ'pin pot
  where cb' = CBsusp CBnothing (λ _ _ ())
wrap-rho-pot' {θ} (detrap p≐E⟦ρθp'⟧) cb@(CBtrap cb') ρθpinsn⟶₁ρθ'pin pot =
  wrap-rho-pot (detrap dehole) (CBtrap CBnothing) distinct-empty-right ρθpinsn⟶₁ρθ'pin pot



E-view-main-bind : ∀{El Er p il ir iol ior ql qr θ θl θr }
                    → ∀{redl : (ρ θ · p) sn⟶₁ (ρ θl · ql) }
                    → ∀{redr : (ρ θ · p) sn⟶₁ (ρ θr · qr) }
                    → ∀{dec1l : p  ≐ El ⟦ il ⟧e}
                    → ∀{dec2l : ql ≐ El ⟦ iol ⟧e}
                    → ∀{dec1r : p  ≐ Er ⟦ ir ⟧e}
                    → ∀{dec2r : qr ≐ Er ⟦ ior ⟧e}
                    → ->E-view redl dec1l dec2l
                    → ->E-view redr dec1r dec2r
                    → (El ≡ Er × ql ≡ qr × θl ≡ θr) ⊎ (El a~ Er)

E-view-main-bind {epar₁ q ∷ El} {epar₂ p ∷ Er} v1 v2 = inj₂ par2
E-view-main-bind {epar₂ p ∷ El} {epar₁ q ∷ Er} v1 v2 = inj₂ par
E-view-main-bind {[]} {[]} {(present S ∣⇒ _ ∣⇒ _)}{θ = θ} {redl = (ris-present ∈1 eq1 dehole)} {(ris-absent ∈2 eq2 dehole)} {dehole} {dehole} {dehole} {dehole} vis-present vis-absent with sig-stats-∈-irr{S}{θ} ∈1 ∈2
... | k with trans (sym (trans k eq2)) eq1
... | ()
E-view-main-bind {[]} {[]} {(present S ∣⇒ _ ∣⇒ _)}{θ = θ} {redl = (ris-absent ∈1 eq1 dehole)} {(ris-present ∈2 eq2 dehole)} {dehole} {dehole} {dehole} {dehole} vis-absent vis-present with sig-stats-∈-irr{S}{θ} ∈1 ∈2
... | k with trans (sym (trans k eq2)) eq1
... | ()
E-view-main-bind {[]} {[]} {(if x ∣⇒ _ ∣⇒ _)}{θ = θ} {redl = (rif-false ∈1 eq1 dehole)} {(rif-true ∈2 eq2 dehole)} {dehole} {dehole} {dehole} {dehole} vif-false vif-true with var-vals-∈-irr{x}{θ} ∈1 ∈2
... | k with trans (sym (trans k eq2)) eq1
... | ()
E-view-main-bind {[]} {[]} {(if x ∣⇒ _ ∣⇒ _)}{θ = θ} {redl = (rif-true ∈1 eq1 dehole)} {(rif-false ∈2 eq2 dehole)} {dehole} {dehole} {dehole} {dehole} vif-true vif-false with var-vals-∈-irr{x}{θ} ∈1 ∈2
... | k with trans (sym (trans k eq2)) eq1
... | ()
E-view-main-bind {[]} {[]} {(s ⇐ _)}{θ = θ} {redl = (rset-shared-value-new _ ∈1 eq1 dehole)} {(rset-shared-value-old _ ∈2 eq2 dehole)} {dehole} {dehole} {dehole} {dehole} vset-shared-value-new vset-shared-value-old
  with shr-stats-∈-irr{s}{θ} ∈1 ∈2
... | k with trans (sym (trans k eq2)) eq1
... | ()
E-view-main-bind {[]} {[]} {(s ⇐ _)}{θ = θ} {redl = (rset-shared-value-old _ ∈1 eq1 dehole)} {(rset-shared-value-new _ ∈2 eq2 dehole)} {dehole} {dehole} {dehole} {dehole} vset-shared-value-old vset-shared-value-new   with shr-stats-∈-irr{s}{θ} ∈1 ∈2
... | k with trans (sym (trans k eq2)) eq1
... | ()

E-view-main-bind {[]} {[]} {.(ρ _ · _)} {redl = .(rmerge dehole)} {.(rmerge dehole)} {dehole} {dehole} {dehole} {dehole} vmerge vmerge = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {.(present _ ∣⇒ _ ∣⇒ _)} {redl = .(ris-present _ _ dehole)} {.(ris-present _ _ dehole)} {dehole} {dehole} {dehole} {dehole} vis-present vis-present = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {.(present _ ∣⇒ _ ∣⇒ _)} {redl = .(ris-absent _ _ dehole)} {.(ris-absent _ _ dehole)} {dehole} {dehole} {dehole} {dehole} vis-absent vis-absent = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {.(emit _)} {redl = .(remit _ _ dehole)} {.(remit _ _ dehole)} {dehole} {dehole} {dehole} {dehole} vemit vemit = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {.(shared _ ≔ _ in: _)} {redl = (rraise-shared e' dehole)} {(rraise-shared e'' dehole)} {dehole} {dehole} {dehole} {dehole} vraise-shared vraise-shared
  rewrite δ-e-irr e' e'' = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {.(_ ⇐ _)} {redl = (rset-shared-value-old e' _ _ dehole)} {(rset-shared-value-old e'' _ _ dehole)} {dehole} {dehole} {dehole} {dehole} vset-shared-value-old vset-shared-value-old
   rewrite δ-e-irr e' e'' = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {(s ⇐ _)}{θ = θ} {redl = (rset-shared-value-new e' s∈' _ dehole)} {(rset-shared-value-new e'' s∈'' _ dehole)} {dehole} {dehole} {dehole} {dehole} vset-shared-value-new vset-shared-value-new
   rewrite δ-e-irr e' e'' | (shr-vals-∈-irr{s}{θ} s∈' s∈'') = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {.(var _ ≔ _ in: _)} {redl = (rraise-var e' dehole)} {(rraise-var e'' dehole)} {dehole} {dehole} {dehole} {dehole} vraise-var vraise-var
   rewrite δ-e-irr e' e'' = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {(x ≔ e)} {redl = (rset-var{e = .e} _ e' dehole)} {(rset-var{e = .e} _ e'' dehole)} {dehole} {dehole} {dehole} {dehole} vset-var vset-var
   rewrite δ-e-irr e' e'' = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {.(if _ ∣⇒ _ ∣⇒ _)} {redl = .(rif-false _ _ dehole)} {.(rif-false _ _ dehole)} {dehole} {dehole} {dehole} {dehole} vif-false vif-false = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {[]} {.(if _ ∣⇒ _ ∣⇒ _)} {redl = .(rif-true _ _ dehole)} {.(rif-true _ _ dehole)} {dehole} {dehole} {dehole} {dehole} vif-true vif-true = inj₁ (refl , refl , refl)
E-view-main-bind {[]} {.(epar₁ _) ∷ Er} {.(_ ∥ _)} {redl = redl} {redr} {dehole} {dec2l} {depar₁ dec1r} {dec2r} () v2
E-view-main-bind {[]} {.(epar₂ _) ∷ Er} {.(_ ∥ _)} {redl = redl} {redr} {dehole} {dec2l} {depar₂ dec1r} {dec2r} () v2
E-view-main-bind {[]} {.(eseq _) ∷ Er} {.(_ >> _)} {redl = redl} {redr} {dehole} {dec2l} {deseq dec1r} {dec2r} () v2
E-view-main-bind {[]} {.(eloopˢ _) ∷ Er} {.(loopˢ _ _)} {redl = redl} {redr} {dehole} {dec2l} {deloopˢ dec1r} {dec2r} () v2
E-view-main-bind {[]} {.(esuspend _) ∷ Er} {.(suspend _ _)} {redl = redl} {redr} {dehole} {dec2l} {desuspend dec1r} {dec2r} () v2
E-view-main-bind {[]} {.etrap ∷ Er} {.(trap _)} {redl = redl} {redr} {dehole} {dec2l} {detrap dec1r} {dec2r} () v2
E-view-main-bind {.(epar₁ _) ∷ El} {[]} {.(_ ∥ _)} {redl = redl} {redr} {depar₁ dec1l} {dec2l} {dehole} {dec2r} v1 ()
E-view-main-bind {.(epar₂ _) ∷ El} {[]} {.(_ ∥ _)} {redl = redl} {redr} {depar₂ dec1l} {dec2l} {dehole} {dec2r} v1 ()
E-view-main-bind {.(eseq _) ∷ El} {[]} {.(_ >> _)} {redl = redl} {redr} {deseq dec1l} {dec2l} {dehole} {dec2r} v1 ()
E-view-main-bind {.(eloopˢ _) ∷ El} {[]} {.(loopˢ _ _)} {redl = redl} {redr} {deloopˢ dec1l} {dec2l} {dehole} {dec2r} v1 ()
E-view-main-bind {.(esuspend _) ∷ El} {[]} {.(suspend _ _)} {redl = redl} {redr} {desuspend dec1l} {dec2l} {dehole} {dec2r} v1 ()
E-view-main-bind {.etrap ∷ El} {[]} {.(trap _)} {redl = redl} {redr} {detrap dec1l} {dec2l} {dehole} {dec2r} v1 ()
E-view-main-bind {epar₁ q ∷ El} {epar₁ .q ∷ Er} {dec1l = depar₁ dec1l} {depar₁ dec2l} {depar₁ dec1r} {depar₁ dec2r} v1 v2 with unwrap-rho _ _ _ dec1l dec2l v1 | unwrap-rho _ _ _ dec1r dec2r v2
... | (redil , viewil) | (redir , viewir) with E-view-main-bind viewil viewir
... | (inj₁ (refl , refl , refl)) = inj₁ (refl , refl , refl)
... | (inj₂ y) = inj₂ (parr y)
E-view-main-bind {.(epar₂ _) ∷ El} {.(epar₂ _) ∷ Er} {.(_ ∥ _)} {dec1l = depar₂ dec1l} {depar₂ dec2l} {depar₂ dec1r} {depar₂ dec2r} v1 v2 with unwrap-rho _ _ _ dec1l dec2l v1 | unwrap-rho _ _ _ dec1r dec2r v2
... | (redil , viewil) | (redir , viewir) with E-view-main-bind viewil viewir
... | (inj₁ (refl , refl , refl)) = inj₁ (refl , refl , refl)
... | (inj₂ y) = inj₂ (parl y)
E-view-main-bind {.(eseq _) ∷ El} {.(eseq _) ∷ Er} {.(_ >> _)} {dec1l = deseq dec1l} {deseq dec2l} {deseq dec1r} {deseq dec2r} v1 v2  with unwrap-rho _ _ _ dec1l dec2l v1 | unwrap-rho _ _ _ dec1r dec2r v2
... | (redil , viewil) | (redir , viewir) with E-view-main-bind viewil viewir
... | (inj₁ (refl , refl , refl)) = inj₁ (refl , refl , refl)
... | (inj₂ y) = inj₂ (seq y)
E-view-main-bind {.(eloopˢ _) ∷ El} {.(eloopˢ _) ∷ Er} {.(loopˢ _ _)} {dec1l = deloopˢ dec1l} {deloopˢ dec2l} {deloopˢ dec1r} {deloopˢ dec2r} v1 v2  with unwrap-rho _ _ _ dec1l dec2l v1 | unwrap-rho _ _ _ dec1r dec2r v2
... | (redil , viewil) | (redir , viewir) with E-view-main-bind viewil viewir
... | (inj₁ (refl , refl , refl)) = inj₁ (refl , refl , refl)
... | (inj₂ y) = inj₂ (loopˢ y)
E-view-main-bind {.(esuspend _) ∷ El} {.(esuspend _) ∷ Er} {.(suspend _ _)} {dec1l = desuspend dec1l} {desuspend dec2l} {desuspend dec1r} {desuspend dec2r} v1 v2  with unwrap-rho _ _ _ dec1l dec2l v1 | unwrap-rho _ _ _ dec1r dec2r v2
... | (redil , viewil) | (redir , viewir) with E-view-main-bind viewil viewir
... | (inj₁ (refl , refl , refl)) = inj₁ (refl , refl , refl)
... | (inj₂ y) = inj₂ (susp y)
E-view-main-bind {.etrap ∷ El} {.etrap ∷ Er} {.(trap _)} {dec1l = detrap dec1l} {detrap dec2l} {detrap dec1r} {detrap dec2r} v1 v2  with unwrap-rho _ _ _ dec1l dec2l v1 | unwrap-rho _ _ _ dec1r dec2r v2
... | (redil , viewil) | (redir , viewir) with E-view-main-bind viewil viewir
... | (inj₁ (refl , refl , refl)) = inj₁ (refl , refl , refl)
... | (inj₂ y) = inj₂ (trp y)


get-view : ∀{θ θ' p q}
           → (red : (ρ θ · p) sn⟶₁ (ρ θ' · q))
           → (Σ[ E ∈ EvaluationContext ]
             Σ[ pin ∈ Term ]
             Σ[ qin ∈ Term ]
             Σ[ peq ∈ (p ≐ E ⟦ pin ⟧e) ]
             Σ[ qeq ∈ (q ≐ E ⟦ qin ⟧e) ]
             (->E-view{p}{q}{pin}{qin}{E}{θ}{θ'} red peq qeq ))
             ⊎ Σ[ eq ∈  (p ≡ q) ] (->pot-view red eq)

get-view (ris-present S∈ x x₁) = inj₁ (_ , _ , _ , x₁ , Erefl , vis-present)
get-view (ris-absent S∈ x x₁) = inj₁ (_ , _ , _ , x₁ , Erefl , vis-absent)
get-view (remit S∈ _ x) = inj₁ (_ , _ , _ , x , Erefl , vemit)
get-view (rraise-shared e' x) = inj₁ (_ , _ , _ , x , Erefl , vraise-shared)
get-view (rset-shared-value-old e' s∈ x x₁) = inj₁ (_ , _ , _ , x₁ , Erefl , vset-shared-value-old)
get-view (rset-shared-value-new e' s∈ x x₁) = inj₁ (_ , _ , _ , x₁ , Erefl , vset-shared-value-new)
get-view (rraise-var e' x₁) = inj₁ (_ , _ , _ , x₁ , Erefl , vraise-var)
get-view (rset-var x∈ e' x₁) = inj₁ (_ , _ , _ , x₁ , Erefl , vset-var)
get-view (rif-false x∈ x₁ x₂) = inj₁ (_ , _ , _ , x₂ , Erefl , vif-false)
get-view (rif-true x∈ x₁ x₂) = inj₁ (_ , _ , _ , x₂ , Erefl , vif-true)
get-view (rmerge x) = inj₁ (_ , _ , _ , x , Erefl , vmerge)
get-view (rabsence {S = S} S∈ x x₁) = inj₂ (refl , vabsence S S∈ x x₁)
get-view (rreadyness {s = s} s∈ x x₁) = inj₂ (refl , vreadyness s s∈ x x₁)
