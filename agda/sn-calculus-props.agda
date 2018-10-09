module _ where

open import Data.Nat using (ℕ ; _+_ ;  _≤′_ ; suc)
open import Induction.Nat using (<-rec)
open import Esterel.Lang.PotentialFunction
open import Function using (_∋_ ; _∘_ ; id ; _$_)
open import Data.Nat.Properties.Simple using ( +-comm ; +-assoc)
open import utility
open import noetherian using (noetherian ; ∥_∥s)
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Environment as Env
open import Esterel.Context
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; subst ; cong ; trans ; module ≡-Reasoning ; cong₂ ; subst₂ ; inspect) 
open import Data.Empty
open import sn-calculus
open import context-properties -- get view, E-views
open import Esterel.Lang.Binding
open import Data.Maybe using ( just )
-- open import coherence
open import Data.List.Any
open import Data.List.Any.Properties
open import Esterel.Lang.PotentialFunction.Base
open import eval
open import blocked
open import Data.List.All

open ≡-Reasoning using (_≡⟨_⟩_ ; _≡⟨⟩_ ; _∎)

open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Data.FiniteMap
import Data.OrderedListMap as OMap
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import sn-calculus-compatconf using (1-step)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open import binding-preserve

{- definition of two relations commuting
   (wrt to Correct Binding) -}
CB-COMMUTE : (Term -> Term -> Set) ->
             (Term -> Term -> Set) ->
             Set
CB-COMMUTE R1 R2 =
  ∀ {p q r BV FV} ->
  CorrectBinding p BV FV ->
  R1 p q ->
  R2 p r ->
  ∃ λ {z → (R2 q z × R1 r z)}

{- a relation that commutes with itself is confluent -}
CB-CONFLUENT : (Term -> Term -> Set) -> Set
CB-CONFLUENT R = CB-COMMUTE R R

sn⟶*-confluent : CB-CONFLUENT _sn⟶*_
sn⟶*-confluent {p} {q} {r} {BV} {FV} CB =
  newman ∥ p ∥s p q r BV FV refl CB where

  {-
    Proof of Newman's lemma from:
    _Confluent Reductions: Abstract Properties and Applications to Term
    Rewriting Systems_ by Gérard Huet. Oct 1980; JACM volume 27 issue 4
    https://dl.acm.org/citation.cfm?id=322230
   -}

  newmantype : ℕ -> Set
  newmantype c = ∀ p q r BV FV ->
    ∥ p ∥s ≡ c ->
    CorrectBinding p BV FV ->
    p sn⟶* q ->
    p sn⟶* r ->
    ∃ λ {z → (q sn⟶* z × r sn⟶* z)}

  step : ∀ (c : ℕ) ->
    ((c′ : ℕ) → suc c′ ≤′ c → newmantype c′)
    -> (newmantype c)
  step c rec x .x z BV FV nsx≡c CB rrefl s*xz = z , (s*xz , rrefl)
  step c rec x y .x BV FV nsx≡c CB s*xy rrefl = y , (rrefl , s*xy)
  step c rec x y z  BV FV refl  CB
    (rstep {.x} {y1} {.y} sxy1 s*y1y)
    (rstep {.x} {z1} {.z} sxz1 s*z1z)
    with 1-step {x} {y1} {z1} {BV} {FV} CB sxy1 sxz1
  ... | (u , s*y1u , s*z1u)        with sn⟶-maintains-binding CB sxy1
  ... | (BVy1 , FVy1) , (CBy1 , _) with sn⟶-maintains-binding CB sxz1
  ... | (BVz1 , FVz1) , (CBz1 , _) with rec ∥ y1 ∥s (noetherian{x}{y1} sxy1)
                                            y1 y u BVy1 FVy1 refl CBy1 s*y1y s*y1u
  ... | (v , s*yv , s*uv)          with rec ∥ z1 ∥s (noetherian{x}{z1} sxz1)
                                            z1 v z BVz1 FVz1 refl CBz1 (sn⟶*+ s*z1u s*uv) s*z1z
  ... | (t , s*vt , s*zt) = t , (sn⟶*+ s*yv s*vt) , s*zt

  newman : ∀ c -> newmantype c
  newman = <-rec _ step


lift-sn⟶* : ∀ {p q} → (P : Term → Set) → (∀ {p q} → P p → p sn⟶ q → P q) → P p → p sn⟶* q → P q
lift-sn⟶* P P-respects-sn⟶ Pp rrefl = Pp
lift-sn⟶* P P-respects-sn⟶ Pp (rstep psn⟶r rsn⟶*q) =
  lift-sn⟶* P P-respects-sn⟶ (P-respects-sn⟶ Pp psn⟶r) rsn⟶*q

sn≡ₑ-preserve-cb : ∀{p q BV FV} → CorrectBinding p BV FV → p sn≡ₑ q → ∃ λ {(BVq , FVq) → CorrectBinding q BVq FVq}
sn≡ₑ-preserve-cb cb (rstp x) with sn⟶-maintains-binding cb x
... | (bv,fv , cbq , _)= _ , cbq
sn≡ₑ-preserve-cb cb (rsym psn≡ₑq x) = _ , x
sn≡ₑ-preserve-cb cb rref = _ , cb
sn≡ₑ-preserve-cb cb (rtrn psn≡ₑq psn≡ₑq₁) = sn≡ₑ-preserve-cb (proj₂ (sn≡ₑ-preserve-cb cb psn≡ₑq)) psn≡ₑq₁

sn≡ₑ-consistent : ∀{p q BV FV} → CorrectBinding p BV FV → p sn≡ₑ q → Σ[ r ∈ Term ] p sn⟶* r ×  q sn⟶* r
sn≡ₑ-consistent cb (rstp x) = _ , rstep x rrefl , rrefl
sn≡ₑ-consistent cb (rsym qsn≡ₑp cbq) with sn≡ₑ-consistent cbq qsn≡ₑp
... | (r , qsn⟶r , psn⟶r ) = (r , psn⟶r , qsn⟶r)
sn≡ₑ-consistent cb rref = _ , rrefl , rrefl
sn≡ₑ-consistent cb (rtrn psn≡ₑs ssn≡ₑq) with (sn≡ₑ-preserve-cb cb psn≡ₑs)
... | (_ , cbs) with sn≡ₑ-consistent cb psn≡ₑs | sn≡ₑ-consistent cbs ssn≡ₑq
... | (rl , psn⟶*rl , ssn⟶*rl) | (rr , ssn⟶*rr , qsn⟶*rr) with sn⟶*-confluent cbs ssn⟶*rl ssn⟶*rr
... | (r , rlsn⟶*r , rrsn⟶*r) = r , (sn⟶*+ psn⟶*rl rlsn⟶*r , sn⟶*+ qsn⟶*rr rrsn⟶*r )

irreducibility-of-complete-sn⟶₁ : ∀{p q} → complete p → p sn⟶₁ q → ⊥
irreducibility-of-complete-sn⟶₁ (codone p/done) psn⟶₁q = done-¬sn⟶₁ p/done psn⟶₁q
irreducibility-of-complete-sn⟶₁ (coenv {θ} (θcomplete x x₁) p/done) ρθpsn⟶₁ρθ'q
  with ρ-stays-ρ-sn⟶₁ ρθpsn⟶₁ρθ'q
... | θ' , q , refl with get-view ρθpsn⟶₁ρθ'q
irreducibility-of-complete-sn⟶₁ (coenv {θ} (θcomplete x x₁) p/done) ρθpsn⟶₁ρθ'q
  | θ' , q , refl | inj₁ (E , pin , qin , p≐E⟦pin⟧ , q≐E⟦qin⟧ , e-view) =
  ⊥-elim
    (done-E-view-term-disjoint
      (done-⟦⟧e p/done p≐E⟦pin⟧)
      (->E-view-inner-term e-view))
irreducibility-of-complete-sn⟶₁ (coenv {θ} (θcomplete x x₁) p/done) ρθpsn⟶₁ρθ'q
  | θ' , q , refl | inj₂ (refl , vabsence S S∈ x₂ x₃)
   with x S S∈
... | inj₁ S≡ = lookup-S-eq θ S S∈ S∈ S≡ x₂ (λ ())
... | inj₂ S≡ = lookup-S-eq θ S S∈ S∈ S≡ x₂ (λ ())
irreducibility-of-complete-sn⟶₁ (coenv {θ} (θcomplete x x₁) p/done) ρθpsn⟶₁ρθ'q
  | θ' , q , refl | inj₂ (refl , vreadyness s s∈ x₂ x₃)
   with x₁ s s∈
... | s≡ with x₂
... | inj₁ s2≡ = lookup-s-eq θ s s∈ s∈ s≡ s2≡ (λ ())
... | inj₂ s2≡ = lookup-s-eq θ s s∈ s∈ s≡ s2≡ (λ ())


inescapability-of-paused-sn⟶ : ∀ {p q} ->
  paused p ->
  p sn⟶ q ->
  paused q
inescapability-of-paused-sn⟶ ppause (rcontext .[] dchole ())
inescapability-of-paused-sn⟶ (pseq ()) (rcontext .[] dchole rseq-done)
inescapability-of-paused-sn⟶ (pseq ()) (rcontext .[] dchole rseq-exit)
inescapability-of-paused-sn⟶ (pseq pausedp) (rcontext _ (dcseq₁ dc) psn⟶₁p')
  = pseq (inescapability-of-paused-sn⟶ pausedp (rcontext _ dc psn⟶₁p'))
inescapability-of-paused-sn⟶ (pseq pausedp) (rcontext _ (dcseq₂ dc) psn⟶₁p')
  = pseq pausedp
inescapability-of-paused-sn⟶ (ploopˢ ()) (rcontext .[] dchole rloopˢ-exit)
inescapability-of-paused-sn⟶ (ploopˢ pausedp) (rcontext _ (dcloopˢ₁ dc) psn⟶₁p')
  = ploopˢ (inescapability-of-paused-sn⟶ pausedp (rcontext _ dc psn⟶₁p'))
inescapability-of-paused-sn⟶ (ploopˢ pausedp) (rcontext _ (dcloopˢ₂ dc) psn⟶₁p')
  = ploopˢ pausedp
inescapability-of-paused-sn⟶ (ppar pausedp _) (rcontext .[] dchole (rpar-done-right p' q'))
  = ⊥-elim (halted-paused-disjoint p' pausedp)
inescapability-of-paused-sn⟶ (ppar _ pausedq) (rcontext .[] dchole (rpar-done-left p' q'))
  = ⊥-elim (halted-paused-disjoint q' pausedq)
inescapability-of-paused-sn⟶ (ppar pausedp pausedq) (rcontext _ (dcpar₁ dc) psn⟶₁p')
  = ppar (inescapability-of-paused-sn⟶ pausedp (rcontext _ dc psn⟶₁p')) pausedq
inescapability-of-paused-sn⟶ (ppar pausedp pausedq) (rcontext _ (dcpar₂ dc) psn⟶₁p')
  = ppar pausedp (inescapability-of-paused-sn⟶ pausedq (rcontext _ dc psn⟶₁p'))
inescapability-of-paused-sn⟶ (psuspend pausedp) (rcontext .[] dchole (rsuspend-done haltedp))
  = ⊥-elim (halted-paused-disjoint haltedp pausedp)
inescapability-of-paused-sn⟶ (psuspend pausedp) (rcontext _ (dcsuspend dc) psn⟶₁p')
  = psuspend (inescapability-of-paused-sn⟶ pausedp (rcontext _ dc psn⟶₁p'))
inescapability-of-paused-sn⟶ (ptrap ()) (rcontext .[] dchole (rtrap-done hnothin))
inescapability-of-paused-sn⟶ (ptrap ()) (rcontext .[] dchole (rtrap-done (hexit n)))
inescapability-of-paused-sn⟶ (ptrap pausedp) (rcontext _ (dctrap dc) psn⟶₁p')
  = ptrap (inescapability-of-paused-sn⟶ pausedp (rcontext _ dc psn⟶₁p'))

inescapability-of-paused-sn⟶* : ∀ {p q} ->
  paused p ->
  p sn⟶* q ->
  paused q
inescapability-of-paused-sn⟶* pausedp rrefl = pausedp
inescapability-of-paused-sn⟶* pausedp (rstep psn⟶r r⟶q)
  = inescapability-of-paused-sn⟶* (inescapability-of-paused-sn⟶ pausedp psn⟶r) r⟶q

inescapability-of-complete-sn⟶ : ∀{p q} → complete p → p sn⟶ q → complete q
inescapability-of-complete-sn⟶ c@(codone p-done) psn⟶q = codone (done-sn⟶ p-done psn⟶q)
inescapability-of-complete-sn⟶ c@(coenv x x₁) (rcontext .[] dchole psn⟶₁p') = ⊥-elim (irreducibility-of-complete-sn⟶₁ c psn⟶₁p')
inescapability-of-complete-sn⟶ (coenv x (dhalted hnothin)) (rcontext .(cenv _ ∷ []) (dcenv dchole) psn⟶₁p')
   = ⊥-elim (irreducibility-of-complete-sn⟶₁ (codone (dhalted hnothin)) psn⟶₁p')
inescapability-of-complete-sn⟶ (coenv x (dhalted (hexit n))) (rcontext .(cenv _ ∷ []) (dcenv dchole) psn⟶₁p')
   = ⊥-elim (irreducibility-of-complete-sn⟶₁ (codone (dhalted (hexit n))) psn⟶₁p')
inescapability-of-complete-sn⟶ (coenv x (dpaused p/paused)) (rcontext .(cenv _ ∷ _) (dcenv dc) psn⟶₁p')
 with (inescapability-of-complete-sn⟶ (codone (dpaused p/paused)) (rcontext _ dc psn⟶₁p'))
inescapability-of-complete-sn⟶ (coenv x (dpaused ppause)) (rcontext .(cenv _ ∷ _) (dcenv dchole) psn⟶₁p') | rec
   =  ⊥-elim (irreducibility-of-complete-sn⟶₁ (codone (dpaused ppause)) psn⟶₁p')

inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (ploopˢ p/paused))) (rcontext .(cenv _ ∷ []) (dcenv dchole) psn⟶₁p') | rec
   =  ⊥-elim (irreducibility-of-complete-sn⟶₁ (codone (dpaused (ploopˢ p/paused))) psn⟶₁p')
inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (ploopˢ p/paused))) (rcontext .(cenv _ ∷ ceval (eloopˢ _) ∷ _) (dcenv (dcloopˢ₁ dc)) psn⟶₁p') | codone x
  = coenv x₁ x
inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (ploopˢ p/paused))) (rcontext .(cenv _ ∷ cloopˢ₂ _ ∷ _) (dcenv (dcloopˢ₂ dc)) psn⟶₁p') | codone x
  = coenv x₁ x

inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (pseq p/paused))) (rcontext .(cenv _ ∷ []) (dcenv dchole) psn⟶₁p') | rec
   =  ⊥-elim (irreducibility-of-complete-sn⟶₁ (codone (dpaused (pseq p/paused))) psn⟶₁p')
inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (pseq p/paused))) (rcontext .(cenv _ ∷ ceval (eseq _) ∷ _) (dcenv (dcseq₁ dc)) psn⟶₁p') | codone x
  = coenv x₁ x
inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (pseq p/paused))) (rcontext .(cenv _ ∷ cseq₂ _ ∷ _) (dcenv (dcseq₂ dc)) psn⟶₁p') | codone x
  = coenv x₁ x

inescapability-of-complete-sn⟶ (coenv x (dpaused (ppar p/paused p/paused₁))) (rcontext .(cenv _ ∷ []) (dcenv dchole) psn⟶₁p') | rec
   =  ⊥-elim (irreducibility-of-complete-sn⟶₁ (codone (dpaused (ppar p/paused p/paused₁))) psn⟶₁p')
inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (ppar p/paused p/paused₁))) (rcontext .(cenv _ ∷ ceval (epar₁ _) ∷ _) (dcenv (dcpar₁ dc)) psn⟶₁p') | codone x
  = coenv x₁ x
inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (ppar p/paused p/paused₁))) (rcontext .(cenv _ ∷ ceval (epar₂ _) ∷ _) (dcenv (dcpar₂ dc)) psn⟶₁p') | codone x = coenv x₁ x
inescapability-of-complete-sn⟶ (coenv x (dpaused (psuspend p/paused))) (rcontext .(cenv _ ∷ []) (dcenv dchole) psn⟶₁p') | rec
   =  ⊥-elim (irreducibility-of-complete-sn⟶₁ (codone (dpaused (psuspend p/paused))) psn⟶₁p')
inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (psuspend p/paused))) (rcontext .(cenv _ ∷ ceval (esuspend _) ∷ _) (dcenv (dcsuspend dc)) psn⟶₁p') | codone x = coenv x₁ x
inescapability-of-complete-sn⟶ (coenv x (dpaused (ptrap p/paused))) (rcontext .(cenv _ ∷ []) (dcenv dchole) psn⟶₁p') | rec
   =  ⊥-elim (irreducibility-of-complete-sn⟶₁ (codone (dpaused (ptrap p/paused))) psn⟶₁p')
inescapability-of-complete-sn⟶ (coenv x₁ (dpaused (ptrap p/paused))) (rcontext .(cenv _ ∷ ceval etrap ∷ _) (dcenv (dctrap dc)) psn⟶₁p') | codone x = coenv x₁ x

inescapability-of-complete-sn : ∀{p q} → complete p → p sn⟶* q → complete q
inescapability-of-complete-sn = lift-sn⟶* complete inescapability-of-complete-sn⟶

equality-of-complete-sn⟶* : ∀{θ θ' p q} →
  complete (ρ θ ·  p) →
  (ρ θ · p) sn⟶* (ρ θ' · q) →
  θ ≡ θ'
equality-of-complete-sn⟶* ρθp/complete rrefl = refl
equality-of-complete-sn⟶* ρθp/complete (rstep (rcontext _ dchole ρθpsn⟶₁ρθ''r) ρθ''rsn⟶*ρθ'q)
  with irreducibility-of-complete-sn⟶₁ ρθp/complete ρθpsn⟶₁ρθ''r
... | ()
equality-of-complete-sn⟶* ρθp/complete (rstep (rcontext _ (dcenv ρθp≐C⟦p'⟧) p'sn⟶₁r) ρθrsn⟶*ρθ'q) =
  equality-of-complete-sn⟶*
    (inescapability-of-complete-sn⟶ ρθp/complete (rcontext _ (dcenv ρθp≐C⟦p'⟧) p'sn⟶₁r))
    ρθrsn⟶*ρθ'q

get-view/blocked : ∀{θ θ' p q} →
  blocked θ p →
  (ρθpsn⟶₁ρθ'q  :  ρ θ · p sn⟶₁ ρ θ' · q) →
  ∃ (->pot-view ρθpsn⟶₁ρθ'q)
get-view/blocked p/blocked ρθpsn⟶₁ρθ'q with get-view ρθpsn⟶₁ρθ'q
... | inj₂ refl-pot-view = refl-pot-view
... | inj₁ (E , pin , qin , p≐E⟦pin⟧ , q≐E⟦qin⟧ , e-view)
  with blocked-⟦⟧e p/blocked p≐E⟦pin⟧ | ->E-view-inner-term e-view
... | inj₂ pin/done | e-view-term =
  ⊥-elim
    (done-E-view-term-disjoint
      pin/done
      (->E-view-inner-term e-view))
... | (inj₁ (bpar-both pin'/blocked qin'/blocked)) | ()
... | (inj₁ (bpar-left pin'/blocked qin'/done))    | ()
... | (inj₁ (bpar-right pin'/done qin'/blocked))   | ()
... | (inj₁ (bloopˢ pin/blocked))                  | ()
... | (inj₁ (bseq pin/blocked))                    | ()
... | (inj₁ (bsusp pin/blocked))                   | ()
... | (inj₁ (btrap pin/blocked))                   | ()
get-view/blocked {θ} p/blocked (ris-present S∈' θS≡present .p≐E⟦pin⟧)
  | inj₁ (E , pin , qin , p≐E⟦pin⟧ , q≐E⟦qin⟧ , vis-present)
  | (inj₁ (bsig-exists S S∈ θS≡unknown)) | evt-present
  with trans (sym θS≡present) (trans (Env.sig-stats-∈-irr {S} {θ} S∈' S∈) θS≡unknown)
... | ()
get-view/blocked {θ} p/blocked (ris-absent S∈' θS≡absent .p≐E⟦pin⟧)
  | inj₁ (E ,  pin , qin , p≐E⟦pin⟧ , q≐E⟦qin⟧ , vis-absent)
  | (inj₁ (bsig-exists S S∈ θS≡unknown)) | evt-present
  with trans (sym θS≡absent) (trans (Env.sig-stats-∈-irr {S} {θ} S∈' S∈) θS≡unknown)
... | ()
get-view/blocked p/blocked (rraise-shared {s = s} e' .p≐E⟦pin⟧)
  | inj₁ (E , pin , qin , p≐E⟦pin⟧ , q≐E⟦qin⟧ , vraise-shared)
  | (inj₁ (bshared e/blocked)) | evt-raise-shared =
  ⊥-elim (all-ready-blocked-disjoint (e' , e/blocked))
get-view/blocked p/blocked (rset-shared-value-old {s = s} e' s∈ θs≡old .p≐E⟦pin⟧)
  | inj₁ (E , pin , qin , p≐E⟦pin⟧ , q≐E⟦qin⟧ , vset-shared-value-old)
  | (inj₁ (bsset e/blocked)) | evt-set-shared =
  ⊥-elim (all-ready-blocked-disjoint (e' , e/blocked))
get-view/blocked p/blocked (rset-shared-value-new {s = s} e' s∈ θs≡new .p≐E⟦pin⟧)
  | inj₁ (E , pin , qin , p≐E⟦pin⟧ , q≐E⟦qin⟧ , vset-shared-value-new)
  | (inj₁ (bsset e/blocked)) | evt-set-shared =
  ⊥-elim (all-ready-blocked-disjoint (e' , e/blocked))
get-view/blocked p/blocked (rraise-var {x = x} e' .p≐E⟦pin⟧)
  | inj₁ (E , pin , qin , p≐E⟦pin⟧ , q≐E⟦qin⟧ , vraise-var)
  | (inj₁ (bvar e/blocked)) | evt-raise-var =
  ⊥-elim (all-ready-blocked-disjoint (e' , e/blocked))
get-view/blocked p/blocked (rset-var {x = x} x∈ e' .p≐E⟦pin⟧)
  | inj₁ (E , pin , qin , p≐E⟦pin⟧ , q≐E⟦qin⟧ , vset-var)
  | (inj₁ (bxset e/blocked)) | evt-set-var =
  ⊥-elim (all-ready-blocked-disjoint (e' , e/blocked))

irreducibility-of-blocked-sn⟶₁ : ∀ {θ p q} → blocked θ p → p sn⟶₁ q → ⊥
irreducibility-of-blocked-sn⟶₁ (bsig-exists S S∈ θS≡unknown) ()
irreducibility-of-blocked-sn⟶₁ (bshared e/blocked)           ()
irreducibility-of-blocked-sn⟶₁ (bsset e/blocked)             ()
irreducibility-of-blocked-sn⟶₁ (bvar e/blocked)              ()
irreducibility-of-blocked-sn⟶₁ (bxset e/blocked)             ()
irreducibility-of-blocked-sn⟶₁ (bpar-both p/blocked q/blocked)
  (rpar-done-right p/halted q/done)   =
  halted-blocked-disjoint p/halted p/blocked
irreducibility-of-blocked-sn⟶₁ (bpar-left p/blocked q/done)
  (rpar-done-right p/halted q/done')  =
  halted-blocked-disjoint p/halted p/blocked
irreducibility-of-blocked-sn⟶₁ (bpar-right p/done q/blocked)
  (rpar-done-right p/halted q/done)   =
  done-blocked-disjoint q/done q/blocked
irreducibility-of-blocked-sn⟶₁ (bpar-both p/blocked q/blocked)
  (rpar-done-left  p/done   q/halted) =
  halted-blocked-disjoint q/halted q/blocked
irreducibility-of-blocked-sn⟶₁ (bpar-left p/blocked q/done)
  (rpar-done-left  p/done   q/halted) =
  done-blocked-disjoint p/done p/blocked
irreducibility-of-blocked-sn⟶₁ (bpar-right p/done q/blocked)
  (rpar-done-left  p/done'  q/halted) =
  halted-blocked-disjoint q/halted q/blocked
irreducibility-of-blocked-sn⟶₁ (bseq ())
  rseq-done
irreducibility-of-blocked-sn⟶₁ (bseq ())
  rseq-exit
irreducibility-of-blocked-sn⟶₁ (bloopˢ ())
  rloopˢ-exit
irreducibility-of-blocked-sn⟶₁ (bsusp p/blocked)
  (rsuspend-done p/halted) =
  halted-blocked-disjoint p/halted p/blocked
irreducibility-of-blocked-sn⟶₁ (btrap p/blocked)
  (rtrap-done p/halted) =
  halted-blocked-disjoint p/halted p/blocked


irreducibility-of-halted-sn⟶ : ∀ {p q} ->
  halted p ->
  p sn⟶ q ->
  ⊥
irreducibility-of-halted-sn⟶ hnothin (rcontext [] dchole ())
irreducibility-of-halted-sn⟶ (hexit n) (rcontext [] dchole ())

-- not sure if it's worthwhile for now to also prove this for ρ θ · p sn⟶₁ ρ θ' · p
inescapability-of-blocked-inside-sn⟶ : ∀{θ p q} →
  blocked θ p →
  p sn⟶ q →
  blocked θ q
inescapability-of-blocked-inside-sn⟶ p/blocked (rcontext _ dchole psn⟶₁p') =
  ⊥-elim (irreducibility-of-blocked-sn⟶₁ p/blocked psn⟶₁p')
inescapability-of-blocked-inside-sn⟶ (bpar-both p/blocked q/blocked)
  (rcontext _ (dcpar₁ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bpar-both
    (inescapability-of-blocked-inside-sn⟶ p/blocked
     (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))
    q/blocked
inescapability-of-blocked-inside-sn⟶ (bpar-both p/blocked q/blocked)
  (rcontext _ (dcpar₂ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bpar-both p/blocked
    (inescapability-of-blocked-inside-sn⟶ q/blocked
     (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))
inescapability-of-blocked-inside-sn⟶ (bpar-left p/blocked q/done)
  (rcontext _ (dcpar₁ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bpar-left
    (inescapability-of-blocked-inside-sn⟶ p/blocked
     (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))
    q/done
inescapability-of-blocked-inside-sn⟶ (bpar-left p/blocked q/done)
  (rcontext _ (dcpar₂ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bpar-left p/blocked
    (done-sn⟶ q/done (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))
inescapability-of-blocked-inside-sn⟶ (bpar-right p/done q/blocked)
  (rcontext _ (dcpar₁ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bpar-right (done-sn⟶ p/done (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))
    q/blocked
inescapability-of-blocked-inside-sn⟶ (bpar-right p/done q/blocked)
  (rcontext _ (dcpar₂ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bpar-right p/done
    (inescapability-of-blocked-inside-sn⟶ q/blocked
     (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))

inescapability-of-blocked-inside-sn⟶ (bseq p/blocked)
  (rcontext _ (dcseq₁ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bseq
    (inescapability-of-blocked-inside-sn⟶ p/blocked
     (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))
inescapability-of-blocked-inside-sn⟶ (bseq p/blocked)
  (rcontext _ (dcseq₂ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bseq p/blocked

inescapability-of-blocked-inside-sn⟶ (bloopˢ p/blocked)
  (rcontext _ (dcloopˢ₁ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bloopˢ
    (inescapability-of-blocked-inside-sn⟶ p/blocked
     (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))
inescapability-of-blocked-inside-sn⟶ (bloopˢ p/blocked)
  (rcontext _ (dcloopˢ₂ p≐C⟦pin⟧) pinsn⟶₁pin') =
  bloopˢ p/blocked

inescapability-of-blocked-inside-sn⟶ (bsusp p/blocked)
  (rcontext _ (dcsuspend p≐C⟦pin⟧) pinsn⟶₁pin') =
  bsusp
    (inescapability-of-blocked-inside-sn⟶ p/blocked
     (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))
inescapability-of-blocked-inside-sn⟶ (btrap p/blocked)
  (rcontext _ (dctrap p≐C⟦pin⟧) pinsn⟶₁pin') =
  btrap
    (inescapability-of-blocked-inside-sn⟶ p/blocked
     (rcontext _ p≐C⟦pin⟧ pinsn⟶₁pin'))
inescapability-of-blocked-inside-sn⟶ (bshared e/blocked)
  (rcontext _ (dcshared p≐C⟦pin⟧) pinsn⟶₁pin') =
  bshared e/blocked
inescapability-of-blocked-inside-sn⟶ (bvar e/blocked)
  (rcontext _ (dcvar p≐C⟦pin⟧) pinsn⟶₁pin') =
  bvar e/blocked
inescapability-of-blocked-inside-sn⟶ {θ} (bsig-exists S S∈ θS≡unknown)
  (rcontext _ S?p:q≐C⟦pin⟧ pinsn⟶₁pin') with S?p:q≐C⟦pin⟧
-- we still have the dchole case here since Agda can't determine that it cannot happen
... | dchole = ⊥-elim (irreducibility-of-blocked-sn⟶₁ (bsig-exists {θ} S S∈ θS≡unknown) pinsn⟶₁pin')
... | dcpresent₁ p≐C⟦pin⟧ = bsig-exists S S∈ θS≡unknown
... | dcpresent₂ p≐C⟦pin⟧ = bsig-exists S S∈ θS≡unknown

