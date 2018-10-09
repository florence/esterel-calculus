module par-swap.union-properties where

open import par-swap
open import par-swap.union-confluent
open import par-swap.confluent
open import sn-calculus
open import sn-calculus-props
open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
open import Esterel.Context
open import Esterel.Context.Properties
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; sig ; []env ;
         module SigMap ; module ShrMap ; module VarMap)
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; sym)

open import binding-preserve

∥R∪sn≡ₑ-preserve-cb : ∀ {p BVp FVp q} ->
  CorrectBinding p BVp FVp ->
  p ∥R∪sn≡ₑ q ->
  ∃ \ { (BVq , FVq) -> CorrectBinding q BVq FVq }
∥R∪sn≡ₑ-preserve-cb CBp (∪stpsn psn⟶q)
  with sn⟶-maintains-binding CBp psn⟶q
... | _ , CBq , _ = _ , CBq
∥R∪sn≡ₑ-preserve-cb CBp (∪stp∥ p∥Rq)
  with ∥R-maintains-binding CBp p∥Rq
... | CBq = _ , CBq
∥R∪sn≡ₑ-preserve-cb CBp (∪sym p∪≡ₑq CBq) = _ , CBq
∥R∪sn≡ₑ-preserve-cb CBp ∪ref = _ , CBp
∥R∪sn≡ₑ-preserve-cb CBp (∪trn p∪≡ₑr r∪≡ₑq)
  with ∥R∪sn≡ₑ-preserve-cb CBp p∪≡ₑr
... | _ , CBr = ∥R∪sn≡ₑ-preserve-cb CBr r∪≡ₑq

∥R∪sn≡ₑ-consistent : ∀{p q BV FV} →
  CorrectBinding p BV FV →
  p ∥R∪sn≡ₑ q →
  Σ[ r ∈ Term ] (p ∥R*∪sn⟶* r) × (q ∥R*∪sn⟶* r)
∥R∪sn≡ₑ-consistent CBp (∪stpsn psn⟶q)
  = _ ,  ∪sn⟶* (rstep psn⟶q rrefl) ∪refl  , ∪refl
∥R∪sn≡ₑ-consistent CBp (∪stp∥ ps∥Rq)
  = _ , ∪∥R* (∥Rn ps∥Rq ∥R0) ∪refl , ∪refl
∥R∪sn≡ₑ-consistent CBp (∪sym psn∪∥R≡ₑq CBq)
  with ∥R∪sn≡ₑ-consistent CBq psn∪∥R≡ₑq
... | _ , a , b
  = _ , b , a
∥R∪sn≡ₑ-consistent CBp ∪ref = _ , ∪refl , ∪refl
∥R∪sn≡ₑ-consistent{p}{q} CBp (∪trn{.p}{r}{.q} p≡r r≡q)
  with ∥R∪sn≡ₑ-preserve-cb CBp p≡r
... | ((BVr , FVr) , CBr)
  with ∥R∪sn≡ₑ-preserve-cb CBr r≡q
... | ((BVq , FVq) , CBq)
  with ∥R∪sn≡ₑ-consistent CBp p≡r
... | (y , p⟶y , r⟶y)
  with ∥R∪sn≡ₑ-consistent CBr r≡q
... | (z , r⟶z , q⟶z)
  with ∥R*∪sn⟶*-confluent CBr r⟶y r⟶z
... | (x , y⟶x , z⟶x)
  = x , ∥R*∪sn⟶*-concat p⟶y y⟶x , ∥R*∪sn⟶*-concat q⟶z z⟶x

inescapability-of-complete-∥R : ∀ {p q} ->
  complete p ->
  p ∥R q ->
  complete q
inescapability-of-complete-∥R
 = \ { completep (∥Rstep dc) -> thm completep dc } where

  thm-p : ∀ {p C p₁ p₂} ->
    paused p ->
    p ≐ C ⟦ p₁ ∥ p₂ ⟧c ->
    paused (C ⟦ p₂ ∥ p₁ ⟧c)
  thm-p ppause ()
  thm-p (pseq paused₁) (dcseq₁ pC) = pseq (thm-p paused₁ pC)
  thm-p (pseq paused₁) (dcseq₂ pC) = pseq paused₁
  thm-p (ploopˢ paused₁) (dcloopˢ₁ pC) = ploopˢ (thm-p paused₁ pC)
  thm-p (ploopˢ paused₁) (dcloopˢ₂ pC) = ploopˢ paused₁
  thm-p (ppar paused₁ paused₂) dchole = ppar paused₂ paused₁
  thm-p (ppar paused₁ paused₂) (dcpar₁ pC) = ppar (thm-p paused₁ pC) paused₂
  thm-p (ppar paused₁ paused₂) (dcpar₂ pC) = ppar paused₁ (thm-p paused₂ pC)
  thm-p (psuspend paused₁) (dcsuspend pC) = psuspend (thm-p paused₁ pC)
  thm-p (ptrap paused₁) (dctrap pC) = ptrap (thm-p paused₁ pC)

  thm-d : ∀ {p C p₁ p₂} ->
    done p ->
    p ≐ C ⟦ p₁ ∥ p₂ ⟧c ->
    done (C ⟦ p₂ ∥ p₁ ⟧c)
  thm-d (dhalted hnothin) ()
  thm-d (dhalted (hexit n)) ()
  thm-d (dpaused p/paused) pC
    = dpaused (thm-p p/paused pC)

  thm : ∀ {p C p₁ p₂} ->
    complete p ->
    p ≐ C ⟦ p₁ ∥ p₂ ⟧c ->
    complete (C ⟦ p₂ ∥ p₁ ⟧c)
  thm (codone x) pC = codone (thm-d x pC)
  thm (coenv x x₁) (dcenv pC) = coenv x (thm-d x₁ pC)

inescapability-of-complete-∥R* : ∀ {p q} ->
  complete p ->
  p ∥R* q ->
  complete q
inescapability-of-complete-∥R* = thm where
  thm : ∀ {p q} ->
    complete p ->
    p ∥R* q ->
    complete q
  thm completep ∥R0 = completep
  thm completep (∥Rn p∥Rr r⟶q)
    = thm (inescapability-of-complete-∥R completep p∥Rr) r⟶q

inescapability-of-complete-∪ : ∀ {p q} ->
  complete p ->
  p ∥R*∪sn⟶* q ->
  complete q
inescapability-of-complete-∪ = thm where
  thm : ∀ {p q} ->
   complete p ->
   p ∥R*∪sn⟶* q ->
   complete q
  thm completep (∪∥R* p∥R*r r⟶q)
   = thm (inescapability-of-complete-∥R* completep p∥R*r) r⟶q
  thm completep (∪sn⟶* psn⟶*r r⟶q)
   = thm (inescapability-of-complete-sn completep psn⟶*r) r⟶q
  thm completep ∪refl = completep

ρ-stays-ρ-∪ : ∀{θ p q} →
  (ρ θ · p) ∥R*∪sn⟶* q →
  Σ[ θ' ∈ Env.Env ] Σ[ qin ∈ Term ] q ≡ (ρ θ' · qin)
ρ-stays-ρ-∪ = thm where

  thm∥R : ∀{θ p q} →
   (ρ θ · p) ∥R q →
   Σ[ θ' ∈ Env.Env ] Σ[ qin ∈ Term ] q ≡ (ρ θ' · qin)
  thm∥R (∥Rstep (dcenv d≐C⟦p∥q⟧c))
   rewrite sym (unplugc d≐C⟦p∥q⟧c)
   = _ , _ , refl

  thm∥R* : ∀{θ p q} →
   (ρ θ · p) ∥R* q →
   Σ[ θ' ∈ Env.Env ] Σ[ qin ∈ Term ] q ≡ (ρ θ' · qin)
  thm∥R* ∥R0 = _ , _ , refl
  thm∥R* (∥Rn p∥Rq p⟶q)
    with thm∥R p∥Rq
  ... | (θ' , qin , refl) = thm∥R* p⟶q

  thm : ∀{θ p q} →
   (ρ θ · p) ∥R*∪sn⟶* q →
   Σ[ θ' ∈ Env.Env ] Σ[ qin ∈ Term ] q ≡ (ρ θ' · qin)
  thm (∪∥R* p∥R*q p⟶q)
    with thm∥R* p∥R*q
  ... | (θ' , qin , refl) = thm p⟶q
  thm (∪sn⟶* psn⟶*q p⟶q)
    with ρ-stays-ρ-sn⟶* psn⟶*q
  ... | (θ' , qin , refl) = thm p⟶q
  thm ∪refl = _ , _ , refl

irreducibility-of-halted-∥R : ∀ {p q} ->
  halted p ->
  p ∥R q ->
  ⊥
irreducibility-of-halted-∥R hnothin (∥Rstep ())
irreducibility-of-halted-∥R (hexit n) (∥Rstep ())

inescapability-of-paused-∥R : ∀ {p q} ->
  paused p ->
  p ∥R q ->
  paused q
inescapability-of-paused-∥R ppause (∥Rstep ())
inescapability-of-paused-∥R (pseq pausedp) (∥Rstep (dcseq₁ dc))
 = pseq (inescapability-of-paused-∥R pausedp (∥Rstep dc))
inescapability-of-paused-∥R (pseq pausedp) (∥Rstep (dcseq₂ dc))
 = pseq pausedp
inescapability-of-paused-∥R (ploopˢ pausedp) (∥Rstep (dcloopˢ₁ dc))
  = ploopˢ (inescapability-of-paused-∥R pausedp (∥Rstep dc))
inescapability-of-paused-∥R (ploopˢ pausedp) (∥Rstep (dcloopˢ₂ dc))
  = ploopˢ pausedp
inescapability-of-paused-∥R (ppar pausedp pausedq) (∥Rstep dchole)
  = ppar pausedq pausedp
inescapability-of-paused-∥R (ppar pausedp pausedq) (∥Rstep (dcpar₁ dc))
  = ppar (inescapability-of-paused-∥R pausedp (∥Rstep dc)) pausedq
inescapability-of-paused-∥R (ppar pausedp pausedq) (∥Rstep (dcpar₂ dc))
  = ppar pausedp (inescapability-of-paused-∥R pausedq (∥Rstep dc))
inescapability-of-paused-∥R (psuspend pausedp) (∥Rstep (dcsuspend dc))
  = psuspend (inescapability-of-paused-∥R pausedp (∥Rstep dc))
inescapability-of-paused-∥R (ptrap pausedp) (∥Rstep (dctrap dc))
  = ptrap (inescapability-of-paused-∥R pausedp (∥Rstep dc))

inescapability-of-paused-∥R* : ∀ {p q} ->
  paused p ->
  p ∥R* q ->
  paused q
inescapability-of-paused-∥R* pausedp ∥R0 = pausedp
inescapability-of-paused-∥R* pausedp (∥Rn p∥Rq p⟶q)
 = inescapability-of-paused-∥R* (inescapability-of-paused-∥R pausedp p∥Rq) p⟶q

equality-of-complete-∪ : ∀{θ θ' p q} →
  complete (ρ θ ·  p) →
  (ρ θ · p) ∥R*∪sn⟶* (ρ θ' · q) →
  θ ≡ θ'
equality-of-complete-∪ = thm where

 done-not-to-ρ-∪ : ∀ {p θ q} ->
    done p ->
    p ∥R*∪sn⟶* (ρ θ · q) ->
    ⊥
 done-not-to-ρ-∪ (dhalted p/halted) (∪∥R* ∥R0 p⟶q)
   = done-not-to-ρ-∪ (dhalted p/halted) p⟶q
 done-not-to-ρ-∪ (dhalted p/halted) (∪∥R* (∥Rn p∥Rq p∥R*q) p⟶q)
   = irreducibility-of-halted-∥R p/halted p∥Rq
 done-not-to-ρ-∪ (dpaused p/paused) (∪∥R* p∥R*q p⟶q)
   = done-not-to-ρ-∪ (dpaused (inescapability-of-paused-∥R* p/paused p∥R*q)) p⟶q
 done-not-to-ρ-∪ (dhalted p/halted) (∪sn⟶* rrefl r⟶q)
  = done-not-to-ρ-∪ (dhalted p/halted) r⟶q
 done-not-to-ρ-∪ (dhalted p/halted) (∪sn⟶* (rstep psn⟶q p⟶r) r⟶q)
  = irreducibility-of-halted-sn⟶ p/halted psn⟶q
 done-not-to-ρ-∪ (dpaused p/paused) (∪sn⟶* p⟶r r⟶q)
  = done-not-to-ρ-∪ (dpaused (inescapability-of-paused-sn⟶* p/paused p⟶r)) r⟶q
 done-not-to-ρ-∪ (dhalted ()) ∪refl
 done-not-to-ρ-∪ (dpaused ()) ∪refl

 ∥R*-lemma : ∀ {θ p q} ->
   done p ->
   (ρ θ ·  p) ∥R* q ->
   Σ[ q' ∈ Term ] q ≡ (ρ θ ·  q') × done q'
 ∥R*-lemma done₁ ∥R0 = _ , refl , done₁
 ∥R*-lemma (dhalted hnothin) (∥Rn (∥Rstep (dcenv ())) p⟶q)
 ∥R*-lemma (dhalted (hexit n)) (∥Rn (∥Rstep (dcenv ())) p⟶q)
 ∥R*-lemma (dpaused p/paused) (∥Rn (∥Rstep (dcenv d≐C⟦p∥q⟧c)) p⟶q)
   with inescapability-of-paused-∥R p/paused (∥Rstep d≐C⟦p∥q⟧c)
 ... | q/paused = ∥R*-lemma (dpaused q/paused) p⟶q

 thm : ∀{θ θ' p q} →
  complete (ρ θ ·  p) →
  (ρ θ · p) ∥R*∪sn⟶* (ρ θ' · q) →
  θ ≡ θ'
 thm (codone x) p⟶q = ⊥-elim (done-not-to-ρ-∪ x p⟶q)
 thm (coenv complete-θθ donep) (∪∥R* p∥R*q p⟶q)
   with ∥R*-lemma donep p∥R*q
 ... | _ , refl , doneq' = thm (coenv complete-θθ doneq') p⟶q
 thm (coenv complete-θθ donep) (∪sn⟶* psn⟶*r r⟶q)
   with inescapability-of-complete-sn (coenv complete-θθ donep) psn⟶*r
 thm (coenv complete-θθ donep) (∪sn⟶* psn⟶*r r⟶q) | codone x
   = ⊥-elim (done-not-to-ρ-∪ x r⟶q)
 thm (coenv complete-θθ donep) (∪sn⟶* psn⟶*r r⟶q) | coenv x x₁
   with equality-of-complete-sn⟶* (coenv complete-θθ donep) psn⟶*r
 ... | refl = thm (coenv x x₁) r⟶q
 thm (coenv complete-θθ donep) ∪refl = refl
