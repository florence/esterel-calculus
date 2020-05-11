module par-swap.dpg where

open import par-swap
open import par-swap.properties
open import par-swap.confluent
open import par-swap.dpg-pot
open import par-swap.dpg-e-view
open import noetherian using (noetherian ; ∥_∥s)
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.Binding
open import Esterel.Environment as Env
open import Esterel.Context
open import Data.Product
open import Data.Bool
open import Data.Empty
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Data.Sum
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; subst ; cong ; trans ;
         module ≡-Reasoning ; cong₂ ; subst₂ ; inspect)
open import sn-calculus
open import context-properties -- get view, E-views

DPG₁ : ∀ {p q r} ->
   (p ∥ q) sn⟶₁ r ->
   ∃ \ {(d , d₁) -> (q ∥ p) sn⟶ d₁ × d₁ sn⟶* d × r ∥R* d}
DPG₁{p} {q} {r} (rpar-done-right haltedp doneq) =
    (r , r) ,
    fixup-valuemax₁ doneq haltedp (rcontext [] dchole (rpar-done-left doneq haltedp)) ,
    rrefl , ∥R0 where
 fixup-valuemax₁ : ∀ {p q}  ->
   (doneq : done q) ->
   (haltedp : halted p) ->
   q ∥ p sn⟶ value-max doneq (dhalted haltedp) (inj₂ haltedp) ->
   q ∥ p sn⟶ value-max (dhalted haltedp) doneq (inj₁ haltedp)
 fixup-valuemax₁ donep haltedq rewrite value-max-sym donep haltedq = λ z → z

DPG₁{p}{q}{r} (rpar-done-left donep haltedq) =
    (r , r) ,
    fixup-valuemax₂ donep haltedq (rcontext [] dchole (rpar-done-right haltedq donep)) ,
    rrefl , ∥R0 where
 fixup-valuemax₂ : ∀ {p q} ->
  (donep : done p) ->
  (haltedq : halted q) ->
  q ∥ p sn⟶ value-max (dhalted haltedq) donep (inj₁ haltedq) ->
  q ∥ p sn⟶ value-max donep (dhalted haltedq) (inj₂ haltedq)
 fixup-valuemax₂ donep haltedq rewrite sym (value-max-sym donep haltedq) = λ z → z

par-not-halted : ∀ {p C q₁ q₂} -> halted p -> p ≐ C ⟦ q₁ ∥ q₂ ⟧c -> ⊥
par-not-halted hnothin ()
par-not-halted (hexit n) ()

swap-paused-is-paused :
  ∀ {p C q₁ q₂} ->
    paused p ->
    p ≐ C ⟦ q₁ ∥ q₂ ⟧c ->
    paused (C ⟦ q₂ ∥ q₁ ⟧c)
swap-paused-is-paused ppause ()
swap-paused-is-paused (pseq pausedp) (dcseq₁ dc)
 = pseq (swap-paused-is-paused pausedp dc)
swap-paused-is-paused (pseq pausedp) (dcseq₂ dc)
 = pseq pausedp
swap-paused-is-paused (ploopˢ pausedp) (dcloopˢ₁ dc)
 = ploopˢ (swap-paused-is-paused pausedp dc)
swap-paused-is-paused (ploopˢ pausedp) (dcloopˢ₂ dc)
 = ploopˢ pausedp
swap-paused-is-paused (ppar pausedp pausedp₁) dchole
 = ppar pausedp₁ pausedp
swap-paused-is-paused (ppar pausedp pausedp₁) (dcpar₁ dc)
 = ppar (swap-paused-is-paused pausedp dc) pausedp₁
swap-paused-is-paused (ppar pausedp pausedp₁) (dcpar₂ dc)
 = ppar pausedp (swap-paused-is-paused pausedp₁ dc)
swap-paused-is-paused (psuspend pausedp) (dcsuspend dc)
 = psuspend (swap-paused-is-paused pausedp dc)
swap-paused-is-paused (ptrap pausedp) (dctrap dc)
 = ptrap (swap-paused-is-paused pausedp dc)

DPG : ∀ {a b c} ->
      a ∥R b ->
      a sn⟶ c ->
      Σ (Term × Term) λ {(d , d₁) -> b sn⟶ d₁ × d₁ sn⟶* d × c ∥R* d}

DPG (∥Rstep dchole) (rcontext _ dchole psn⟶₁p')
  = DPG₁ psn⟶₁p'

DPG (∥Rstep dchole) (rcontext _ (dcpar₁ dcsn⟶) psn⟶₁p')
  =  _ ,  rcontext _ (dcpar₂ dcsn⟶) psn⟶₁p'  , rrefl , ∥Rn (∥Rstep dchole) ∥R0

DPG (∥Rstep dchole) (rcontext _ (dcpar₂ dcsn⟶) psn⟶₁p')
  = _ ,  rcontext _ (dcpar₁ dcsn⟶) psn⟶₁p'  , rrefl , ∥Rn (∥Rstep dchole) ∥R0

DPG (∥Rstep (dcpar₁ dc∥R)) (rcontext .[] dchole (rpar-done-right haltedp doneq))
 = ⊥-elim (par-not-halted haltedp dc∥R)

DPG (∥Rstep (dcpar₁ dc∥R)) (rcontext .[] dchole (rpar-done-left (dhalted p/halted) haltedq))
  = ⊥-elim (par-not-halted p/halted dc∥R)

DPG (∥Rstep (dcpar₁ dc∥R)) (rcontext .[] dchole (rpar-done-left (dpaused p/paused) hnothin))
  = _ ,
    rcontext [] dchole (rpar-done-left (dpaused (swap-paused-is-paused p/paused dc∥R)) hnothin) ,
    rrefl ,
    ∥Rn (∥Rstep dc∥R) ∥R0

DPG (∥Rstep (dcpar₁ dc∥R)) (rcontext .[] dchole (rpar-done-left (dpaused p/paused) (hexit n)))
  = _ ,
    rcontext [] dchole (rpar-done-left (dpaused (swap-paused-is-paused p/paused dc∥R)) (hexit n)) ,
    rrefl ,
    ∥R0

DPG (∥Rstep (dcpar₁ dc∥R)) (rcontext (ceval (epar₁ _) ∷ C) (dcpar₁ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ (ceval (epar₁ _)) sn⟶step ,
   Context1-sn⟶* (ceval (epar₁ _)) sn⟶*step ,
   Context1-∥R* (ceval (epar₁ _)) ∥R*step

DPG (∥Rstep (dcpar₁ dc∥R)) (rcontext _ (dcpar₂ dcsn⟶) psn⟶₁p')
 = _ ,
  rcontext _ (dcpar₂ dcsn⟶) psn⟶₁p' ,
  rrefl ,
  ∥Rn (∥Rstep (dcpar₁ dc∥R)) ∥R0

DPG (∥Rstep (dcpar₂ dc∥R)) (rcontext .[] dchole (rpar-done-right haltedp (dhalted p/halted)))
 = ⊥-elim (par-not-halted p/halted dc∥R)

DPG (∥Rstep (dcpar₂ dc∥R)) (rcontext .[] dchole (rpar-done-right hnothin (dpaused p/paused)))
 = _ ,
   rcontext [] dchole (rpar-done-right hnothin (dpaused (swap-paused-is-paused p/paused dc∥R))) ,
   rrefl ,
   ∥Rn (∥Rstep dc∥R) ∥R0

DPG (∥Rstep (dcpar₂ dc∥R)) (rcontext .[] dchole (rpar-done-right (hexit n) (dpaused p/paused)))
 =  _ ,
    rcontext [] dchole (rpar-done-right (hexit n) (dpaused (swap-paused-is-paused p/paused dc∥R))) ,
    rrefl ,
    ∥R0

DPG (∥Rstep (dcpar₂ dc∥R)) (rcontext .[] dchole (rpar-done-left donep haltedq))
 = ⊥-elim (par-not-halted haltedq dc∥R)

DPG (∥Rstep (dcpar₂ dc∥R)) (rcontext _ (dcpar₁ dcsn⟶) psn⟶₁p')
 = _ ,
   (rcontext _ (dcpar₁ dcsn⟶) psn⟶₁p') ,
   rrefl ,
   ∥Rn (∥Rstep (dcpar₂ dc∥R)) ∥R0

DPG (∥Rstep (dcpar₂ dc∥R)) (rcontext (c ∷ C) (dcpar₂ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcseq₁ ())) (rcontext .[] dchole rseq-done)

DPG (∥Rstep (dcseq₁ ())) (rcontext .[] dchole rseq-exit)

DPG (∥Rstep (dcseq₁ dc∥R)) (rcontext (c ∷ C) (dcseq₁ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcseq₁ dc∥R)) (rcontext _ (dcseq₂ dcsn⟶) psn⟶₁p')
 = _ ,
   rcontext _ (dcseq₂ dcsn⟶) psn⟶₁p' ,
   rrefl ,
   ∥Rn (∥Rstep (dcseq₁ dc∥R)) ∥R0

DPG (∥Rstep (dcseq₂ dc∥R)) (rcontext .[] dchole rseq-done)
 = _ , rcontext [] dchole rseq-done , rrefl , ∥Rn (∥Rstep dc∥R) ∥R0

DPG (∥Rstep (dcseq₂ dc∥R)) (rcontext .[] dchole rseq-exit)
 = _ , rcontext [] dchole rseq-exit , rrefl , ∥R0

DPG (∥Rstep (dcseq₂ dc∥R)) (rcontext _ (dcseq₁ dcsn⟶) psn⟶₁p')
 = _ ,
   rcontext _ (dcseq₁ dcsn⟶) psn⟶₁p' ,
   rrefl ,
   ∥Rn (∥Rstep (dcseq₂ dc∥R)) ∥R0

DPG (∥Rstep (dcseq₂ dc∥R)) (rcontext (c ∷ C) (dcseq₂ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcsuspend dc∥R)) (rcontext .[] dchole (rsuspend-done haltedp))
  = ⊥-elim (par-not-halted haltedp dc∥R)

DPG (∥Rstep (dcsuspend dc∥R)) (rcontext (c ∷ C) (dcsuspend dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dctrap dc∥R)) (rcontext .[] dchole (rtrap-done haltedp))
  = ⊥-elim (par-not-halted haltedp dc∥R)

DPG (∥Rstep (dctrap dc∥R)) (rcontext (c ∷ C) (dctrap dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcsignl dc∥R)) (rcontext .[] dchole rraise-signal)
 = _ ,
   (rcontext [] dchole rraise-signal) ,
   rrefl ,
   (∥Rn (∥Rstep (dcenv dc∥R)) ∥R0)

DPG (∥Rstep (dcsignl dc∥R)) (rcontext (c ∷ C) (dcsignl dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcpresent₁ dc∥R)) (rcontext .[] dchole ())

DPG (∥Rstep (dcpresent₁ dc∥R)) (rcontext (c ∷ C) (dcpresent₁ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcpresent₁ dc∥R)) (rcontext _ (dcpresent₂ dcsn⟶) psn⟶₁p')
  = _ ,
    rcontext _ (dcpresent₂ dcsn⟶) psn⟶₁p' ,
    rrefl ,
    ∥Rn (∥Rstep (dcpresent₁ dc∥R)) ∥R0

DPG (∥Rstep (dcpresent₂ dc∥R)) (rcontext .[] dchole ())

DPG (∥Rstep (dcpresent₂ dc∥R)) (rcontext _ (dcpresent₁ dcsn⟶) psn⟶₁p')
  = _ ,
    rcontext _ (dcpresent₁ dcsn⟶) psn⟶₁p' ,
    rrefl ,
    ∥Rn (∥Rstep (dcpresent₂ dc∥R)) ∥R0

DPG (∥Rstep (dcpresent₂ dc∥R)) (rcontext (c ∷ C) (dcpresent₂ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcloop dc∥R)) (rcontext .[] dchole rloop-unroll)
 = _ ,
   (rcontext [] dchole rloop-unroll) ,
   rrefl ,
   ∥Rn (∥Rstep (dcloopˢ₁ dc∥R)) (∥Rn (∥Rstep (dcloopˢ₂ dc∥R)) ∥R0)

DPG (∥Rstep (dcloop dc∥R)) (rcontext (c ∷ C) (dcloop dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcloopˢ₁ ())) (rcontext .[] dchole rloopˢ-exit)

DPG (∥Rstep (dcloopˢ₁ dc∥R)) (rcontext (c ∷ C) (dcloopˢ₁ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcloopˢ₁ dc∥R)) (rcontext _ (dcloopˢ₂ dcsn⟶) psn⟶₁p')
 = _ ,
   rcontext _ (dcloopˢ₂ dcsn⟶) psn⟶₁p' ,
   rrefl ,
   ∥Rn (∥Rstep (dcloopˢ₁ dc∥R)) ∥R0

DPG (∥Rstep (dcloopˢ₂ dc∥R)) (rcontext .[] dchole rloopˢ-exit)
 = _ ,
   (rcontext [] dchole rloopˢ-exit) ,
   rrefl ,
   ∥R0

DPG (∥Rstep (dcloopˢ₂ dc∥R)) (rcontext _ (dcloopˢ₁ dcsn⟶) psn⟶₁p')
 = _ ,
   rcontext _ (dcloopˢ₁ dcsn⟶) psn⟶₁p' ,
   rrefl ,
   ∥Rn (∥Rstep (dcloopˢ₂ dc∥R)) ∥R0

DPG (∥Rstep (dcloopˢ₂ dc∥R)) (rcontext (c ∷ C) (dcloopˢ₂ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcshared dc∥R)) (rcontext .[] dchole ())

DPG (∥Rstep (dcshared dc∥R)) (rcontext (c ∷ C) (dcshared dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcvar dc∥R)) (rcontext .[] dchole ())

DPG (∥Rstep (dcvar dc∥R)) (rcontext (c ∷ C) (dcvar dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcif₁ dc∥R)) (rcontext .[] dchole ())

DPG (∥Rstep (dcif₁ dc∥R)) (rcontext (c ∷ C) (dcif₁ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcif₁ dc∥R)) (rcontext _ (dcif₂ dcsn⟶) psn⟶₁p')
 = _ ,
   rcontext _ (dcif₂ dcsn⟶) psn⟶₁p' ,
   rrefl ,
   ∥Rn (∥Rstep (dcif₁ dc∥R)) ∥R0

DPG (∥Rstep (dcif₂ dc∥R)) (rcontext .[] dchole ())

DPG (∥Rstep (dcif₂ dc∥R)) (rcontext _ (dcif₁ dcsn⟶) psn⟶₁p')
 = _ ,
   rcontext _ (dcif₁ dcsn⟶) psn⟶₁p' ,
   rrefl ,
   ∥Rn (∥Rstep (dcif₂ dc∥R)) ∥R0

DPG (∥Rstep (dcif₂ dc∥R)) (rcontext (c ∷ C) (dcif₂ dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

DPG (∥Rstep (dcenv dc∥R)) (rcontext{p' = p'} .[] dchole psn⟶₁p')
  with ρ-stays-ρ-sn⟶₁ psn⟶₁p'
... | θ' , q , refl
  with get-view psn⟶₁p'
... | inj₂ (eq , pot-view) = DPG-pot-view dc∥R psn⟶₁p' eq pot-view  
... | inj₁ (E , pin , qin , peq , qeq , E-view) with
   DPG-E-view peq qeq dc∥R psn⟶₁p' E-view
... | (d , sn⟶step , ∥R*-step , _ )
  = _ ,
    rcontext [] dchole sn⟶step ,
    rrefl ,
    Context1-∥R* (cenv θ') ∥R*-step

DPG (∥Rstep (dcenv dc∥R)) (rcontext (c ∷ C) (dcenv dcsn⟶) psn⟶₁p')
 with DPG (∥Rstep dc∥R) (rcontext C dcsn⟶ psn⟶₁p')
... | _ , sn⟶step , sn⟶*step , ∥R*step
 = _ ,
   Context1-sn⟶ c sn⟶step ,
   Context1-sn⟶* c sn⟶*step ,
   Context1-∥R* c ∥R*step

