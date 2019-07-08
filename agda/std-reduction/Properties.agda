module std-reduction.Properties where

open import std-reduction
open import std-reduction.Base
open import std-reduction.Can
open import sn-calculus
open import Esterel.Context
open import Esterel.Context.Properties
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.CanFunction
  using (Canθₛ ; Canθₛₕ ; [S]-env)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; sig ; []env ; module SigMap ; module ShrMap ; module VarMap)
import Esterel.Variable.Signal as Signal



open import utility
  using (_∉_)
  renaming (module UniquedSet to US)
open US using (UniquedSet ; uniqued-set)

open import Relation.Binary.PropositionalEquality using (_≡_ ; sym)
open import Function
  using (_∘_ ; _$_ ; _∋_)
open import Data.List using (_∷_ ; map ; [])
open import Data.Product using (_,_ ; proj₁ ; proj₂)


open _≡_

sn⟶₁->⟶* : ∀{p q} → p sn⟶₁ q → p sn⟶* q
sn⟶₁->⟶* = sn⟶*-inclusion ∘ sn⟶-inclusion

sn⟶₁->⟶*+E : ∀{p q E rp}
               → (rp=E⟦p⟧ : rp ≐ E ⟦ p ⟧e) 
               → p sn⟶₁ q
               → rp sn⟶* (E ⟦ q ⟧e)
sn⟶₁->⟶*+E {E = E} rp=E⟦p⟧ psn⟶₁q with Context-sn⟶ (map ceval E) (⟦⟧e-to-⟦⟧c rp=E⟦p⟧) $ sn⟶-inclusion psn⟶₁q
... | r' , r'=E⟦q⟧  , rpsn⟶r' rewrite sym $ unplug $ ⟦⟧c-to-⟦⟧e r'=E⟦q⟧ =  sn⟶*-inclusion rpsn⟶r'

sn⟶₁->⟶*+Eρθ : ∀{p q E rp θ A}
               → (rp=E⟦p⟧ : rp ≐ E ⟦ p ⟧e) 
               → p sn⟶₁ q
               → (ρ⟨ θ , A ⟩· rp) sn⟶* (ρ⟨ θ , A ⟩· (E ⟦ q ⟧e))
sn⟶₁->⟶*+Eρθ {θ = θ}{A} rp=E⟦p⟧ psn⟶₁q = (Context-sn⟶* (cenv θ A ∷ [])) $ sn⟶₁->⟶*+E rp=E⟦p⟧ psn⟶₁q 

std-redution-deterministic : ∀{p q r} →
                             p ⇁ q →
                             p ⇁ r →
                             q ≡ r
std-redution-deterministic = {!!}

{- Helper for std=>calc for the absence rule -}
std=>calc-for-absence' : ∀{θ A p} → ∀ lst unq
                        → ρ⟨ θ , A ⟩· p sn⟶* ρ⟨ (set-all-absent θ p lst unq) , A ⟩· p
std=>calc-for-absence' [] US.e = rrefl
std=>calc-for-absence'{θ}{A}{p} lst1@((S , x) ∷ lst) unq1@(US.c .(S , x) .lst fx∉l unq)
  = sn⟶*+{p = ρ⟨ θ , A ⟩· p}{q = ρ⟨ (set-all-absent θ p lst1 unq1) , A ⟩· p} (std=>calc-for-absence' lst unq)
    $ sn⟶*-inclusion
    $ rcontext [] dchole
    $ rabsence (set-all-absent∈ θ p S lst unq S∈) (proj₂ (can-set-absent∈-update{θ}{p} lst unq S S∈ fx∉l S≡u))
    $ ((Signal.unwrap S) ∉ Canθₛ (sig (set-all-absent θ p lst unq)) 0 p []env) ∋ {!!}
    where open CanSetToAbsent x

std=>calc-for-absence : ∀{θ A p} → ∀ uns
                        → ρ⟨ θ , A ⟩· p sn⟶* ρ⟨ (US.curry (set-all-absent θ p) uns) , A ⟩· p
std=>calc-for-absence{θ}{A}{p} (uniqued-set lst unq) = std=>calc-for-absence' {θ}{A}{p} lst unq
                        {-
std=>calc-for-absence {Ss = []} = rrefl
std=>calc-for-absence{θ}{A}{p} {Ss = (S , x) ∷ Ss}
   = sn⟶*+ (std=>calc-for-absence {Ss = Ss})
     $ sn⟶*-inclusion
     $ rcontext [] dchole
     $ rabsence (set-all-absent∈ θ p S Ss S∈) {!!}
     $ {!!}
    where open CanSetToAbsent x
    -}

std=>calc : ∀{p q} → p ⇁ q → p sn⟶* q
std=>calc (std-par-right lmθE haltedp doneq r=E⟦p∥q⟧) = sn⟶₁->⟶*+Eρθ r=E⟦p∥q⟧ (rpar-done-right haltedp doneq)
std=>calc (std-par-left lmθE pausedp haltedq r=E⟦p∥q⟧) = sn⟶₁->⟶*+Eρθ r=E⟦p∥q⟧
                                                           (rpar-done-left (dpaused pausedp)
                                                            haltedq)
std=>calc (std-is-present lmθE S S∈ θ⦅S⦆=present r=E⟦presentSpq⟧) = rstep
                                                                      (rcontext [] dchole (ris-present S∈ θ⦅S⦆=present r=E⟦presentSpq⟧))
                                                                      rrefl
std=>calc (std-is-absent lmθE S S∈ θ⦅S⦆=absent r=E⟦presentSpq⟧) = rstep
                                                                    (rcontext [] dchole (ris-absent S∈ θ⦅S⦆=absent r=E⟦presentSpq⟧))
                                                                    rrefl
std=>calc (std-emit lmθE S S∈ ¬S≡a r=E⟦emitS⟧) = rstep (rcontext [] dchole (remit S∈ ¬S≡a r=E⟦emitS⟧)) rrefl
std=>calc (std-loop-unroll lmθE r=E⟦loopp⟧) = sn⟶₁->⟶*+Eρθ r=E⟦loopp⟧ rloop-unroll
std=>calc (std-seq-done lmθE r=E⟦nothing>>q⟧) = sn⟶₁->⟶*+Eρθ r=E⟦nothing>>q⟧ rseq-done
std=>calc (std-seq-exit lmθE r=E⟦exitn>>q⟧) = sn⟶₁->⟶*+Eρθ r=E⟦exitn>>q⟧ rseq-exit
std=>calc (std-loopˢ-exit lmθE r=E⟦loopˢexitnq⟧) = sn⟶₁->⟶*+Eρθ r=E⟦loopˢexitnq⟧ rloopˢ-exit
std=>calc (std-suspend-done lmθE haltedp r=E⟦suspendpS⟧) = sn⟶₁->⟶*+Eρθ r=E⟦suspendpS⟧ (rsuspend-done haltedp)
std=>calc (std-trap-done lmθE haltedp r=E⟦trapp⟧) = sn⟶₁->⟶*+Eρθ r=E⟦trapp⟧ (rtrap-done haltedp)
std=>calc (std-raise-signal lmθE r=E⟦signalsp⟧) = sn⟶₁->⟶*+Eρθ r=E⟦signalsp⟧ rraise-signal
std=>calc (std-raise-shared lmθE e' r=E⟦shareds=ep⟧) = rstep (rcontext [] dchole (rraise-shared e' r=E⟦shareds=ep⟧)) rrefl
std=>calc (std-set-shared-value-old lmθE e' s∈ θ⦅s⦆=old r=E⟦s<=e⟧) = rstep
                                                                       (rcontext [] dchole
                                                                        (rset-shared-value-old e' s∈ θ⦅s⦆=old r=E⟦s<=e⟧))
                                                                       rrefl
std=>calc (std-set-shared-value-new lmθE e' s∈ θ⦅s⦆=new r=E⟦s<=e⟧) = rstep (rcontext [] dchole (rset-shared-value-new e' s∈ θ⦅s⦆=new r=E⟦s<=e⟧)) rrefl
std=>calc (std-raise-var lmθE e' r=E⟦varx=ep⟧) = rstep (rcontext [] dchole (rraise-var e' r=E⟦varx=ep⟧)) rrefl
std=>calc (std-set-var lmθE x∈ e' r=E⟦x=e⟧) = rstep (rcontext [] dchole (rset-var x∈ e' r=E⟦x=e⟧)) rrefl
std=>calc (std-if-false lmθE x∈ θ⦅x⦆=0 r=E⟦ifxpq⟧) = rstep (rcontext [] dchole (rif-false x∈ θ⦅x⦆=0 r=E⟦ifxpq⟧)) rrefl
std=>calc (std-if-true lmθE x∈ θ⦅x⦆≠0 r=E⟦ifxpq⟧) = rstep (rcontext [] dchole (rif-true x∈ θ⦅x⦆≠0 r=E⟦ifxpq⟧)) rrefl
std=>calc (std-merge lmθ₁E r=E⟦ρ⟨θ₂,A₂⟩·p⟧) = rstep (rcontext [] dchole (rmerge r=E⟦ρ⟨θ₂,A₂⟩·p⟧)) rrefl
std=>calc (std-absent{θ}{p}{A} BVDθAp can-set-something-absent) = std=>calc-for-absence (can-set-absent θ p)
std=>calc (std-readyness BVDθAp can-set-nothing-absent can-set-something-ready) = {!!}

