module calculus.properties where

open import utility

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
open import Esterel.Lang.CanFunction
  using (Canθₛ ; Canθₛₕ ; [S]-env)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; sig ; []env ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c ; dchole)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)
open import Esterel.Context.Properties

open import Relation.Nullary
  using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)
open import Data.Empty
  using (⊥ ; ⊥-elim)
import Data.FiniteMap
open import Data.List
  using (List ; _∷_ ; [] ; _++_)
open import Data.List.All as All
  using (All ; _∷_ ; [])
open import Data.Nat
  using (ℕ ; zero ; suc ; _+_)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; _,′_ ; ∃)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality

open import sn-calculus
open import calculus
open import par-swap
open import par-swap.union-properties using (∥R∪sn≡ₑ-consistent)

open import binding-preserve using (CB-preservation*)

⟶*-concat : ∀ {p q r} -> p ⟶* q -> q ⟶* r -> p ⟶* r
⟶*-concat [refl] q⟶*r = q⟶*r
⟶*-concat ([step] p⟶q p⟶*q) q⟶*r = [step] p⟶q (⟶*-concat p⟶*q q⟶*r)

⟶*->∥R*∪sn⟶* : ∀ {p q} -> p ⟶* q -> p ∥R*∪sn⟶* q
⟶*->∥R*∪sn⟶* = thm where

 thm : ∀ {p q} -> p ⟶* q -> p ∥R*∪sn⟶* q
 thm [refl] = ∪refl
 thm ([step] ([context] C dc p⟶₁p') p'⟶*q) with thm p'⟶*q
 thm ([step] ([context] C dc [par-swap]) p'⟶*q) | R
  = ∪∥R* (∥Rn (∥Rstep{C} dc) ∥R0) R
 thm ([step] ([context] C dc ([par-nothing] doneq)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rpar-done-right hnothin doneq)) rrefl) R
 thm ([step] ([context] C dc ([par-1exit] n pausedq)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rpar-done-right (hexit n) (dpaused pausedq))) rrefl) R
 thm ([step] ([context] C dc ([par-2exit] n m)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rpar-done-right (hexit n) (dhalted (hexit m)))) rrefl) R
 thm ([step] ([context] C dc ([is-present] S S∈ θ[S]≡present de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (ris-present{S = S} S∈ θ[S]≡present de)) rrefl) R
 thm ([step] ([context] C dc ([is-absent] S S∈ θ[S]≡absent de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (ris-absent{S = S} S∈ θ[S]≡absent de)) rrefl) R
 thm ([step] ([context] C dc ([emit] S∈ ¬S≡a de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (remit S∈ ¬S≡a de)) rrefl) R
 thm ([step] ([context] C dc [loop-unroll]) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc rloop-unroll) rrefl) R
 thm ([step] ([context] C dc [seq-done]) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc rseq-done) rrefl) R
 thm ([step] ([context] C dc [seq-exit]) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc rseq-exit) rrefl) R
 thm ([step] ([context] C dc [loopˢ-exit]) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc rloopˢ-exit) rrefl) R
 thm ([step] ([context] C dc ([suspend-done] haltedp)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rsuspend-done haltedp)) rrefl) R
 thm ([step] ([context] C dc ([trap-done] haltedp)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rtrap-done haltedp)) rrefl) R
 thm ([step] ([context] C dc [raise-signal]) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc rraise-signal) rrefl) R
 thm ([step] ([context] C dc ([raise-shared] all-readyeθ de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rraise-shared all-readyeθ de)) rrefl) R
 thm ([step] ([context] C dc ([set-shared-value-old] e' s∈ θ[s]≡old de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rset-shared-value-old e' s∈ θ[s]≡old de)) rrefl) R
 thm ([step] ([context] C dc ([set-shared-value-new] e' s∈ θ[s]≡n de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rset-shared-value-new e' s∈ θ[s]≡n de)) rrefl) R
 thm ([step] ([context] C dc ([raise-var] all-readyeθ de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rraise-var all-readyeθ de)) rrefl) R
 thm ([step] ([context] C dc ([set-var] x∈ all-readyeθ de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rset-var x∈ all-readyeθ de)) rrefl) R
 thm ([step] ([context] C dc ([if-false] x∈ θ[x]≡z de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rif-false x∈ θ[x]≡z de)) rrefl) R
 thm ([step] ([context] C dc ([if-true] x∈ θ[x]≡s de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rif-true x∈ θ[x]≡s de)) rrefl) R
 thm ([step] ([context] C dc ([absence] S S∈ θ[S]≡unknown S∉Canθₛ)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rabsence{S = S} S∈ θ[S]≡unknown S∉Canθₛ)) rrefl) R
 thm ([step] ([context] C dc ([readyness] s s∈ θ[s]≡old⊎θ[s]≡new s∉Canθₛₕ)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rreadyness{s = s} s∈ θ[s]≡old⊎θ[s]≡new s∉Canθₛₕ)) rrefl) R
 thm ([step] ([context] C dc ([merge] de)) p'⟶*q) | R
  = ∪sn⟶* (rstep (rcontext C dc (rmerge de)) rrefl) R

∥R*∪sn⟶*->⟶* : ∀ {p q} -> p ∥R*∪sn⟶* q -> p ⟶* q
∥R*∪sn⟶*->⟶* = thm where

  p∥R*q->p⟶*q : ∀ {p q} -> p ∥R* q -> p ⟶* q
  p∥R*q->p⟶*q ∥R0 = [refl]
  p∥R*q->p⟶*q (∥Rn (∥Rstep d≐C⟦p∥q⟧c) p∥R*q)
   = [step] ([context] _ d≐C⟦p∥q⟧c [par-swap]) (p∥R*q->p⟶*q p∥R*q)

  sn* : ∀ {p q} -> p sn⟶* q -> p ⟶* q
  sn* rrefl = [refl]
  sn* (rstep (rcontext C dc step) more) with sn* more
  sn* (rstep (rcontext C dc (rpar-done-right hnothin q')) _) | R
   = [step] ([context] C dc ([par-nothing] q')) R
  sn* (rstep (rcontext C dc (rpar-done-right (hexit n) (dhalted hnothin))) _) | R
   = [step] ([context] C dc [par-swap])
     ([step] ([context] C Crefl ([par-nothing] (dhalted (hexit n))))
      R)
  sn* (rstep (rcontext C dc (rpar-done-right (hexit n) (dhalted (hexit m)))) _) | R
   = [step] ([context] C dc ([par-2exit] n m)) R
  sn* (rstep (rcontext C dc (rpar-done-right (hexit n) (dpaused p/paused))) _) | R
   = [step] ([context] C dc ([par-1exit] n p/paused)) R
  sn* (rstep (rcontext C dc (rpar-done-left (dhalted hnothin) q')) more) | R
   = [step] ([context] C dc ([par-nothing] (dhalted q'))) R
  sn* (rstep (rcontext C dc (rpar-done-left (dhalted (hexit n)) hnothin)) more) | R
   = [step] ([context] C dc [par-swap])
     ([step] ([context] C Crefl ([par-nothing] (dhalted (hexit n))))
      R)
  sn* (rstep (rcontext C dc (rpar-done-left (dhalted (hexit n)) (hexit m))) more) | R
   = [step] ([context] C dc ([par-2exit] n m)) R
  sn* (rstep (rcontext C dc (rpar-done-left (dpaused p/paused) hnothin)) more) | R
   = [step] ([context] C dc [par-swap])
     ([step] ([context] C Crefl ([par-nothing] (dpaused p/paused)))
      R)
  sn* (rstep (rcontext C dc (rpar-done-left (dpaused p/paused) (hexit n))) more) | R
   = [step] ([context] C dc [par-swap])
     ([step] ([context] C Crefl ([par-1exit] n p/paused))
      R)
  sn* (rstep (rcontext C dc (ris-present{S = S} S∈ x x₁)) _) | R
   = [step] ([context] C dc ([is-present] S S∈ x x₁)) R
  sn* (rstep (rcontext C dc (ris-absent{S = S} S∈ x x₁)) _) | R
   = [step] ([context] C dc ([is-absent] S S∈ x x₁)) R
  sn* (rstep (rcontext C dc (remit S∈ ¬S≡a x)) _) | R
   = [step] ([context] C dc ([emit] S∈ ¬S≡a x)) R
  sn* (rstep (rcontext C dc rloop-unroll) _) | R
   = [step] ([context] C dc [loop-unroll]) R
  sn* (rstep (rcontext C dc rseq-done) _) | R
   = [step] ([context] C dc [seq-done]) R
  sn* (rstep (rcontext C dc rseq-exit) _) | R
   = [step] ([context] C dc [seq-exit]) R
  sn* (rstep (rcontext C dc rloopˢ-exit) _) | R
   = [step] ([context] C dc [loopˢ-exit]) R
  sn* (rstep (rcontext C dc (rsuspend-done x)) _) | R
   = [step] ([context] C dc ([suspend-done] x)) R
  sn* (rstep (rcontext C dc (rtrap-done p')) _) | R
   = [step] ([context] C dc ([trap-done] p')) R
  sn* (rstep (rcontext C dc rraise-signal) _) | R
   = [step] ([context] C dc [raise-signal]) R
  sn* (rstep (rcontext C dc (rraise-shared e' x)) _) | R
   = [step] ([context] C dc ([raise-shared] e' x)) R
  sn* (rstep (rcontext C dc (rset-shared-value-old e' s∈ x x₁)) _) | R
   = [step] ([context] C dc ([set-shared-value-old] e' s∈ x x₁)) R
  sn* (rstep (rcontext C dc (rset-shared-value-new e' s∈ x x₁)) _) | R
   = [step] ([context] C dc ([set-shared-value-new] e' s∈ x x₁)) R
  sn* (rstep (rcontext C dc (rraise-var e' x₁)) _) | R
   = [step] ([context] C dc ([raise-var] e' x₁)) R
  sn* (rstep (rcontext C dc (rset-var x∈ e' x₁)) _) | R
   = [step] ([context] C dc ([set-var] x∈ e' x₁)) R
  sn* (rstep (rcontext C dc (rif-false x∈ x₁ x₂)) _) | R
   = [step] ([context] C dc ([if-false] x∈ x₁ x₂)) R
  sn* (rstep (rcontext C dc (rif-true x∈ x₁ x₂)) _) | R
   = [step] ([context] C dc ([if-true] x∈ x₁ x₂)) R
  sn* (rstep (rcontext C dc (rabsence{S = S} S∈ x x₁)) _) | R
   = [step] ([context] C dc ([absence] S S∈ x x₁)) R
  sn* (rstep (rcontext C dc (rreadyness{s = s} s∈ x x₁)) _) | R
   = [step] ([context] C dc ([readyness] s s∈ x x₁)) R
  sn* (rstep (rcontext C dc (rmerge x)) _) | R
   = [step] ([context] C dc ([merge] x)) R


  thm : ∀ {p q} -> p ∥R*∪sn⟶* q -> p ⟶* q
  thm (∪∥R* p∥R*q p∥R*∪sn⟶*q)
   = ⟶*-concat (p∥R*q->p⟶*q p∥R*q) (thm p∥R*∪sn⟶*q)
  thm (∪sn⟶* psn⟶*q p∥R*∪sn⟶*q)
   = ⟶*-concat (sn* psn⟶*q)  (thm p∥R*∪sn⟶*q)
  thm ∪refl = [refl]

≡ₑ-to-∥R∪sn≡ₑ : ∀ {p q} ->
  p ≡ₑ q # [] ->
  p ∥R∪sn≡ₑ q
≡ₑ-to-∥R∪sn≡ₑ
 = λ p≡ₑq#[] → thm Crefl Crefl p≡ₑq#[] where

 lift-∥R* : ∀ {p q} ->
    p ∥R* q ->
    p ∥R∪sn≡ₑ q
 lift-∥R* ∥R0 = ∪ref
 lift-∥R* (∥Rn p∥Rr r⟶q)
  = ∪trn (∪stp∥ p∥Rr) (lift-∥R* r⟶q)

 lift-sn⟶* : ∀ {p q} ->
    p sn⟶* q ->
    p ∥R∪sn≡ₑ q
 lift-sn⟶* rrefl = ∪ref
 lift-sn⟶* (rstep psn⟶r r⟶q)
  = ∪trn (∪stpsn psn⟶r) (lift-sn⟶* r⟶q)

 lift-∪ : ∀ {p q} ->
    p ∥R*∪sn⟶* q ->
    p ∥R∪sn≡ₑ q
 lift-∪ (∪∥R* p∥R*r r⟶*q)
   = ∪trn (lift-∥R* p∥R*r) (lift-∪ r⟶*q)
 lift-∪ (∪sn⟶* psn⟶*r r⟶*q)
   = ∪trn (lift-sn⟶* psn⟶*r) (lift-∪ r⟶*q)
 lift-∪ ∪refl = ∪ref

 thm : ∀ {p′ p q′ q C} ->
   (p′C : p′ ≐ C ⟦ p ⟧c) ->
   (q′C : q′ ≐ C ⟦ q ⟧c) ->
   p ≡ₑ q # C ->
   p′ ∥R∪sn≡ₑ q′

 thm p′C q′C ≡ₑrefl
  rewrite sym (unplugc p′C) | sym (unplugc q′C)
  = ∪ref

 thm p′C q′C (≡ₑtran p≡ₑr r≡ₑq)
  with thm p′C Crefl p≡ₑr
 ... | p′∪≡r′
  with thm Crefl q′C r≡ₑq
 ... | r′∪≡q′ = ∪trn p′∪≡r′ r′∪≡q′

 thm p′C q′C (≡ₑsymm CBq p≡ₑq)
  with thm q′C p′C p≡ₑq
 ... | q∪≡p rewrite sym (unplugc q′C)
  = ∪sym q∪≡p CBq

 thm p′C q′C (≡ₑctxt pC′ qC′ C′⟦p₂⟧≡ₑC′⟦q₂⟧)
  = thm (C++ p′C pC′)
        (C++ q′C qC′)
        C′⟦p₂⟧≡ₑC′⟦q₂⟧

 thm p′C q′C (≡ₑstep p⟶₁q)
  with ⟶*->∥R*∪sn⟶* ([step] ([context] _ p′C p⟶₁q) [refl])
 ... | p′∥R*∪sn⟶*q′ rewrite sym (unplugc q′C)
  = lift-∪ p′∥R*∪sn⟶*q′

∥R∪sn≡-to-≡ₑ : ∀ {p q} ->
  p ∥R∪sn≡ₑ q ->
  p ≡ₑ q # []
∥R∪sn≡-to-≡ₑ = thm where

 lift⟶* : ∀ {p q} ->
  p ⟶* q ->
  p ≡ₑ q # []
 lift⟶* [refl] = ≡ₑrefl
 lift⟶* ([step] ([context] C dc p⟶₁p') r⟶*q) =
   ≡ₑtran (≡ₑctxt dc Crefl (≡ₑstep p⟶₁p'))
          (lift⟶* r⟶*q)

 thm  : ∀ {p q} ->
  p ∥R∪sn≡ₑ q ->
  p ≡ₑ q # []
 thm (∪stpsn psn⟶q) =
   lift⟶*
    (∥R*∪sn⟶*->⟶*
     (∪sn⟶* (rstep psn⟶q rrefl)
             ∪refl))
 thm (∪stp∥ (∥Rstep d≐C⟦p∥q⟧c))
   = ≡ₑctxt d≐C⟦p∥q⟧c Crefl
            (≡ₑstep [par-swap]) 
 thm (∪sym q∪≡p CBq)
  with thm q∪≡p
 ... | q≡ₑp
  = ≡ₑsymm CBq q≡ₑp
 thm ∪ref = ≡ₑrefl
 thm (∪trn p∪≡r r∪≡q)
  with thm p∪≡r
 ... | p≡ₑr
   with thm r∪≡q
 ... | r≡ₑq
  = ≡ₑtran p≡ₑr r≡ₑq

≡ₑ-consistent : ∀{p q BV FV}
                → CorrectBinding p BV FV
                → p ≡ₑ q # []
                → Σ[ r ∈ Term ] p ⟶* r × q ⟶* r
≡ₑ-consistent CB eq with ∥R∪sn≡ₑ-consistent CB (≡ₑ-to-∥R∪sn≡ₑ eq)
≡ₑ-consistent CB₁ eq | r , p∥⟶*r , q∥⟶*r
  = r , (∥R*∪sn⟶*->⟶* p∥⟶*r) , (∥R*∪sn⟶*->⟶* q∥⟶*r)

∥R*-preserve-CB : ∀ p q → (⊢C⟦p⟧ : CB p) → (p∥R*q :  p ∥R* q) → CB q
∥R*-preserve-CB p .p ⊢C⟦p⟧ ∥R0 = ⊢C⟦p⟧
∥R*-preserve-CB p q₁ ⊢C⟦p⟧ (∥Rn (∥Rstep d≐C⟦p∥q⟧c) p∥R*q) with binding-extractc' ⊢C⟦p⟧ d≐C⟦p∥q⟧c
... | (FV' , BV') , CB2 with CB2
... | (CBpar{BVp = BVp}{FVp = FVp} y y₁ BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) with n
  where
    n = binding-substc' ⊢C⟦p⟧ d≐C⟦p∥q⟧c CB2 (∪-comm-⊆-left BVp ⊆-refl) ((∪-comm-⊆-left FVp ⊆-refl)) ((CBpar y₁ y (distinct-sym BVp≠BVq)  (distinct-sym BVp≠FVq) (distinct-sym FVp≠BVq) (distinct'-sym Xp≠Xq)))
... | (_ , _ , cb) with BVFVcorrect _ _ _ cb
... | refl , refl = ∥R*-preserve-CB _ _ cb p∥R*q

∥R*∪sn⟶*-preserve-CB : ∀ p q → (⊢C⟦p⟧ : CB p) → (p∥R*∪sn⟶*q : p ∥R*∪sn⟶* q) → CB q
∥R*∪sn⟶*-preserve-CB p q ⊢C⟦p⟧ (∪∥R* p∥R*q p∥R*∪sn⟶*q)
  = ∥R*∪sn⟶*-preserve-CB _ _ (∥R*-preserve-CB _ _ ⊢C⟦p⟧ p∥R*q) p∥R*∪sn⟶*q
∥R*∪sn⟶*-preserve-CB p q ⊢C⟦p⟧ (∪sn⟶* psn⟶*q p∥R*∪sn⟶*q)
  = ∥R*∪sn⟶*-preserve-CB _ _ next p∥R*∪sn⟶*q
  where
    next = CB-preservation* p _ ⊢C⟦p⟧  psn⟶*q
∥R*∪sn⟶*-preserve-CB p .p ⊢C⟦p⟧ ∪refl = ⊢C⟦p⟧

⟶₁-preserve-CB : ∀ p q C → (⊢C⟦p⟧ : CB (C ⟦ p ⟧c)) → (p⟶₁q : p ⟶₁ q) → CB (C ⟦ q ⟧c)
⟶₁-preserve-CB p q C ⊢C⟦p⟧ p⟶₁q with (⟶*->∥R*∪sn⟶* ([step] ([context] C Crefl p⟶₁q) [refl]))
... | p∥R*∪sn⟶*q = ∥R*∪sn⟶*-preserve-CB (C ⟦ p ⟧c) (C ⟦ q ⟧c) ⊢C⟦p⟧ p∥R*∪sn⟶*q
