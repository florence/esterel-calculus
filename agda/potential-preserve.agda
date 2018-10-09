{-
This file proves the monotonicity of potential function over reductions.
CorrectBinding is required in order to guarantee that SI and SC introduced
by the loop never accidentally capture signals in the loop body.


canₖ-monotonic : ∀ {BV FV} θ r r' →
  CorrectBinding r BV FV →
  r sn⟶₁ r' →
  ∀ k →
    k ∈ Canₖ r' θ →
    k ∈ Canₖ r θ

canₛ-monotonic : ∀ {BV FV} θ r r' →
  CorrectBinding r BV FV →
  r sn⟶₁ r' →
  ∀ S' →
    Signal.unwrap S' ∈ Canₛ r' θ →
    Signal.unwrap S' ∈ Canₛ r θ

canₛₕ-monotonic : ∀ {BV FV} θ r r' →
  CorrectBinding r BV FV →
  r sn⟶₁ r' →
  ∀ s' →
    SharedVar.unwrap s' ∈ Canₛₕ r' θ →
    SharedVar.unwrap s' ∈ Canₛₕ r θ


In addition to the main lemmas, there are various random small propositions
dealing with the computatin of the calculation of Can in the loop body
(the big ρ-θ-emit-present term introduced by the loop-unroll rule).
-}
module potential-preserve where

open import sn-calculus
open import utility

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
open import Esterel.Lang.PotentialFunction
open import Esterel.Lang.PotentialFunction.Properties
open import Esterel.Context
  using (EvaluationContext1 ; EvaluationContext ; _⟦_⟧e ; _≐_⟦_⟧e)
open import Esterel.Context.Properties
  using (unplug ; Erefl)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)

open import Data.Bool
  using (Bool ; true ; false ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; [] ; _∷_ ; _++_ ; map ; concatMap ; foldr)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using (++ˡ ; ++ʳ)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_)
open import Data.Product
  using (Σ ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; _∋_ ; id)
open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; trans ; sym ; cong ; subst
       ; inspect ; Reveal_·_is_ ; [_] ; module ≡-Reasoning)

open EvaluationContext1
open _≐_⟦_⟧e

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

open ListSet Data.Nat._≟_
  using (set-subtract ; set-subtract-[] ; set-subtract-split ; set-subtract-merge
       ; set-subtract-notin ; set-subtract-[a]≡set-remove
       ; set-remove-mono-∈ ; set-remove-removed ; set-remove-not-removed)


canₛ-present-lemma : ∀ S p q θ →
  ∀ S' →
    Signal.unwrap S' ∈ Canₛ (present S ∣⇒ p ∣⇒ q) θ →
    Signal.unwrap S' ∈ Canₛ p θ ⊎ Signal.unwrap S' ∈ Canₛ q θ
canₛ-present-lemma S p q θ S' S'∈can-present with Env.Sig∈ S θ
canₛ-present-lemma S p q θ S' S'∈can-present | yes S∈
  with Env.sig-stats {S} θ S∈
... | Signal.present = inj₁ S'∈can-present
... | Signal.absent  = inj₂ S'∈can-present
... | Signal.unknown = ++⁻ (Canₛ p θ) S'∈can-present
canₛ-present-lemma S p q θ S' S'∈can-present | no  S∉ =
  ++⁻ (Canₛ p θ) S'∈can-present


canₛₕ-present-lemma : ∀ S p q θ →
  Canₛₕ p θ ≡ [] → Canₛₕ q θ ≡ [] →
  Canₛₕ (present S ∣⇒ p ∣⇒ q) θ ≡ []
canₛₕ-present-lemma S p q θ can-p≡[] can-q≡[] with Env.Sig∈ S θ
canₛₕ-present-lemma S p q θ can-p≡[] can-q≡[] | yes S∈
  with Env.sig-stats {S} θ S∈
... | Signal.present = can-p≡[]
... | Signal.absent  = can-q≡[]
... | Signal.unknown rewrite can-p≡[] | can-q≡[] = refl
canₛₕ-present-lemma S p q θ can-p≡[] can-q≡[] | no  S∉
  rewrite can-p≡[] | can-q≡[] = refl


canₖ-monotonic : ∀ {BV FV} θ r r' →
  CorrectBinding r BV FV →
  r sn⟶₁ r' →
  ∀ k →
    k ∈ Canₖ r' θ →
    k ∈ Canₖ r θ

canₛ-monotonic : ∀ {BV FV} θ r r' →
  CorrectBinding r BV FV →
  r sn⟶₁ r' →
  ∀ S' →
    Signal.unwrap S' ∈ Canₛ r' θ →
    Signal.unwrap S' ∈ Canₛ r θ

canₛₕ-monotonic : ∀ {BV FV} θ r r' →
  CorrectBinding r BV FV →
  r sn⟶₁ r' →
  ∀ s' →
    SharedVar.unwrap s' ∈ Canₛₕ r' θ →
    SharedVar.unwrap s' ∈ Canₛₕ r θ

canθₖ-monotonic : ∀ sigs S' → ∀ {BV FV} θ r r' →
  CorrectBinding r BV FV →
  r sn⟶₁ r' →
  ∀ k →
    k ∈ Canθₖ sigs S' r' θ →
    k ∈ Canθₖ sigs S' r θ

canθₛ-monotonic : ∀ sigs S'' → ∀ {BV FV} θ r r' →
  CorrectBinding r BV FV →
  r sn⟶₁ r' →
  ∀ S' →
    Signal.unwrap S' ∈ Canθₛ sigs S'' r' θ →
    Signal.unwrap S' ∈ Canθₛ sigs S'' r θ

canθₛₕ-monotonic : ∀ sigs S' → ∀ {BV FV} θ r r' →
  CorrectBinding r BV FV →
  r sn⟶₁ r' →
  ∀ s' →
    SharedVar.unwrap s' ∈ Canθₛₕ sigs S' r' θ →
    SharedVar.unwrap s' ∈ Canθₛₕ sigs S' r θ

canθₖ-monotonic [] S' cb red = canₖ-monotonic cb red
canθₖ-monotonic (nothing ∷ sigs) S' = canθₖ-monotonic sigs (suc S')
canθₖ-monotonic (just Signal.present ∷ sigs) S' θ
  = canθₖ-monotonic sigs (suc S') (θ ← _)
canθₖ-monotonic (just Signal.absent ∷ sigs) S' θ
  = canθₖ-monotonic sigs (suc S') (θ ← _)
canθₖ-monotonic (just Signal.unknown ∷ sigs) S' θ r r' cb red
  with any (_≟_ S') (Canθₛ sigs (suc S') r  (θ ← ([S]-env (S' ₛ))))
     | any (_≟_ S') (Canθₛ sigs (suc S') r' (θ ← ([S]-env (S' ₛ))))
... | yes S'∈Canr | yes S'∈Canr' = canθₖ-monotonic sigs (suc S') (θ ← [S]-env (S' ₛ)) r r' cb red
... | no  S'∉Canr | no  S'∉Canr' = canθₖ-monotonic sigs (suc S') (θ ← [S]-env-absent (S' ₛ)) r r' cb red
... | no  S'∉Canr | yes S'∈Canr'
  = ⊥-elim (S'∉Canr (canθₛ-monotonic sigs (suc S') (θ ← [S]-env (S' ₛ)) r r' cb red (S' ₛ) S'∈Canr'))
... | yes S'∈Canr | no  S'∉Canr'
   with (canθₖ-monotonic sigs (suc S') (θ ← [S]-env-absent (S' ₛ)) r r' cb red)
... | rec rewrite sym (Env.sig-set-clobber-single-as-← (S' ₛ) Signal.absent Signal.unknown θ (Env.sig-∈-single-right-← (S' ₛ) Signal.unknown θ))
  = λ k k∈ →  canθₖ-set-sig-monotonic sigs (suc S') r (S' ₛ) (θ ← [S]-env (S' ₛ))
                                      (Env.sig-∈-single-right-← (S' ₛ) Signal.unknown θ) Signal.absent
                                      (Env.sig-stats-1map-right-← (S' ₛ) Signal.unknown θ (Env.sig-∈-single-right-← (S' ₛ) Signal.unknown θ))
                                      (n∉map-suc-n-+ S' (SigM.Dom' sigs))
                                      k (rec k k∈)

canθₛ-monotonic [] S' cb red = canₛ-monotonic cb red
canθₛ-monotonic (nothing ∷ sigs) S' = canθₛ-monotonic sigs (suc S')
canθₛ-monotonic (just Signal.present ∷ sigs) S' θ
  = canθₛ-monotonic sigs (suc S') (θ ← _)
canθₛ-monotonic (just Signal.absent ∷ sigs) S' θ
  = canθₛ-monotonic sigs (suc S') (θ ← _)
canθₛ-monotonic (just Signal.unknown ∷ sigs) S' θ r r' cb red
  with any (_≟_ S') (Canθₛ sigs (suc S') r  (θ ← ([S]-env (S' ₛ))))
     | any (_≟_ S') (Canθₛ sigs (suc S') r' (θ ← ([S]-env (S' ₛ))))
... | yes S'∈Canr | yes S'∈Canr' = canθₛ-monotonic sigs (suc S') (θ ← [S]-env (S' ₛ)) r r' cb red
... | no  S'∉Canr | no  S'∉Canr' = canθₛ-monotonic sigs (suc S') (θ ← [S]-env-absent (S' ₛ)) r r' cb red
... | no  S'∉Canr | yes S'∈Canr'
  = ⊥-elim (S'∉Canr (canθₛ-monotonic sigs (suc S') (θ ← [S]-env (S' ₛ)) r r' cb red (S' ₛ) S'∈Canr'))
... | yes S'∈Canr | no  S'∉Canr'
   with (canθₛ-monotonic sigs (suc S') (θ ← [S]-env-absent (S' ₛ)) r r' cb red)
... | rec rewrite sym (Env.sig-set-clobber-single-as-← (S' ₛ) Signal.absent Signal.unknown θ (Env.sig-∈-single-right-← (S' ₛ) Signal.unknown θ))
  = λ k k∈ →  canθₛ-set-sig-monotonic sigs (suc S') r (S' ₛ) (θ ← [S]-env (S' ₛ))
                                      (Env.sig-∈-single-right-← (S' ₛ) Signal.unknown θ) Signal.absent
                                      (Env.sig-stats-1map-right-← (S' ₛ) Signal.unknown θ (Env.sig-∈-single-right-← (S' ₛ) Signal.unknown θ))
                                      (n∉map-suc-n-+ S' (SigM.Dom' sigs))
                                      (Signal.unwrap k) (rec k k∈)

canθₛₕ-monotonic [] S' cb red = canₛₕ-monotonic cb red
canθₛₕ-monotonic (nothing ∷ sigs) S' = canθₛₕ-monotonic sigs (suc S')
canθₛₕ-monotonic (just Signal.present ∷ sigs) S' θ
  = canθₛₕ-monotonic sigs (suc S') (θ ← _)
canθₛₕ-monotonic (just Signal.absent ∷ sigs) S' θ
  = canθₛₕ-monotonic sigs (suc S') (θ ← _)
canθₛₕ-monotonic (just Signal.unknown ∷ sigs) S' θ r r' cb red
  with any (_≟_ S') (Canθₛ sigs (suc S') r  (θ ← ([S]-env (S' ₛ))))
     | any (_≟_ S') (Canθₛ sigs (suc S') r' (θ ← ([S]-env (S' ₛ))))
... | yes S'∈Canr | yes S'∈Canr' = canθₛₕ-monotonic sigs (suc S') (θ ← [S]-env (S' ₛ)) r r' cb red
... | no  S'∉Canr | no  S'∉Canr' = canθₛₕ-monotonic sigs (suc S') (θ ← [S]-env-absent (S' ₛ)) r r' cb red
... | no  S'∉Canr | yes S'∈Canr'
  = ⊥-elim (S'∉Canr (canθₛ-monotonic sigs (suc S') (θ ← [S]-env (S' ₛ)) r r' cb red (S' ₛ) S'∈Canr'))
... | yes S'∈Canr | no  S'∉Canr'
   with (canθₛₕ-monotonic sigs (suc S') (θ ← [S]-env-absent (S' ₛ)) r r' cb red)
... | rec rewrite sym (Env.sig-set-clobber-single-as-← (S' ₛ) Signal.absent Signal.unknown θ (Env.sig-∈-single-right-← (S' ₛ) Signal.unknown θ))
  = λ k k∈ →  canθₛₕ-set-sig-monotonic sigs (suc S') r (S' ₛ) (θ ← [S]-env (S' ₛ))
                                      (Env.sig-∈-single-right-← (S' ₛ) Signal.unknown θ) Signal.absent
                                      (Env.sig-stats-1map-right-← (S' ₛ) Signal.unknown θ (Env.sig-∈-single-right-← (S' ₛ) Signal.unknown θ))
                                      (n∉map-suc-n-+ S' (SigM.Dom' sigs))
                                      (SharedVar.unwrap k) (rec k k∈)



canₖ-monotonic θ (p ∥ q) _ cb
  (rpar-done-right hnothin q/done) k k∈can-r'-θ =
  any-map⁺² {xs = Code.nothin ∷ []} (λ k' → map (Code._⊔_ k') (Canₖ q θ))
    (here refl) (any-map⁺ (Code._⊔_ Code.nothin) k∈can-r'-θ)
canₖ-monotonic θ (p ∥ q) _ cb
  (rpar-done-right (hexit n) (dhalted hnothin)) k k∈can-r'-θ =
  k∈can-r'-θ
canₖ-monotonic θ (p ∥ q) _ cb
  (rpar-done-right (hexit n) (dhalted (hexit m))) k k∈can-r'-θ =
  k∈can-r'-θ
canₖ-monotonic θ (p ∥ q) _ cb
  (rpar-done-right (hexit n) (dpaused q/paused)) k k∈can-r'-θ
  rewrite canₖ-paused θ q/paused
  = k∈can-r'-θ
canₖ-monotonic θ (p ∥ q) _ cb
  (rpar-done-left (dhalted hnothin) q/halted) k k∈can-r'-θ =
  any-map⁺² {xs = Code.nothin ∷ []} (λ k' → map (Code._⊔_ k') (Canₖ q θ))
    (here refl) (any-map⁺ (Code._⊔_ Code.nothin) k∈can-r'-θ)
canₖ-monotonic θ (p ∥ q) _ cb
  (rpar-done-left (dhalted (hexit n)) hnothin) k k∈can-r'-θ =
  k∈can-r'-θ
canₖ-monotonic θ (p ∥ q) _ cb
  (rpar-done-left (dhalted (hexit n)) (hexit m)) k k∈can-r'-θ =
  k∈can-r'-θ
canₖ-monotonic θ (p ∥ q) _ cb
  (rpar-done-left (dpaused p/paused) hnothin) k k∈can-r'-θ
  rewrite canₖ-paused θ p/paused =
  k∈can-r'-θ
canₖ-monotonic θ (p ∥ q) _ cb
  (rpar-done-left (dpaused p/paused) (hexit m)) k k∈can-r'-θ
  rewrite canₖ-paused θ p/paused =
  k∈can-r'-θ
canₖ-monotonic θ (ρ θ' · r) r' cb
  (ris-present {S = S} {p = p} {E = E} S∈ θ'S≡present r≐E⟦present⟧) k k∈can-r'-θ
  rewrite canθ-is-present (Env.sig θ') S∈ θ r≐E⟦present⟧  θ'S≡present 
  =   k∈can-r'-θ
canₖ-monotonic θ (ρ θ' · r) r' cb
  (ris-absent {S = S} S∈ θ'S≡absent r≐E⟦present⟧) k k∈can-r'-θ
  rewrite canθ-is-absent (Env.sig θ') S∈ θ r≐E⟦present⟧ θ'S≡absent
  =  k∈can-r'-θ 
canₖ-monotonic θ (ρ θ' · r) r' cb
  (remit {S = S} {E = E} S∈ θ'S≢absent r≐E⟦emit⟧) k k∈can-r'-θ
  = canθₖ-emit θ' S∈ θ r≐E⟦emit⟧ θ'S≢absent ((canθₛ-membership (Env.sig θ') 0 r θ S
                                                (λ θ* → canₛ-capture-emit-signal θ* r≐E⟦emit⟧)))
               k k∈can-r'-θ
canₖ-monotonic θ (loop r) r' cb rloop-unroll k k∈can-r'-θ = k∈can-r'-θ
canₖ-monotonic θ .(nothin >> r') r' cb
  rseq-done k k∈can-r'-θ = k∈can-r'-θ
canₖ-monotonic θ .(exit _ >> _) .(exit _) cb
  rseq-exit k k∈can-r'-θ = k∈can-r'-θ
canₖ-monotonic θ .(loopˢ (exit _)  _) .(exit _) cb
  rloopˢ-exit k k∈can-r'-θ = k∈can-r'-θ
canₖ-monotonic θ (suspend r S) .r cb
  (rsuspend-done r/halted) k k∈can-r'-θ = k∈can-r'-θ
canₖ-monotonic θ (trap r) .nothin   cb
  (rtrap-done hnothin) k k∈can-r'-θ = k∈can-r'-θ
canₖ-monotonic θ (trap r) .nothin   cb
  (rtrap-done (hexit zero)) k k∈can-r'-θ = k∈can-r'-θ
canₖ-monotonic θ (trap r) .(exit n) cb
  (rtrap-done (hexit (suc n))) k k∈can-r'-θ = k∈can-r'-θ
canₖ-monotonic θ (signl S r) r' cb
  rraise-signal k k∈can-r'-θ = k∈can-r'-θ
canₖ-monotonic θ (ρ θ' · r) r' cb
  (rraise-shared {s = s} {e = e} {p = p} {E = E} e' r≐E⟦shared⟧) k k∈can-r'-θ
  rewrite sym (unplug r≐E⟦shared⟧)
        | sym (canθₖ-raise-lemma (Env.sig θ') 0 θ E (tshared (δ e') s e p))
  =   k∈can-r'-θ  
canₖ-monotonic θ (ρ θ' · r) r' cb
  (rset-shared-value-old {s = s} {e = e} {E = E} e' s∈ θ's≡old r≐E⟦s⇐e⟧) k k∈can-r'-θ
  rewrite canθ-shr-var-irr (Env.sig (Env.set-shr {s} θ' s∈ SharedVar.new (δ e'))) 0 r θ θ refl
        | sym (unplug r≐E⟦s⇐e⟧)
  =   canθₖ-term-nothin-lemma
      (Env.sig (Env.set-shr {s} θ' s∈ SharedVar.new (δ e')))
      0
      θ
      E (tset-shr s e) k k∈can-r'-θ 
canₖ-monotonic θ (ρ θ' · r) r' cb
  (rset-shared-value-new {s = s} {e = e} {E = E} e' s∈ θ's≡new r≐E⟦s⇐e⟧) k k∈can-r'-θ
  rewrite canθ-shr-var-irr (Env.sig (Env.set-shr {s} θ' s∈ SharedVar.new (Env.shr-vals {s} θ' s∈ + δ e')))
                           0 r θ θ refl
        | sym (unplug r≐E⟦s⇐e⟧)
  = canθₖ-term-nothin-lemma
      (Env.sig (Env.set-shr {s} θ' s∈ SharedVar.new (Env.shr-vals {s} θ' s∈ + δ e')))
      0
      θ
      E (tset-shr s e) k k∈can-r'-θ 
canₖ-monotonic θ (ρ θ' · r) r' cb
  (rraise-var {x = x} {p = p} {e = e} {E = E} e' r≐E⟦var⟧) k k∈can-r'-θ
  rewrite sym (unplug r≐E⟦var⟧)
        | (canθₖ-raise-lemma (Env.sig θ') 0 θ E (tvar (δ e') x e p))
  =  k∈can-r'-θ 
canₖ-monotonic θ (ρ θ' · r) r' cb
  (rset-var {x = x} {e = e} {E = E} x∈ e' r≐E⟦x≔e⟧) k k∈can-r'-θ
  rewrite canθ-shr-var-irr (Env.sig (Env.set-var {x} θ' x∈ (δ e'))) 0 r θ θ refl
        | sym (unplug r≐E⟦x≔e⟧)
  =  canθₖ-term-nothin-lemma
      (Env.sig (Env.set-var {x} θ' x∈ (δ e')))
      0
      θ
      E (tset-var x e) k k∈can-r'-θ 
canₖ-monotonic θ (ρ θ' · r) r' cb
  (rif-false {p = p} {q = q} {x = x} {E = E} x∈ θ'x≡zero r≐E⟦if⟧) k k∈can-r'-θ
  rewrite sym (unplug r≐E⟦if⟧)
  =  canθₖ-if-false-lemma (Env.sig θ' ) 0 x p q θ E k k∈can-r'-θ 
canₖ-monotonic θ (ρ θ' · r) r' cb
  (rif-true {p = p} {q = q} {x = x} {E = E} x∈ θ'x≡suc r≐E⟦if⟧) k k∈can-r'-θ
  rewrite sym (unplug r≐E⟦if⟧)
  =  canθₖ-if-true-lemma (Env.sig θ') 0 x p q θ E k k∈can-r'-θ 
canₖ-monotonic θ (ρ θ' · r) r' cb
  (rabsence {S = S} S∈ θ'S≡unknown S∉can-r-θ') k k∈can-r'-θ
  rewrite Env.sig-switch-right S Signal.absent θ θ' S∈ (Env.sig-←-monoʳ S θ' θ S∈)
  = canθₖ-set-sig-monotonic-absence-lemma (Env.sig θ') 0 r S θ  S∈
      θ'S≡unknown k k∈can-r'-θ 
  where
    θ←θ'        = θ ← θ'
    S∈Domθ←θ'   = Env.sig-←-monoʳ S θ' θ S∈
    ⟨θ←θ'⟩S≡θ'S = Env.sig-stats-←-right-irr' S θ θ' S∈ S∈Domθ←θ'
canₖ-monotonic θ (ρ θ' · r) r' cb
  (rreadyness {s = s} s∈ θ's≡old⊎θ's≡new s∉can-r-θ') k k∈can-r'-θ
  rewrite can-shr-var-irr r (θ ← θ')
            (θ ← Env.set-shr {s} θ' s∈ SharedVar.ready (Env.shr-vals {s} θ' s∈)) refl
  = k∈can-r'-θ
canₖ-monotonic θ (ρ θ' · r) r' cb@(CBρ cb')
  (rmerge {θ₁ = .θ'} {θ₂ = θ''} {p = rin} {E = E} r≐E⟦ρθ''·rin⟧) k k∈can-r'-θ
  = canθₖ-mergeˡ (Env.sig θ') θ cb' r≐E⟦ρθ''·rin⟧ k k∈can-r'-θ


canₛ-monotonic θ (p ∥ q) _ cb
  (rpar-done-right p/halted q/done) S' S'∈can-r'-θ
  rewrite canₛ-done θ (value-max-done (dhalted p/halted) q/done (inj₁ p/halted))
  with S'∈can-r'-θ
... | ()
canₛ-monotonic θ (p ∥ q) _ cb
  (rpar-done-left p/done q/halted) S' S'∈can-r'-θ
  rewrite canₛ-done θ (value-max-done p/done (dhalted q/halted) (inj₂ q/halted))
  with S'∈can-r'-θ
... | ()
canₛ-monotonic θ (ρ θ' · r) r' cb
  (ris-present {S = S} S∈ θ'S≡present r≐E⟦present⟧) S' S'∈can-r'-θ
    rewrite canθ-is-present (Env.sig θ') S∈ θ r≐E⟦present⟧  θ'S≡present 
  =  S'∈can-r'-θ 
canₛ-monotonic θ (ρ θ' · r) r' cb
  (ris-absent {S = S} S∈ θ'S≡absent r≐E⟦absent⟧) S' S'∈can-r'-θ
    rewrite canθ-is-absent (Env.sig θ') S∈ θ r≐E⟦absent⟧  θ'S≡absent
  =  S'∈can-r'-θ 
canₛ-monotonic θ (ρ θ' · r) (ρ θ'' · r') cb
  (remit {S = S} {E = E} S∈ θ'S≢absent r≐E⟦emit⟧) S' S'∈can-ρθ''·r'-θ
  with set-subtract-merge
         {xs = Canθₛ (Env.sig (Env.set-sig {S} θ' S∈ Signal.present)) 0 r' θ}
         {ys = proj₁ (Dom θ'')}
         S'∈can-ρθ''·r'-θ
... | S'∈can-r'-θ←θ'' , S'∉Domθ''
  with set-subtract-split {ys = proj₁ (Dom θ')}
         (canθₛ-emit θ' S∈ θ r≐E⟦emit⟧ θ'S≢absent
           (canθₛ-membership (Env.sig θ') 0 r θ S
               (λ θ* → canₛ-capture-emit-signal θ* r≐E⟦emit⟧))
           S' S'∈can-r'-θ←θ'')
... | inj₁ S'∈can-r-θ←θ'-θ' = S'∈can-r-θ←θ'-θ'
... | inj₂ S'∈Domθ' =
  ⊥-elim (S'∉Domθ'' (Env.sig-set-mono' {S'} {S} {θ'} {Signal.present} {S∈} S'∈Domθ'))
canₛ-monotonic θ (loop r) r' cb rloop-unroll S' S'∈can-r'-θ = S'∈can-r'-θ
canₛ-monotonic θ .(nothin >> r') r' cb
  rseq-done S' S'∈can-r'-θ = S'∈can-r'-θ
canₛ-monotonic θ .(exit _ >> _) .(exit _) cb
  rseq-exit S' S'∈can-r'-θ = S'∈can-r'-θ
canₛ-monotonic θ .(loopˢ (exit _) _) .(exit _) cb
  rloopˢ-exit S' S'∈can-r'-θ = S'∈can-r'-θ
canₛ-monotonic θ (suspend r S) .r cb
  (rsuspend-done r/halted) S' S'∈can-r'-θ
  rewrite canₛ-done θ (dhalted r/halted) with S'∈can-r'-θ
... | ()
canₛ-monotonic θ (trap r) r' cb
  (rtrap-done r/halted) S' S'∈can-r'-θ
  rewrite canₛ-done θ (dhalted (↓-well-behaved _ r/halted)) with S'∈can-r'-θ
... | ()
canₛ-monotonic θ (signl S r) r' cb
  rraise-signal S' S'∈can-r'-θ
  rewrite SigMap.keys-1map S Signal.unknown
        | set-subtract-[a]≡set-remove (Canθₛ (Env.sig ([S]-env S)) 0 r θ) (Signal.unwrap S)
  =  S'∈can-r'-θ 
canₛ-monotonic θ (ρ θ' · r) (ρ .θ' · r') cb
  (rraise-shared {s = s} {e = e} {p = p} {E = E} e' r≐E⟦shared⟧) S' S'∈can-ρθ'·r'-θ
    rewrite sym (unplug r≐E⟦shared⟧)
          | sym (canθₛ-raise-lemma (Env.sig θ') 0 θ E (tshared (δ e') s e p))
    =  S'∈can-ρθ'·r'-θ 

canₛ-monotonic θ (ρ θ' · r) (ρ θ'' · r') cb
  (rset-shared-value-old{s = s}{e = e}{E = E} e' s∈ θ's≡old r≐E⟦s⇐e⟧) S' S'∈can-ρθ''·r'-θ
  with set-subtract-merge{xs = Canθₛ (Env.sig θ'') 0 r' θ}{ys = proj₁ (Dom θ'')} S'∈can-ρθ''·r'-θ
... | S'∈can-r'-θ←θ'' , S'∉Domθ''
  with set-subtract-split {xs = Canθₛ (Env.sig θ') 0 r θ} {ys = proj₁ (Dom θ')} {z = Signal.unwrap S'}
         (subst
            (λ x → _ ∈ Canθₛ (Env.sig θ') 0 x θ)
            (unplug r≐E⟦s⇐e⟧)
            (canθₛ-term-nothin-lemma (Env.sig θ'') 0 θ E (tset-shr s e)
                              (Signal.unwrap S')  S'∈can-r'-θ←θ'' )  )
... | inj₁ S'∈can-r-θ←θ'-θ' = S'∈can-r-θ←θ'-θ' -- θ' and θ'' differ only by shared var Dom
... | inj₂ S'∈Domθ' = ⊥-elim (S'∉Domθ'' S'∈Domθ')
canₛ-monotonic θ (ρ θ' · r) (ρ θ'' · r') cb
  (rset-shared-value-new{s = s}{e = e}{E = E} e' s∈ θ's≡new r≐E⟦s⇐e⟧) S' S'∈can-ρθ''·r'-θ
  with set-subtract-merge{xs = Canθₛ (Env.sig θ'') 0 r' θ}{ys = proj₁ (Dom θ'')} S'∈can-ρθ''·r'-θ
... | S'∈can-r'-θ←θ'' , S'∉Domθ''
  with set-subtract-split {xs = Canθₛ (Env.sig θ') 0 r θ} {ys = proj₁ (Dom θ')} {z = Signal.unwrap S'}
         (subst
            (λ x → _ ∈ Canθₛ (Env.sig θ') 0 x θ)
            (unplug r≐E⟦s⇐e⟧)
            (canθₛ-term-nothin-lemma (Env.sig θ'') 0 θ E (tset-shr s e)
                              (Signal.unwrap S')  S'∈can-r'-θ←θ'' )) 
... | inj₁ S'∈can-r-θ←θ'-θ' = S'∈can-r-θ←θ'-θ'
... | inj₂ S'∈Domθ' = ⊥-elim (S'∉Domθ'' S'∈Domθ')
canₛ-monotonic θ (ρ θ' · r) (ρ .θ' · r') cb
  (rraise-var {x = x} {p = p} {e = e} {E = E} e' r≐E⟦var⟧) S' S'∈can-ρθ'·r'-θ
  rewrite sym (canθₛ-raise-lemma (Env.sig θ') 0 θ E (tvar (δ e') x e p)) | (unplug r≐E⟦var⟧) = S'∈can-ρθ'·r'-θ
canₛ-monotonic θ (ρ θ' · r) (ρ θ'' · r') cb
  (rset-var {x = x} {e = e} {E = E}  x∈ e' r≐E⟦x≔e⟧) S' S'∈can-ρθ''·r'-θ
  with set-subtract-merge {xs = Canθₛ (Env.sig θ'') 0 r' θ}{ys = proj₁ (Dom θ'')} S'∈can-ρθ''·r'-θ
... | S'∈can-r'-θ←θ'' , S'∉Domθ''
  with set-subtract-split {xs = Canθₛ (Env.sig θ') 0 r θ} {ys = proj₁ (Dom θ')}{z = Signal.unwrap S'}
         ( (subst
            (λ x → _ ∈ Canθₛ (Env.sig θ') 0 x θ)
            (unplug r≐E⟦x≔e⟧)
            (canθₛ-term-nothin-lemma (Env.sig θ'') 0 θ E (tset-var x e)
                              (Signal.unwrap S')  S'∈can-r'-θ←θ'' )) )
... | inj₁ S'∈can-r-θ←θ'-θ' = S'∈can-r-θ←θ'-θ' -- θ' and θ'' differ only by seq var Dom
... | inj₂ S'∈Domθ' = ⊥-elim (S'∉Domθ'' S'∈Domθ')
canₛ-monotonic θ (ρ θ' · r) (ρ .θ' · r') cb
  (rif-false {p = p} {q = q} {x = x} {E = E} x∈ θ'x≡zero r≐E⟦if⟧) S' S'∈can-ρθ'·r'-θ
    with set-subtract-merge{xs = (proj₁ (Canθ (Env.sig θ') 0 r' θ))} {ys = proj₁ (Dom θ')}{z = (Signal.unwrap S')} S'∈can-ρθ'·r'-θ
... | S'∈can-r'-θ←θ' , S'∉Domθ' rewrite sym (unplug r≐E⟦if⟧) =
  set-subtract-notin (canθₛ-if-false-lemma (Env.sig θ') 0 x p q θ E (Signal.unwrap S')  S'∈can-r'-θ←θ') S'∉Domθ'
canₛ-monotonic θ (ρ θ' · r) (ρ .θ' · r') cb
  (rif-true {p = p} {q = q} {x = x} {E = E} x∈ θ'x≡suc r≐E⟦if⟧) S' S'∈can-ρθ'·r'-θ
    with set-subtract-merge{xs = (proj₁ (Canθ (Env.sig θ') 0 r' θ))} {ys = proj₁ (Dom θ')}{z = (Signal.unwrap S')} S'∈can-ρθ'·r'-θ
... | S'∈can-r'-θ←θ' , S'∉Domθ' rewrite sym (unplug r≐E⟦if⟧) =
  set-subtract-notin (canθₛ-if-true-lemma (Env.sig θ') 0 x p q θ E (Signal.unwrap S')  S'∈can-r'-θ←θ') S'∉Domθ'
canₛ-monotonic θ (ρ θ' · r) (ρ θ'' · .r) cb
  (rabsence {S = S} S∈ θ'S≡unknown S∉can-r-θ') S' S'∈can-ρθ''·r-θ
  rewrite Env.sig-switch-right S Signal.absent θ θ' S∈ (Env.sig-←-monoʳ S θ' θ S∈)
  with set-subtract-merge{xs = Canθₛ (Env.sig θ'') 0 r θ } {ys = proj₁ (Dom θ'')} S'∈can-ρθ''·r-θ
... | S'∈can-r-θ←θ'' , S'∉Domθ''
  with set-subtract-split{xs = (Canθₛ (Env.sig θ') 0 r θ)}{ys = fst (Dom θ')}
         (canθₛ-set-sig-monotonic-absence-lemma (Env.sig θ') 0 r S θ S∈
           θ'S≡unknown (Signal.unwrap S') S'∈can-r-θ←θ'')
  where
    θ←θ'        = θ ← θ'
    S∈Domθ←θ'   = Env.sig-←-monoʳ S θ' θ S∈
    ⟨θ←θ'⟩S≡θ'S = Env.sig-stats-←-right-irr' S θ θ' S∈ S∈Domθ←θ'
... | inj₁ S'∈can-r-θ←θ'-θ' = S'∈can-r-θ←θ'-θ'
... | inj₂ S'∈Domθ' =
  ⊥-elim
    (S'∉Domθ''
      (Env.sig-set-mono' {S'} {S} {θ'} {Signal.absent} {S∈}
        S'∈Domθ'))
canₛ-monotonic θ (ρ θ' · r) r' cb
  (rreadyness {s = s} s∈ θ's≡old⊎θ's≡new s∉can-r-θ') S' S'∈can-r'-θ
  = S'∈can-r'-θ
canₛ-monotonic θ (ρ θ' · r) (ρ .(θ' ← θ'') · r') cb@(CBρ cb')
  (rmerge {θ₁ = .θ'} {θ₂ = θ''} {p = rin} {E = E} r≐E⟦ρθ''·rin⟧) S' S'∈can-ρθ'←θ''·r'-θ
  with set-subtract-merge
         {xs = Canθₛ (Env.sig (θ' ← θ'')) 0 r' θ}
         {ys = proj₁ (Dom (θ' ← θ''))}
         S'∈can-ρθ'←θ''·r'-θ
... | S'∈can-r'-θ←θ'←θ'' , S'∉Domθ'←θ''
  = set-subtract-notin
      (canθₛ-mergeˡ (Env.sig θ') θ cb' r≐E⟦ρθ''·rin⟧
        S' (S'∉Domθ'←θ'' ∘ Env.sig-←-monoʳ S' θ'' θ') S'∈can-r'-θ←θ'←θ'')
      (S'∉Domθ'←θ'' ∘ Env.sig-←-monoˡ S' θ' θ'')


canₛₕ-monotonic θ (p ∥ q) _ cb
  (rpar-done-right p/halted q/done) s' s'∈can-r'-θ
  rewrite canₛₕ-done θ (value-max-done (dhalted p/halted) q/done (inj₁ p/halted))
  with s'∈can-r'-θ
... | ()
canₛₕ-monotonic θ (p ∥ q) _ cb
  (rpar-done-left p/done q/halted) s' s'∈can-r'-θ
  rewrite canₛₕ-done θ (value-max-done p/done (dhalted q/halted) (inj₂ q/halted))
  with s'∈can-r'-θ
... | ()
canₛₕ-monotonic θ (ρ θ' · r) r' cb
  (ris-present {S = S} S∈ θ'S≡present r≐E⟦present⟧) s' s'∈can-r'-θ
  rewrite canθ-is-present (Env.sig θ') S∈ θ r≐E⟦present⟧ θ'S≡present
  =  s'∈can-r'-θ 
canₛₕ-monotonic θ (ρ θ' · r) r' cb
  (ris-absent {S = S} S∈ θ'S≡absent r≐E⟦present⟧) s' s'∈can-r'-θ
  rewrite canθ-is-absent (Env.sig θ') S∈ θ r≐E⟦present⟧ θ'S≡absent
  =  s'∈can-r'-θ 
canₛₕ-monotonic θ (ρ θ' · r) (ρ θ'' · r') cb
  (remit {S = S} {E = E} S∈ θ'S≢absent r≐E⟦emit⟧) s' s'∈can-ρθ''·r'-θ
  with set-subtract-merge
         {xs = Canθₛₕ (Env.sig (Env.set-sig {S} θ' S∈ Signal.present)) 0 r' θ}
         {ys = proj₁ (proj₂ (Dom θ''))}
         s'∈can-ρθ''·r'-θ
... | s'∈can-r'-θ←θ'' , s'∉Domθ''
  with set-subtract-split {ys = proj₁ (proj₂ (Dom θ'))}
         (canθₛₕ-emit θ' S∈ θ r≐E⟦emit⟧ θ'S≢absent
           (canθₛ-membership (Env.sig θ') 0 r θ S
             (λ θ* → canₛ-capture-emit-signal θ* r≐E⟦emit⟧))
           s' s'∈can-r'-θ←θ'')
... | inj₁ s'∈can-r-θ←θ'-θ' = s'∈can-r-θ←θ'-θ'
... | inj₂ s'∈Domθ' = ⊥-elim (s'∉Domθ'' s'∈Domθ') -- θ' and θ'' differ only by sig
canₛₕ-monotonic θ (loop r) r' cb rloop-unroll s' s'∈can-r'-θ = s'∈can-r'-θ
canₛₕ-monotonic θ .(nothin >> r') r' cb
  rseq-done s' s'∈can-r'-θ = s'∈can-r'-θ
canₛₕ-monotonic θ .(exit _ >> _) .(exit _) cb
  rseq-exit s' s'∈can-r'-θ = s'∈can-r'-θ
canₛₕ-monotonic θ .(loopˢ (exit _) _) .(exit _) cb
  rloopˢ-exit s' s'∈can-r'-θ = s'∈can-r'-θ
canₛₕ-monotonic θ (suspend r S) .r cb
  (rsuspend-done r/halted) s' s'∈can-r'-θ
  rewrite canₛₕ-done θ (dhalted r/halted) with s'∈can-r'-θ
... | ()
canₛₕ-monotonic θ (trap r) r' cb
  (rtrap-done r/halted) s' s'∈can-r'-θ
  rewrite canₛₕ-done θ (dhalted (↓-well-behaved _ r/halted)) with s'∈can-r'-θ
... | ()
canₛₕ-monotonic θ (signl S r) r' cb
  rraise-signal s' s'∈can-r'-θ
  rewrite set-subtract-[] (Canθₛₕ (Env.sig ([S]-env S)) 0 r θ)
  =  s'∈can-r'-θ 
canₛₕ-monotonic θ (ρ θ' · r) (ρ .θ' · r') cb
  (rraise-shared {s = s} {e = e} {p = p} {E = E} e' r≐E⟦shared⟧) s' s'∈can-ρθ'·r'-θ
  with set-subtract-merge {ys = proj₁ (proj₂ (Dom θ'))} s'∈can-ρθ'·r'-θ
... | s'∈can-r'-θ←θ' , s'∉Domθ' =
  
  set-subtract-notin
    (canθₛₕ-subset (Env.sig θ') 0 (E ⟦ ρ [s,δe]-env s (δ e') · p ⟧e) r
       θ (λ θ* S* → canₛ-raise θ* (tshared (δ e') s e p) r≐E⟦shared⟧ S*)
       (λ θ* s* → canₛₕ-raise θ* (tshared (δ e') s e p) r≐E⟦shared⟧ s*) s'
       s'∈can-r'-θ←θ')
    s'∉Domθ'


canₛₕ-monotonic θ (ρ θ' · r) (ρ θ'' · r') cb
  (rset-shared-value-old {s = s} {e = e} {E = E} e' s∈ θ's≡old r≐E⟦s⇐e⟧) s' s'∈can-ρθ''·r'-θ
  with set-subtract-merge {ys = proj₁ (proj₂ (Dom θ''))} s'∈can-ρθ''·r'-θ
... | s'∈can-r'-θ←θ'' , s'∉Domθ''
  with set-subtract-split {ys = proj₁ (proj₂ (Dom θ'))}
         (canθₛₕ-subset (Env.sig θ') 0 (E ⟦ nothin ⟧e) r θ
           (λ θ* S* → canₛ-term-nothin θ* θ* refl (tset-shr s e) r≐E⟦s⇐e⟧ S*)
           (λ θ* s* → canₛₕ-term-nothin θ* θ* refl (tset-shr s e) r≐E⟦s⇐e⟧ s*)
           s' s'∈can-r'-θ←θ'')
... | inj₁ s'∈can-r-θ←θ'-θ' = s'∈can-r-θ←θ'-θ'
... | inj₂ s'∈Domθ' =
  ⊥-elim
    (s'∉Domθ''
      (Env.shr-set-mono' {s'} {s} {θ'} {SharedVar.new} {δ e'} {s∈}
        s'∈Domθ'))
canₛₕ-monotonic θ (ρ θ' · r) (ρ θ'' · r') cb
  (rset-shared-value-new {s = s} {e = e} {E = E} e' s∈ θ's≡new r≐E⟦s⇐e⟧) s' s'∈can-ρθ''·r'-θ
  with set-subtract-merge {ys = proj₁ (proj₂ (Dom θ''))} s'∈can-ρθ''·r'-θ
... | s'∈can-r'-θ←θ'' , s'∉Domθ''
  with set-subtract-split {ys = proj₁ (proj₂ (Dom θ'))}
         (canθₛₕ-subset (Env.sig θ') 0 (E ⟦ nothin ⟧e) r θ
           (λ θ* S* → canₛ-term-nothin θ* θ* refl (tset-shr s e) r≐E⟦s⇐e⟧ S*)
           (λ θ* s* → canₛₕ-term-nothin θ* θ* refl (tset-shr s e) r≐E⟦s⇐e⟧ s*)
           s' s'∈can-r'-θ←θ'')
... | inj₁ s'∈can-r-θ←θ'-θ' = s'∈can-r-θ←θ'-θ'
... | inj₂ s'∈Domθ' =
  ⊥-elim
    (s'∉Domθ''
      (Env.shr-set-mono' {s'} {s} {θ'} {SharedVar.new}
        {Env.shr-vals {s} θ' s∈ + δ e'} {s∈}
        s'∈Domθ'))
canₛₕ-monotonic θ (ρ θ' · r) (ρ .θ' · r') cb
  (rraise-var {x = x} {p = p} {e = e} {E = E} e' r≐E⟦var⟧) s' s'∈can-ρθ'·r'-θ
  with set-subtract-merge {ys = proj₁ (proj₂ (Dom θ'))} s'∈can-ρθ'·r'-θ
... | s'∈can-r'-θ←θ' , s'∉Domθ' =
  set-subtract-notin
    (canθₛₕ-subset (Env.sig θ') 0 (E ⟦ ρ [x,δe]-env x (δ e') · p ⟧e) r θ
      (λ θ* S* → canₛ-raise θ* (tvar (δ e') x e p) r≐E⟦var⟧ S*)
      (λ θ* s* → canₛₕ-raise θ* (tvar (δ e') x e p) r≐E⟦var⟧ s*)
      s' s'∈can-r'-θ←θ')
    s'∉Domθ'
canₛₕ-monotonic θ (ρ θ' · r) (ρ θ'' · r') cb
  (rset-var {x = x} {e = e} {E = E} x∈ e' r≐E⟦x≔e⟧) s' s'∈can-ρθ''·r'-θ
  with set-subtract-merge {ys = proj₁ (proj₂ (Dom θ''))} s'∈can-ρθ''·r'-θ
... | s'∈can-r'-θ←θ'' , s'∉Domθ''
  with set-subtract-split {ys = proj₁ (proj₂ (Dom θ'))}
         (canθₛₕ-subset (Env.sig θ') 0 (E ⟦ nothin ⟧e) r θ
           (λ θ* S* → canₛ-term-nothin θ* θ* refl (tset-var x e) r≐E⟦x≔e⟧ S*)
           (λ θ* s* → canₛₕ-term-nothin θ* θ* refl (tset-var x e) r≐E⟦x≔e⟧ s*)
           s' s'∈can-r'-θ←θ'')
... | inj₁ s'∈can-r-θ←θ'-θ' = s'∈can-r-θ←θ'-θ' -- θ' and θ'' differ only by seq var Dom
... | inj₂ s'∈Domθ' = ⊥-elim (s'∉Domθ'' s'∈Domθ')
canₛₕ-monotonic θ (ρ θ' · r) (ρ .θ' · r') cb
  (rif-false {p = p} {q = q} {x = x} {E = E} x∈ θ'x≡zero r≐E⟦if⟧) s' s'∈can-ρθ'·r'-θ
  with set-subtract-merge{xs = (thd (Canθ (Env.sig θ') 0 r' θ))} {ys = snd (Dom θ')}{z = (SharedVar.unwrap s')} s'∈can-ρθ'·r'-θ
... |  s'∈can-r'-θ←θ' , s'∉Domθ'
    rewrite sym (unplug r≐E⟦if⟧)
  = set-subtract-notin
      (canθₛₕ-if-false-lemma (Env.sig θ' ) 0 x p q θ E (SharedVar.unwrap s')   s'∈can-r'-θ←θ' )
      s'∉Domθ'
canₛₕ-monotonic θ (ρ θ' · r) (ρ .θ' · r') cb
  (rif-true {p = p} {q = q} {x = x} {E = E} x∈ θ'x≡suc r≐E⟦if⟧) s' s'∈can-ρθ'·r'-θ
    with set-subtract-merge{xs = (thd (Canθ (Env.sig θ') 0 r' θ))} {ys = snd (Dom θ')}{z = (SharedVar.unwrap s')} s'∈can-ρθ'·r'-θ
... |  s'∈can-r'-θ←θ' , s'∉Domθ'
    rewrite sym (unplug r≐E⟦if⟧)
  = set-subtract-notin
      (canθₛₕ-if-true-lemma (Env.sig θ' ) 0 x p q θ E (SharedVar.unwrap s')   s'∈can-r'-θ←θ' )
      s'∉Domθ'
canₛₕ-monotonic θ (ρ θ' · r) (ρ θ'' · .r) cb
  (rabsence {S = S} S∈ θ'S≡unknown S∉can-r-θ') s' s'∈can-ρθ''·r-θ
  rewrite Env.sig-switch-right S Signal.absent θ θ' S∈ (Env.sig-←-monoʳ S θ' θ S∈)
 with set-subtract-merge {xs = Canθₛₕ (Env.sig θ'') 0 r θ }{ys = proj₁ (proj₂ (Dom θ''))} s'∈can-ρθ''·r-θ
... | s'∈can-r-θ←θ'' , s'∉Domθ''
  with set-subtract-split
         (canθₛₕ-set-sig-monotonic-absence-lemma (Env.sig θ') 0 r S θ S∈
            θ'S≡unknown (SharedVar.unwrap s') s'∈can-r-θ←θ'')
  where
    θ←θ'        = θ ← θ'
    S∈Domθ←θ'   = Env.sig-←-monoʳ S θ' θ S∈
    ⟨θ←θ'⟩S≡θ'S = Env.sig-stats-←-right-irr' S θ θ' S∈ S∈Domθ←θ'
... | inj₁ s'∈can-r-θ←θ'-θ' = s'∈can-r-θ←θ'-θ'
... | inj₂ s'∈Domθ' = ⊥-elim (s'∉Domθ'' s'∈Domθ') -- θ' and θ'' differ only by sig 
canₛₕ-monotonic θ (ρ θ' · r) r' cb
  (rreadyness {s = s} s∈ θ's≡old⊎θ's≡new s∉can-r-θ') s' s'∈can-r'-θ
  rewrite cong (proj₁ ∘ proj₂)
            (Env.shr-set-dom-eq s SharedVar.ready (Env.shr-vals {s} θ' s∈) θ' s∈)
        | can-shr-var-irr r (θ ← θ')
            (θ ← Env.set-shr {s} θ' s∈ SharedVar.ready (Env.shr-vals {s} θ' s∈)) refl
  = s'∈can-r'-θ
canₛₕ-monotonic θ (ρ θ' · r) (ρ .(θ' ← θ'') · r') cb@(CBρ cb')
  (rmerge {θ₁ = .θ'} {θ₂ = θ''} {p = rin} {E = E} r≐E⟦ρθ''·rin⟧) s' s'∈can-ρθ'←θ''·r'-θ
  with set-subtract-merge
         {xs = Canθₛₕ (Env.sig (θ' ← θ'')) 0 r' θ}
         {ys = proj₁ (proj₂ (Dom (θ' ← θ'')))}
         s'∈can-ρθ'←θ''·r'-θ
 -- rewrite Env.←-assoc θ θ' θ''
... | s'∈can-r'-θ←θ'←θ'' , s'∉Domθ'←θ'' =
  set-subtract-notin
    (canθₛₕ-mergeˡ (Env.sig θ') θ cb' r≐E⟦ρθ''·rin⟧
      s' (s'∉Domθ'←θ'' ∘ Env.shr-←-monoʳ s' θ'' θ')
      s'∈can-r'-θ←θ'←θ'')
    (s'∉Domθ'←θ'' ∘ Env.shr-←-monoˡ s' θ' θ'')



infix 4 _⊑₃_
_⊑₃_ : SigSet.ST × CodeSet.ST × ShrSet.ST -> SigSet.ST × CodeSet.ST × ShrSet.ST -> Set
_⊑₃_ (Ss , ks , ss)  (Ss' , ks' , ss') =
  ((∀ S → (Signal.unwrap S) ∈ Ss → (Signal.unwrap S) ∈ Ss') ×
   (∀ k → k ∈ ks → k ∈ ks') ×
   (∀ s → (SharedVar.unwrap s) ∈ ss → (SharedVar.unwrap s) ∈ ss'))

can-antimonotonic :
  ∀ θ p q →
    CB p →
    p sn⟶₁ q →
  Can q θ ⊑₃ Can p θ
can-antimonotonic θ r r' CBr rsn⟶₁r' =
  (canₛ-monotonic  θ r r' CBr rsn⟶₁r' ,′
   canₖ-monotonic  θ r r' CBr rsn⟶₁r' ,′
   canₛₕ-monotonic  θ r r' CBr rsn⟶₁r')

