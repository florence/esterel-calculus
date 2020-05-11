module Esterel.Lang.Properties where

open import Esterel.Lang
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Esterel.Environment
open import Esterel.Variable.Signal as Signal
open import Esterel.Variable.Shared as SharedVar
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Context.Properties

open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.Nat
  using (ℕ ; zero ; suc) renaming (_⊔_ to _⊔ℕ_)
open import Data.MoreNatProp
  using (⊔-sym)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; _,′_ ; proj₁ ; proj₂ ; _×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Data.List
open import Data.Maybe
open import Data.List.Any
open import Data.List.All
open import Data.OrderedListMap
open import Function using (_$_) 

import Data.OrderedListMap(Signal)(Signal.unwrap)(Signal.Status) as SigOMap
import Data.OrderedListMap(SharedVar)(SharedVar.unwrap)(SharedVar.Status × ℕ) as ShrOMap

open ≡-Reasoning using (begin_ ; _≡⟨_⟩_ ; _∎)

open EvaluationContext1
open _≐_⟦_⟧e
open Context1
open _≐_⟦_⟧c

data halted : Term → Set where
  hnothin :           halted nothin
  hexit   : (n : ℕ) → halted (exit n)

data paused : Term → Set where
  ppause   :                     paused pause
  pseq     : ∀{p q} → paused p → paused (p >> q)
  ploopˢ   : ∀{p q} → paused p → paused (loopˢ p q)
  ppar     : ∀{p q} → paused p → paused q → paused (p ∥ q)
  psuspend : ∀{p S} → paused p → paused (suspend p S)
  ptrap    : ∀{p}   → paused p → paused (trap p)

data done : Term → Set where
  dhalted : ∀{p} → (p/halted : halted p) → done p
  dpaused : ∀{p} → (p/paused : paused p) → done p

data complete-θ : Env → Set where
  θcomplete : ∀{θ} →
                (∀ S → (S∈ : isSig∈ S θ) → ((sig-stats{S} θ S∈ ≡ Signal.absent) ⊎ (sig-stats{S} θ S∈ ≡ Signal.present))) →
                (∀ s → (s∈ : isShr∈ s θ) → (shr-stats{s} θ s∈ ≡ SharedVar.ready)) →
                ---------------
                complete-θ θ

data complete : Term → Set where
  codone : ∀{p} → done p → complete p
  coenv : ∀{θ A p} → complete-θ θ → done p → complete (ρ⟨ θ , A ⟩· p)

-- Halted and paused programs are disjoint
halted-paused-disjoint : ∀{p} → halted p → paused p → ⊥
halted-paused-disjoint hnothin   ()
halted-paused-disjoint (hexit _) ()

↓_ : ∀ {p} → halted p → Term
↓ hnothin = nothin
↓ hexit zero = nothin
↓ hexit (suc n) = exit n

↓-well-behaved : ∀ p -> (haltedp : halted p) -> halted (↓ haltedp)
↓-well-behaved .nothin hnothin = hnothin
↓-well-behaved .(exit 0) (hexit zero) = hnothin
↓-well-behaved .(exit (suc n)) (hexit (suc n)) = hexit n

A-max : Ctrl → Ctrl → Ctrl
A-max GO   GO   = GO
A-max GO   WAIT = GO
A-max WAIT GO   = GO
A-max WAIT WAIT = WAIT

value-max : ∀{p q} → done p → done q → (halted p ⊎ halted q) →  Term
value-max {q = q} (dhalted hnothin)   done-q              h⊎h = q
value-max {p = p} done-p              (dhalted hnothin)   h⊎h = p
value-max         (dhalted (hexit n)) (dhalted (hexit m)) h⊎h = exit (n ⊔ℕ m)
value-max         (dhalted (hexit n)) (dpaused _)         h⊎h = exit n
value-max         (dpaused _)         (dhalted (hexit m)) h⊎h = exit m
value-max         (dpaused paused-p)  (dpaused paused-q)  (inj₁ halted-p) =
  ⊥-elim (halted-paused-disjoint halted-p paused-p)
value-max         (dpaused paused-p)  (dpaused paused-q)  (inj₂ halted-q) =
  ⊥-elim (halted-paused-disjoint halted-q paused-q)

value-max-unique : ∀{p q d1 d2 d3 d4 ij1 ij2} → value-max{p}{q} d1 d2 ij1 ≡ value-max{p}{q} d3 d4 ij2
value-max-unique {d1 = dhalted hnothin}   {d2}                {dhalted hnothin}    {d4}                 {ij1} {ij2} = refl
value-max-unique {d1 = dhalted (hexit n)} {dhalted hnothin}   {dhalted (hexit .n)} {dhalted hnothin}    {ij1} {ij2} = refl
value-max-unique {d1 = dpaused p/paused}  {dhalted hnothin}   {dpaused p/paused'}  {dhalted hnothin}    {ij1} {ij2} = refl
value-max-unique {d1 = dhalted (hexit n)} {dhalted (hexit m)} {dhalted (hexit .n)} {dhalted (hexit .m)} {ij1} {ij2} = refl
value-max-unique {d1 = dhalted (hexit n)} {dpaused q/paused}  {dhalted (hexit .n)} {dpaused q/paused'}  {ij1} {ij2} = refl
value-max-unique {d1 = dpaused p/paused}  {dhalted (hexit n)} {dpaused p/paused'}  {dhalted (hexit .n)} {ij1} {ij2} = refl
value-max-unique {d1 = dpaused p/paused}  {dpaused q/paused}  {dpaused p/paused'}  {dpaused q/paused'} {inj₁ p/halted} {ij2} =
  ⊥-elim (halted-paused-disjoint p/halted p/paused')
value-max-unique {d1 = dpaused p/paused} {dpaused q/paused}   {dpaused p/paused'}  {dpaused q/paused'} {inj₂ q/halted} {ij2} =
  ⊥-elim (halted-paused-disjoint q/halted q/paused')
value-max-unique {d1 = dhalted p/halted} {d2} {dpaused p/paused'} {d4} {ij1} {ij2} =
  ⊥-elim (halted-paused-disjoint p/halted p/paused')
value-max-unique {d1 = dpaused p/paused} {d2} {dhalted p/halted'} {d4} {ij1} {ij2} =
  ⊥-elim (halted-paused-disjoint p/halted' p/paused)
value-max-unique {d1 = d1} {dhalted q/halted} {d3} {dpaused q/paused} {ij1} {ij2} =
  ⊥-elim (halted-paused-disjoint q/halted q/paused)
value-max-unique {d1 = d1} {dpaused q/paused}  {d3} {dhalted q/halted} {ij1} {ij2} =
  ⊥-elim (halted-paused-disjoint q/halted q/paused)

value-max-sym : ∀ {p q} ->
  (donep : done p) ->
  (haltedq : halted q) ->
  value-max donep (dhalted haltedq) (inj₂ haltedq) ≡
  value-max (dhalted haltedq) donep (inj₁ haltedq)
value-max-sym (dhalted hnothin) hnothin = refl
value-max-sym (dhalted hnothin) (hexit n) = refl
value-max-sym (dhalted (hexit n)) hnothin = refl
value-max-sym (dhalted (hexit n)) (hexit m)
  rewrite ⊔-sym n m = refl
value-max-sym (dpaused p/paused) hnothin = refl
value-max-sym (dpaused p/paused) (hexit n) = refl


value-max-done : ∀ {p q} →
  (p/done : done p) →
  (q/done : done q) →
  (p/halted⊎q/halted : halted p ⊎ halted q) →
  done (value-max p/done q/done p/halted⊎q/halted)
value-max-done (dhalted hnothin)   q/done              ⟨p⊎q⟩/halted = q/done
value-max-done (dhalted (hexit n)) (dhalted hnothin)   ⟨p⊎q⟩/halted = dhalted (hexit n)
value-max-done (dhalted (hexit n)) (dhalted (hexit m)) ⟨p⊎q⟩/halted = dhalted (hexit (n ⊔ℕ m))
value-max-done (dhalted (hexit n)) (dpaused q/paused)  ⟨p⊎q⟩/halted = dhalted (hexit n)
value-max-done (dpaused p/paused)  (dhalted hnothin)   ⟨p⊎q⟩/halted = dpaused p/paused
value-max-done (dpaused p/paused)  (dhalted (hexit m)) ⟨p⊎q⟩/halted = dhalted (hexit m)
value-max-done (dpaused p/paused)  (dpaused q/paused)  (inj₁ p/halted) =
  ⊥-elim (halted-paused-disjoint p/halted p/paused)
value-max-done (dpaused p/paused)  (dpaused q/paused)  (inj₂ q/halted) =
  ⊥-elim (halted-paused-disjoint q/halted q/paused)

{-
Properties relating halted, paused, done programs and the contexts. There's no way to
decompose halted programs, so the result must remain halted. The decomposition of paused
programs under the evaluation context must result in paused programs.

    halted-⟦⟧c : ∀{p p' C} → halted p → p ≐ C ⟦ p' ⟧c → halted p'
    paused-⟦⟧e : ∀{p p' E} → paused p → p ≐ E ⟦ p' ⟧e → paused p'
-}
halted-⟦⟧c : ∀{p p' C} → halted p → p ≐ C ⟦ p' ⟧c → halted p'
halted-⟦⟧c hnothin dchole = hnothin
halted-⟦⟧c (hexit n) dchole = hexit n

-- In fact, the only valid case would be E ≡ [] and p ≡ p'
halted-⟦⟧e : ∀{p p' E} → halted p → p ≐ E ⟦ p' ⟧e → halted p'
halted-⟦⟧e p/halted p≐E⟦p'⟧ = halted-⟦⟧c p/halted (⟦⟧e-to-⟦⟧c p≐E⟦p'⟧)

paused-⟦⟧e : ∀{p p' E} → paused p → p ≐ E ⟦ p' ⟧e → paused p'
paused-⟦⟧e ppause dehole = ppause
paused-⟦⟧e (pseq paused) dehole = pseq paused
paused-⟦⟧e (pseq paused) (deseq d) = paused-⟦⟧e paused d
paused-⟦⟧e (ploopˢ paused) dehole = ploopˢ paused
paused-⟦⟧e (ploopˢ paused) (deloopˢ d) = paused-⟦⟧e paused d
paused-⟦⟧e (ppar paused₁ paused₂) dehole = ppar paused₁ paused₂
paused-⟦⟧e (ppar paused₁ paused₂) (depar₁ d) = paused-⟦⟧e paused₁ d
paused-⟦⟧e (ppar paused₁ paused₂) (depar₂ d) = paused-⟦⟧e paused₂ d
paused-⟦⟧e (psuspend paused) dehole = psuspend paused
paused-⟦⟧e (psuspend paused) (desuspend d) = paused-⟦⟧e paused d
paused-⟦⟧e (ptrap paused) dehole = ptrap paused
paused-⟦⟧e (ptrap paused) (detrap d) = paused-⟦⟧e paused d

done-⟦⟧e : ∀ {p p' E} → done p → p ≐ E ⟦ p' ⟧e → done p'
done-⟦⟧e (dhalted p/halted) p≐E⟦p'⟧ = dhalted (halted-⟦⟧e p/halted p≐E⟦p'⟧)
done-⟦⟧e (dpaused p/paused) p≐E⟦p'⟧ = dpaused (paused-⟦⟧e p/paused p≐E⟦p'⟧)

halted-dec : ∀ p -> Dec (halted p)
halted-dec nothin = yes hnothin
halted-dec pause = no (λ ())
halted-dec (signl S p) = no (λ ())
halted-dec (present S ∣⇒ p ∣⇒ p₁) = no (λ ())
halted-dec (emit S) = no (λ ())
halted-dec (p ∥ q) = no (λ ())
halted-dec (loop p) = no (λ ())
halted-dec (loopˢ p q) = no (λ ())
halted-dec (p >> q) = no (λ ())
halted-dec (suspend p S) = no (λ ())
halted-dec (trap p) = no (λ ())
halted-dec (exit x) = yes (hexit x)
halted-dec (shared s ≔ e in: p) = no (λ ())
halted-dec (s ⇐ e) = no (λ ())
halted-dec (var x ≔ e in: p) = no (λ ())
halted-dec (x ≔ e) = no (λ ())
halted-dec (if x ∣⇒ p ∣⇒ q) = no (λ ())
halted-dec (ρ⟨ θ , A ⟩· p) = no (λ ())

paused-dec : ∀ p -> Dec (paused p)
paused-dec nothin = no (λ ())
paused-dec pause = yes ppause
paused-dec (signl S p) = no (λ ())
paused-dec (present S ∣⇒ p ∣⇒ p₁) = no (λ ())
paused-dec (emit S) = no (λ ())
paused-dec (p ∥ q) with paused-dec p | paused-dec q
paused-dec (p ∥ q) | yes pausedp | yes pausedq = yes (ppar pausedp pausedq)
paused-dec (p ∥ q) | _ | no ¬pausedq = no (λ { (ppar _ pausedq) → ¬pausedq pausedq } )
paused-dec (p ∥ q) | no ¬pausedp | _ = no (λ { (ppar pausedp _) → ¬pausedp pausedp } )
paused-dec (loop p) = no (λ ())
paused-dec (loopˢ p q) with paused-dec p
paused-dec (loopˢ p q) | yes pausedp = yes (ploopˢ pausedp)
paused-dec (loopˢ p q) | no ¬pausedp = no (λ { (ploopˢ pausedp) → ¬pausedp pausedp })
paused-dec (p >> q) with paused-dec p
paused-dec (p >> q) | yes pausedp = yes (pseq pausedp)
paused-dec (p >> q) | no ¬pausedp = no (λ { (pseq pausedp) → ¬pausedp pausedp })
paused-dec (suspend p S) with paused-dec p
paused-dec (suspend p S) | yes pausedp = yes (psuspend pausedp)
paused-dec (suspend p S) | no ¬pausedp = no (λ { (psuspend pausedp) → ¬pausedp pausedp })
paused-dec (trap p) with paused-dec p
paused-dec (trap p) | yes pasuedp = yes (ptrap pasuedp)
paused-dec (trap p) | no ¬pausedp = no (λ { (ptrap pausedp) → ¬pausedp pausedp })
paused-dec (exit x) = no (λ ())
paused-dec (shared s ≔ e in: p) = no (λ ())
paused-dec (s ⇐ e) = no (λ ())
paused-dec (var x ≔ e in: p) = no (λ ())
paused-dec (x ≔ e) = no (λ ())
paused-dec (if x ∣⇒ p ∣⇒ q) = no (λ ())
paused-dec (ρ⟨ θ , A ⟩· p) = no (λ ())

done-dec : ∀ p → Dec (done p)
done-dec p with halted-dec p
done-dec p | yes halted-p = yes (dhalted halted-p)
done-dec p | no ¬halted-p with paused-dec p
done-dec p | no _ | yes paused-p = yes (dpaused paused-p)
done-dec p | no ¬halted-p | (no ¬paused-p) = no
  (λ { (dhalted p/halted) → ¬halted-p p/halted ;
       (dpaused p/paused) → ¬paused-p p/paused})


signal-absent-or-present : Signal.Status → Set
signal-absent-or-present S = S ≡ Signal.absent ⊎ S ≡ Signal.present

signal-absent-or-present-dec : Decidable signal-absent-or-present
signal-absent-or-present-dec present = yes (inj₂ refl)
signal-absent-or-present-dec absent = yes (inj₁ refl)
signal-absent-or-present-dec unknown = no (λ { (inj₁ ()) ; (inj₂ ())})

signals-all-absent-or-present-dec :
  (Ss :  SigMap.Map Signal.Status) ->
        Dec (∀ S → (S∈ : (SigMap.∈Dom S Ss)) →
              (signal-absent-or-present (SigMap.lookup{k = S} Ss S∈)))
signals-all-absent-or-present-dec m
   with SigOMap.andmap{_}{signal-absent-or-present} signal-absent-or-present-dec m
signals-all-absent-or-present-dec m | yes p = yes (λ S → p (Signal.unwrap S))
signals-all-absent-or-present-dec m | no ¬p = no (λ z → ¬p (λ n → z (n ₛ)))

var-is-ready : SharedVar.Status × ℕ → Set
var-is-ready p = (proj₁ p) ≡ SharedVar.ready

var-is-ready-dec : Decidable var-is-ready
var-is-ready-dec (ready , _) = yes refl
var-is-ready-dec (new , _) = no (λ ())
var-is-ready-dec (old , _) = no (λ ())

vars-all-ready-dec :
  (ss : ShrMap.Map (SharedVar.Status × ℕ)) ->
   Dec (∀ s → (s∈ : ShrMap.∈Dom s ss) →
        var-is-ready (ShrMap.lookup{k = s} ss s∈))
vars-all-ready-dec ss with ShrOMap.andmap{_}{var-is-ready} var-is-ready-dec ss
vars-all-ready-dec ss | yes p = yes (λ s → p (SharedVar.unwrap s))
vars-all-ready-dec ss | no ¬p = no (λ z → ¬p (λ n → z (n ₛₕ)))

complete-θ-dec : ∀ θ → Dec (complete-θ θ)
complete-θ-dec (Θ sigs shr _) with signals-all-absent-or-present-dec sigs
complete-θ-dec (Θ sigs shrs _) | yes p with vars-all-ready-dec shrs
complete-θ-dec (Θ sigs shrs _) | yes p₁ | yes p₂ = yes (θcomplete p₁ p₂)
complete-θ-dec (Θ sigs shrs _) | yes _ | no ¬p = no (λ { (θcomplete _ x) → ¬p x } )
complete-θ-dec (Θ sigs shrs _) | no ¬p = no (λ { (θcomplete x _) → ¬p x } )

complete-dec : ∀ p → Dec (complete p)
complete-dec p with done-dec p
complete-dec p | yes donep = yes (codone donep)
complete-dec nothin | no ¬donep = no (λ _ → ¬donep (dhalted hnothin))
complete-dec pause | no ¬donep = no (λ _ → ¬donep (dpaused ppause))
complete-dec (signl S p) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (present S ∣⇒ p ∣⇒ p₁) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (emit S) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (p ∥ p₁) | no ¬donep =  no (λ { (codone x) → ¬donep x } )
complete-dec (loop p) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (loopˢ p q) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (p >> p₁) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (suspend p S) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (trap p) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (exit x) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (shared s ≔ e in: p) | no ¬donep = no (λ { (codone x) → ¬donep x } )
complete-dec (s ⇐ e) | no ¬donep =  no (λ { (codone x) → ¬donep x } )
complete-dec (var x ≔ e in: p) | no ¬donep =  no (λ { (codone x) → ¬donep x } )
complete-dec (x ≔ e) | no ¬donep =  no (λ { (codone x) → ¬donep x } )
complete-dec (if x ∣⇒ p ∣⇒ p₁) | no ¬donep =  no (λ { (codone x) → ¬donep x } )
complete-dec (ρ⟨ θ , A ⟩· p) | _ with done-dec p
complete-dec (ρ⟨ θ , A ⟩· p) | _ | yes donep with complete-θ-dec θ
complete-dec (ρ⟨ θ , A ⟩· p) | _ | yes donep | (yes complete-θ) = yes (coenv complete-θ donep)
complete-dec (ρ⟨ θ , A ⟩· p) | _ | yes donep | (no ¬complete-θ) = no
   (λ { (codone (dhalted ())) ;
        (codone (dpaused ())) ;
        (coenv complete-θ _) → ¬complete-θ complete-θ })
complete-dec (ρ⟨ θ , A ⟩· p) | _ | no ¬donep = no
  (λ { (codone (dhalted ())) ;
       (codone (dpaused ())) ;
       (coenv _ donep) → ¬donep donep })


A-max-GO-≡-left : ∀ A → A-max GO A ≡ GO
A-max-GO-≡-left GO =  refl
A-max-GO-≡-left WAIT = refl

A-max-GO-≡-right : ∀ A → A-max A GO ≡ GO
A-max-GO-≡-right GO = refl
A-max-GO-≡-right WAIT = refl

A-max-comm : ∀ A1 A2 → A-max A1 A2 ≡ A-max A2 A1
A-max-comm GO GO = refl
A-max-comm GO WAIT = refl
A-max-comm WAIT GO = refl 
A-max-comm WAIT WAIT = refl 

A-max-assoc : ∀ A1 A2 A3 → (A-max A1 $ A-max A2 A3) ≡ A-max (A-max A1 A2) A3
A-max-assoc GO GO GO = refl
A-max-assoc GO GO WAIT = refl
A-max-assoc GO WAIT GO = refl
A-max-assoc GO WAIT WAIT = refl
A-max-assoc WAIT GO GO = refl
A-max-assoc WAIT GO WAIT = refl
A-max-assoc WAIT WAIT GO = refl
A-max-assoc WAIT WAIT WAIT = refl

A-max-swap : ∀ A1 A2 A3
             → (A-max (A-max A1 A2) A3) ≡ (A-max (A-max A1 A3) A2)
A-max-swap A1 A2 A3 = begin
                        (A-max (A-max A1 A2) A3) ≡⟨ sym (A-max-assoc A1 A2 A3) ⟩
                        (A-max A1 $ A-max A2 A3) ≡⟨ sym (cong (A-max A1) (A-max-comm A3 A2)) ⟩
                        (A-max A1 $ A-max A3 A2) ≡⟨ A-max-assoc A1 A3 A2 ⟩
                        (A-max (A-max A1 A3) A2) ∎
                       
