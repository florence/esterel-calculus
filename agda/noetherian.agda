module noetherian where

open import sn-calculus
open import Esterel.Lang 
open import Esterel.Lang.Properties
open import Esterel.Context
open import Esterel.Context.Properties
open import Esterel.Environment
open import Esterel.Variable.Signal as Signal using (Signal)
open import Esterel.Variable.Shared as SharedVar using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar using (SeqVar)
open import Data.Nat as Nat
  using (ℕ ; zero ; suc ; _+_ ; _>_ ; _≤′_ ; _≤_ ; _*_ ; ≤′-refl)
open import Data.Nat.Properties
  using (s≤′s ; z≤′n ; m≤′m+n ; n≤′m+n ; ≤⇒pred≤)
open import Data.Nat.Properties.Simple using (+-comm ; +-assoc ; +-suc)
open import Data.MoreNatProp
open import Data.Sum as Sum using (inj₁ ; inj₂ ; _⊎_)
open import Data.Maybe using (just ; nothing)
open import Data.Product using (_×_ ; _,_ ; _,′_ ; proj₁)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Data.List using (List ; _∷_ ; [])
open import Data.Bool using (Bool ; true ; false)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary
  using (Dec ; yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality
  using (sym ; inspect ; Reveal_·_is_ ; trans ; cong)
open import Data.Empty using (⊥-elim ; ⊥)

SM = SigMap.Map Signal.Status
ShM = ShrMap.Map (SharedVar.Status × ℕ)

is-unknownp : Signal.Status -> Bool
is-unknownp x = ⌊ x Signal.≟ₛₜ Signal.unknown ⌋

is-notreadyp : SharedVar.Status × ℕ -> Bool
is-notreadyp (SharedVar.ready , _) = false
is-notreadyp (SharedVar.new   , _) = true
is-notreadyp (SharedVar.old   , _) = true

is-notreadyp-status : SharedVar.Status -> Bool
is-notreadyp-status SharedVar.ready = false
is-notreadyp-status SharedVar.new = true
is-notreadyp-status SharedVar.old = true

is-notreadyp' : SharedVar.Status × ℕ -> Bool
is-notreadyp' x = is-notreadyp-status (proj₁ x)

hunch : ∀ x -> is-notreadyp x ≡ is-notreadyp' x
hunch (SharedVar.ready , proj₃) = refl
hunch (SharedVar.new , proj₃) = refl
hunch (SharedVar.old , proj₃) = refl

numstepsSig : SM -> ℕ
numstepsSig m = SigMap.count is-unknownp m

numstepsShr : ShM -> ℕ
numstepsShr m = ShrMap.count is-notreadyp m

numstepsθ : Env -> ℕ
numstepsθ (Θ sig₁ shr₁ var₁) = (numstepsSig sig₁) + (numstepsShr shr₁)

∥_∥s : Term -> ℕ
∥ nothin ∥s = 0
∥ pause ∥s = 0

{- one for stepping to ρ θ p
   one for (maybe) setting S to absent
   one for (maybe) this ρ mergeing with another one 
   (same idea for `shared` and `var`) -}
∥ (signl S p) ∥s = suc (suc (suc (∥ p ∥s)))

∥ (present S ∣⇒ p ∣⇒ q) ∥s = suc (∥ p ∥s + ∥ q ∥s)
∥ (emit S) ∥s = 1
∥ (p ∥ q) ∥s = suc (∥ p ∥s + ∥ q ∥s)
∥ (loop p) ∥s = suc (suc (∥ p ∥s + ∥ p ∥s))
∥ (loopˢ p q) ∥s = suc (∥ p ∥s + ∥ q ∥s)
∥ (p >> q) ∥s = suc (∥ p ∥s + ∥ q ∥s)
∥ (suspend p S) ∥s = suc (∥ p ∥s)
∥ (trap p) ∥s = suc (∥ p ∥s)
∥ (exit x) ∥s = 0
∥ (shared s ≔ e in: p) ∥s = suc (suc (suc (∥ p ∥s)))
∥ (s ⇐ e) ∥s = 1
∥ (var x ≔ e in: p) ∥s = suc (suc (∥ p ∥s))
∥ (x ≔ e) ∥s = 1
∥ (if x ∣⇒ p ∣⇒ q) ∥s = suc (∥ p ∥s + ∥ q ∥s)
∥ (ρ⟨ θ , A ⟩· p) ∥s = suc (numstepsθ θ + ∥ p ∥s)

arith1 : ∀ a b c -> suc b ≤′ c -> suc (suc (a + b)) ≤′ suc (a + c)
arith1 a b c sucb≤′c rewrite sym (+-suc a b) = s≤′s (≤′+r {z = a} sucb≤′c)

arith2 : ∀ x y z -> suc x ≤′ y -> suc (suc (x + z)) ≤′ suc (y + z)
arith2 x y z sucx≤′y = s≤′s (≤′+l{z = z} sucx≤′y)

arith3 : ∀ x y z -> suc x ≤′ y -> suc (suc (z + x)) ≤′ suc (z + y)
arith3 x y z sucx≤′y rewrite sym (+-suc z x) = s≤′s (≤′+r {z = z} sucx≤′y)

arith4 : ∀ x y z -> suc (suc x + y + z) ≤′ suc (x + suc y + z)
arith4 x y z rewrite +-suc x y = s≤′s ≤′-refl

arith5 : ∀ x y -> suc x ≤′ y -> suc (suc (suc (x + x))) ≤′ suc (suc (y + y))
arith5 x y sucx≤′y rewrite sym (+-suc x x) =
  s≤′s (s≤′s (≤′+b x (suc x) y y (suc≤′⇒≤′ x y sucx≤′y)  sucx≤′y))

decompose∥∥s : ∀ E p -> ∥ E ⟦ p ⟧e ∥s ≡ ∥ E ⟦ nothin ⟧e ∥s + ∥ p ∥s
decompose∥∥s [] p = refl
decompose∥∥s (x ∷ E) p with decompose∥∥s E
decompose∥∥s (epar₁ q ∷ E) p | R
  rewrite R p
  | +-assoc (∥ E ⟦ nothin ⟧e ∥s) ∥ p ∥s  ∥ q ∥s 
  | +-assoc (∥ E ⟦ nothin ⟧e ∥s) ∥ q ∥s  ∥ p ∥s
  | +-comm (∥ p ∥s) (∥ q ∥s)
  = cong suc refl
decompose∥∥s (epar₂ p ∷ E) p₁ | R
  rewrite R p₁
  | +-assoc ∥ p ∥s ∥ E ⟦ nothin ⟧e ∥s ∥ p₁ ∥s 
  = cong suc refl
decompose∥∥s (eseq q ∷ E) p | R
  rewrite R p
  | +-assoc (∥ E ⟦ nothin ⟧e ∥s) ∥ p ∥s  ∥ q ∥s 
  | +-assoc (∥ E ⟦ nothin ⟧e ∥s) ∥ q ∥s  ∥ p ∥s
  | +-comm (∥ p ∥s) (∥ q ∥s)
  = cong suc refl
decompose∥∥s (eloopˢ q ∷ E) p | R
  rewrite R p
  | +-assoc (∥ E ⟦ nothin ⟧e ∥s) ∥ p ∥s  ∥ q ∥s 
  | +-assoc (∥ E ⟦ nothin ⟧e ∥s) ∥ q ∥s  ∥ p ∥s
  | +-comm (∥ p ∥s) (∥ q ∥s)
  = cong suc refl
decompose∥∥s (esuspend S ∷ E) p | R rewrite R p = refl
decompose∥∥s (etrap ∷ E) p | R rewrite R p = refl

eplug≤ : ∀ p q E ->
  ∥ p ∥s ≤′ ∥ q ∥s ->
  ∥ E ⟦ p ⟧e ∥s ≤′ ∥ E ⟦ q ⟧e ∥s
eplug≤ p q E ∥p∥s≤′∥q∥s
  rewrite decompose∥∥s E p | decompose∥∥s E q
  = ≤′+r{z = ∥ E ⟦ nothin ⟧e ∥s} ∥p∥s≤′∥q∥s

eplug< : ∀ p q E ->
  suc ∥ p ∥s ≤′ ∥ q ∥s ->
  suc (∥ (E ⟦ p ⟧e) ∥s) ≤′ (∥ (E ⟦ q ⟧e) ∥s)
eplug< p q E ∥p∥s<∥q∥s
  rewrite decompose∥∥s E p | decompose∥∥s E q
        | sym (+-suc ∥ E ⟦ nothin ⟧e ∥s  ∥ p ∥s)
  = ≤′+r{z = ∥ E ⟦ nothin ⟧e ∥s} ∥p∥s<∥q∥s

valuemax-norm : ∀ {p q} ->
  (donep : done p) -> (doneq : done q) ->
  (haltedporq : halted p ⊎ halted q) ->
  ∥ value-max donep doneq haltedporq ∥s ≤′ ∥ p ∥s + ∥ q ∥s
valuemax-norm (dhalted hnothin) (dhalted p/halted₁) _ = ≤′-refl
valuemax-norm (dhalted (hexit n)) (dhalted hnothin) _ = ≤′-refl
valuemax-norm (dhalted (hexit n)) (dhalted (hexit m)) _ = ≤′-refl
valuemax-norm (dhalted hnothin) (dpaused p/paused) _ = ≤′-refl
valuemax-norm{q = q} (dhalted (hexit n)) (dpaused p/paused) _ = m≤′m+n 0 ∥ q ∥s
valuemax-norm{p = p} (dpaused p/paused) (dhalted hnothin) _ = m≤′m+n ∥ p ∥s 0
valuemax-norm (dpaused p/paused) (dhalted (hexit n)) _ = z≤′n
valuemax-norm (dpaused p/paused) (dpaused p/paused₁) (inj₁ x) =
  ⊥-elim (halted-paused-disjoint x p/paused)
valuemax-norm (dpaused p/paused) (dpaused p/paused₁) (inj₂ y) =
  ⊥-elim (halted-paused-disjoint y p/paused₁)

halted-norm : ∀ {p} -> (haltedp : halted p) ->  ∥ ↓ haltedp ∥s ≡ 0
halted-norm hnothin = refl
halted-norm (hexit zero) = refl
halted-norm (hexit (suc n)) = refl

noetherian₁ :
  ∀ {p q} ->
  p sn⟶₁ q ->
  (suc (∥ q ∥s)) ≤′ (∥ p ∥s)
noetherian₁ (rpar-done-right{p}{q} haltedp doneq) =
  s≤′s (valuemax-norm (dhalted haltedp) doneq (inj₁ haltedp)) 
noetherian₁ (rpar-done-left{p}{q} donep haltedq) =
  s≤′s (valuemax-norm donep (dhalted haltedq) (inj₂ haltedq)) 
noetherian₁ (ris-present{θ}{S = S}{p = p}{q = q}{E = E} S∈ x x₁) with unplug x₁
... | refl =
  arith1 (numstepsθ θ)
         ∥ E ⟦ p ⟧e ∥s
         ∥ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e ∥s
         (eplug< p (present S ∣⇒ p ∣⇒ q) E (s≤′s (m≤′m+n ∥ p ∥s ∥ q ∥s)))

noetherian₁ (ris-absent{θ}{S}{p = p}{q = q}{E = E} S∈ x x₁) with unplug x₁
... | refl =
  arith1 (numstepsθ θ)
         ∥ E ⟦ q ⟧e ∥s
         ∥ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e ∥s
         (eplug< q (present S ∣⇒ p ∣⇒ q) E (s≤′s (n≤′m+n ∥ p ∥s ∥ q ∥s)))

noetherian₁ (remit {θ} {_} {S} {E} S∈ ¬S≡a x) with unplug x
noetherian₁ (remit {θ} {_} {S} {E} S∈ ¬S≡a x) | refl with
    is-unknownp (SigMap.lookup{k = S} (sig θ) S∈)
  | inspect is-unknownp (SigMap.lookup{k = S} (sig θ) S∈)
  | SigMap.lookup{k = S} (sig θ) S∈
  | inspect (SigMap.lookup{k = S} (sig θ)) S∈
... | true  | Reveal_·_is_.[ eq1 ] | Signal.present | Reveal_·_is_.[ eq ]
  rewrite eq = ⊥-elim (false-not-true eq1) where
  false-not-true : false ≡ true -> ⊥
  false-not-true ()
... | false | Reveal_·_is_.[ eq1 ] | Signal.absent  | Reveal_·_is_.[ eq ]
  = ⊥-elim (¬S≡a refl)
... | true  | Reveal_·_is_.[ eq1 ] | Signal.absent  | Reveal_·_is_.[ eq ]
  = ⊥-elim (¬S≡a refl)
... | false | Reveal_·_is_.[ eq1 ] | Signal.unknown | Reveal_·_is_.[ eq ]
  rewrite eq = ⊥-elim (true-not-false eq1) where
  true-not-false : true ≡ false -> ⊥
  true-not-false ()
noetherian₁ (remit {θ} {.(E ⟦ emit S ⟧e)} {S} {E} S∈ ¬S≡a x)
   | refl | false | Reveal_·_is_.[ eq1 ] | Signal.present | Reveal_·_is_.[ eq ]
   with sym (SigMap.getput-m S (sig θ) S∈)
... | updateθ-S-to-present≡θ rewrite eq | updateθ-S-to-present≡θ =
  arith1 (numstepsθ θ)
         ∥ E ⟦ nothin ⟧e ∥s
         ∥ E ⟦ emit S ⟧e ∥s
         (eplug< nothin (emit S) E ≤′-refl)
noetherian₁ (remit {θ} {.(E ⟦ emit S ⟧e)} {S} {E} S∈ ¬S≡a x)
  | refl | true  | Reveal_·_is_.[ eq1 ] | Signal.unknown | Reveal_·_is_.[ eq ]
  rewrite SigMap.change-one-count-goes-down
   (sig θ) is-unknownp
   S S∈ eq1 Signal.present refl =
   s≤′s (s≤′s (≤′+r {z = numstepsθ (set-sig{S} θ S∈ Signal.present)}
                    (eplug≤ nothin (emit S) E (Nat.≤′-step ≤′-refl))))

noetherian₁ rloop-unroll = ≤′-refl
noetherian₁ rseq-done = ≤′-refl
noetherian₁ (rseq-exit{q}) = s≤′s z≤′n
noetherian₁ (rloopˢ-exit{q}) = s≤′s z≤′n
noetherian₁ (rsuspend-done x) = ≤′-refl
noetherian₁ (rtrap-done{p} haltedp)
  rewrite halted-norm haltedp =
  s≤′s z≤′n
noetherian₁ (rraise-signal{p}{S}) = ans where
  oneunknown≡1 : ∀ S ->
     numstepsθ (Θ SigMap.[ S ↦ Signal.unknown ] [] []) ≡ 1
  oneunknown≡1 (zero Signal.ₛ) = refl
  oneunknown≡1 (suc n Signal.ₛ) = oneunknown≡1 (n Signal.ₛ)

  ans : suc (suc (numstepsθ (Θ SigMap.[ S ↦ Signal.unknown ] [] []) +  ∥ p ∥s))
     ≤′ suc (suc (suc ∥ p ∥s))
  ans rewrite oneunknown≡1 S = ≤′-refl

noetherian₁ (rraise-shared{θ}{_}{s}{e}{p}{E} e' x) with unplug x
... | refl =
  arith1 (numstepsθ θ)
         ∥ E ⟦ ρ⟨ [s,δe]-env  s (δ e') , WAIT ⟩· p ⟧e ∥s
         ∥ E ⟦ shared s ≔ e in: p ⟧e ∥s
         (eplug< (ρ⟨ [s,δe]-env s (δ e') , WAIT ⟩· p)
                 (shared s ≔ e in: p) E newθ≡1) where

   silly : ∀ s -> numstepsθ ([s,δe]-env s (δ e')) ≡ 1
   silly (zero SharedVar.ₛₕ) = refl
   silly (suc x₁ SharedVar.ₛₕ) = silly (x₁ SharedVar.ₛₕ)

   newθ≡1 : suc (suc (numstepsθ ([s,δe]-env s (δ e')) + ∥ p ∥s)) ≤′
            suc (suc (suc ∥ p ∥s))
   newθ≡1 rewrite silly s = ≤′-refl

noetherian₁ (rset-shared-value-old{θ}{_}{s}{e}{E} e' s∈ θ[s]≡old x) with unplug x
... | refl  = ans where

  snotready : is-notreadyp (ShrMap.lookup{k = s} (shr θ) s∈) ≡ true
  snotready rewrite hunch (ShrMap.lookup{k = s} (shr θ) s∈)
            | θ[s]≡old = refl

  θsame : numstepsθ (set-shr{s} θ s∈ (SharedVar.new) (δ e'))
        ≡ numstepsθ θ
  θsame rewrite
     ShrMap.change-nothing-count-stays-same
       (shr θ) is-notreadyp s s∈
       (SharedVar.new , δ e') snotready = refl

  ans : suc ∥ (ρ⟨ (set-shr{s} θ s∈ (SharedVar.new) (δ e')) , GO ⟩·
                 E ⟦ nothin ⟧e) ∥s ≤′
        ∥ ρ⟨ θ , GO ⟩· E ⟦ s ⇐ e ⟧e ∥s
  ans rewrite θsame =
    arith1 (numstepsθ θ)
            ∥ E ⟦ nothin ⟧e ∥s
            ∥ E ⟦ s ⇐ e ⟧e ∥s
            (eplug< nothin (s ⇐ e) E ≤′-refl)

noetherian₁ (rset-shared-value-new{θ}{_}{s}{e}{E} e' s∈ θ[s]≡new x) with unplug x
... | refl = ans where

  snotready : is-notreadyp (ShrMap.lookup{k = s} (shr θ) s∈) ≡ true
  snotready rewrite hunch (ShrMap.lookup{k = s} (shr θ) s∈)
            | θ[s]≡new = refl

  θsame : numstepsθ (set-shr{s} θ s∈ (SharedVar.new) (shr-vals{s} θ s∈ + δ e'))
        ≡ numstepsθ θ
  θsame rewrite
     ShrMap.change-nothing-count-stays-same
       (shr θ) is-notreadyp s s∈
       (SharedVar.new , shr-vals{s} θ s∈ + δ e') snotready = refl

  ans : suc ∥ (ρ⟨ (set-shr{s} θ s∈ (SharedVar.new) (shr-vals{s} θ s∈ + δ e')) , GO ⟩·
                 E ⟦ nothin ⟧e) ∥s ≤′
        ∥ ρ⟨ θ , GO ⟩· E ⟦ s ⇐ e ⟧e ∥s
  ans rewrite θsame =
     arith1 (numstepsθ θ)
            ∥ E ⟦ nothin ⟧e ∥s
            ∥ E ⟦ s ⇐ e ⟧e ∥s
            (eplug< nothin (s ⇐ e) E ≤′-refl) 

noetherian₁ (rraise-var{θ}{r}{x}{p}{e}{E} e' x₁) with unplug x₁
... | refl =
  arith1 (numstepsθ θ)
         ∥ E ⟦ ρ⟨ [x,δe]-env x (δ e') , WAIT ⟩· p ⟧e ∥s
         ∥ E ⟦ var x ≔ e in: p ⟧e ∥s
         (eplug< (ρ⟨ [x,δe]-env x (δ e') , WAIT ⟩· p)
                 (var x ≔ e in: p)
                 E
                 ≤′-refl)
noetherian₁ (rset-var{θ}{_}{x}{e}{E} x∈ e' x₁) with unplug x₁
... | refl =
  arith1 (numstepsθ θ)
          ∥ E ⟦ nothin ⟧e ∥s
          ∥ E ⟦ x ≔ e ⟧e ∥s
          (eplug< nothin (x ≔ e) E ≤′-refl)
noetherian₁ (rif-false{θ}{p = p}{q = q}{x = x}{E = E} x∈ x₁ x₂) with unplug x₂
... | refl = arith1 (numstepsθ θ)
                    ∥ E ⟦ q ⟧e ∥s
                    ∥ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e ∥s
                    (eplug< q (if x ∣⇒ p ∣⇒ q) E (s≤′s (n≤′m+n ∥ p ∥s ∥ q ∥s)))
noetherian₁ (rif-true{θ}{p = p}{q = q}{x = x}{E = E} x∈ x₁ x₂) with unplug x₂
... | refl = arith1 (numstepsθ θ)
                    ∥ E ⟦ p ⟧e ∥s
                    ∥ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e ∥s
                    (eplug< p (if x ∣⇒ p ∣⇒ q) E (s≤′s (m≤′m+n ∥ p ∥s ∥ q ∥s)))
noetherian₁ (rabsence{θ = θ}{S = S} S∈ θ[S]≡unk S̸S∉Canθ)
    with is-unknownp (SigMap.lookup{k = S} (sig θ) S∈)
       | inspect is-unknownp (SigMap.lookup{k = S} (sig θ) S∈)
... | false | Reveal_·_is_.[ eq ] rewrite θ[S]≡unk
  = ⊥-elim (absurd eq) where
      absurd : true ≡ false -> ⊥
      absurd ()
... | true  | Reveal_·_is_.[ eq ] with
   SigMap.change-one-count-goes-down
     (sig θ) is-unknownp
     S S∈ eq Signal.absent refl
... | thing rewrite thing = ≤′-refl

noetherian₁ (rreadyness {θ}{p}{s} s∈ (inj₁ θs=old) s∉Canθ)
  with is-notreadyp (ShrMap.lookup{k = s} (shr θ) s∈)
     | inspect is-notreadyp (ShrMap.lookup{k = s} (shr θ) s∈)
... | false | Reveal_·_is_.[ eq ]
  rewrite hunch (ShrMap.lookup{k = s} (shr θ) s∈) |  θs=old 
  = ⊥-elim (absurd eq) where
       absurd : true ≡ false -> ⊥
       absurd ()
... | true  | Reveal_·_is_.[ eq ] rewrite θs=old with
  ShrMap.change-one-count-goes-down
     (shr θ) is-notreadyp
     s s∈ eq (SharedVar.ready ,′ shr-vals{s} θ s∈) refl
... | thing rewrite thing =
    arith4 (numstepsSig (sig θ))
           (numstepsShr (shr (set-shr{s} θ s∈ (SharedVar.ready)
                                         (shr-vals{s} θ s∈))))
           (∥ p ∥s) 

noetherian₁ (rreadyness {θ}{p}{s} s∈ (inj₂ θs=new) s∉Canθ)
  with is-notreadyp (ShrMap.lookup{k = s} (shr θ) s∈)
     | inspect is-notreadyp (ShrMap.lookup{k = s} (shr θ) s∈)
... | false | Reveal_·_is_.[ eq ]
  rewrite hunch (ShrMap.lookup{k = s} (shr θ) s∈) |  θs=new 
  = ⊥-elim (absurd eq) where
       absurd : true ≡ false -> ⊥
       absurd ()
... | true  | Reveal_·_is_.[ eq ] rewrite θs=new with
  ShrMap.change-one-count-goes-down
     (shr θ) is-notreadyp
     s s∈ eq (SharedVar.ready ,′ shr-vals{s} θ s∈) refl
... | thing rewrite thing =
    arith4 (numstepsSig (sig θ))
           (numstepsShr (shr (set-shr{s} θ s∈ (SharedVar.ready)
                                         (shr-vals{s} θ s∈))))
           (∥ p ∥s) 


noetherian₁ (rmerge{θ₁}{θ₂}{_}{p}{E}{A₁}{A₂} x) with unplug x
... | refl rewrite decompose∥∥s E (ρ⟨ θ₂ , A₂ ⟩· p)
                 | decompose∥∥s E p
  = s≤′s
    (rearrange-things
      (numstepsSig (SigMap.union (sig θ₁) (sig θ₂)))
      (numstepsShr (ShrMap.union (shr θ₁) (shr θ₂)))
      ∥ E ⟦ nothin ⟧e ∥s
      ∥ p ∥s
      (numstepsSig (sig θ₁))
      (numstepsShr (shr θ₁))
      (numstepsSig (sig θ₂))
      (numstepsShr (shr θ₂))
      (≤′+b (numstepsSig (SigMap.union (sig θ₁) (sig θ₂)))
            (numstepsShr (ShrMap.union (shr θ₁) (shr θ₂)))
            (numstepsSig (sig θ₁) + numstepsSig (sig θ₂))
            (numstepsShr (shr θ₁) + numstepsShr (shr θ₂))
            (SigMap.count-merge≤′sum-count
             (sig θ₁) (sig θ₂) is-unknownp)
            (ShrMap.count-merge≤′sum-count
             (shr θ₁) (shr θ₂) is-notreadyp))) where

  rearrange-more :
    ∀ ab cd a b c d ->
      ab + cd ≤′ a + b + (c + d) ->
      ab + cd ≤′ a + c + (b + d)
  rearrange-more ab cd a b c d simple rewrite
     sym (+-assoc (a + c) b d)
   | +-assoc a c b
   | +-comm c b
   | sym (+-assoc a b c)
   | +-assoc (a + b) c d
   = simple

  rearrange-things : ∀ ab cd n p a c b d ->
    ab + cd ≤′ (a + b) + (c + d) ->
    suc (ab + cd + (n + p)) ≤′ a + c + (n + (suc (b + d + p)))
  rearrange-things ab cd n p a c b d simple rewrite
     +-suc n (b + d + p)
   | +-suc (a + c) (n + (b + d + p))
   | +-comm (b + d) p
   | sym (+-assoc n p (b + d))
   | +-comm (n + p) (b + d)
   | sym (+-assoc (a + c) (b + d) (n + p))
   = s≤′s (≤′+l {z = n + p} (rearrange-more ab cd a b c d simple))


csteps : ∀ {p q C C⟦p⟧ C⟦q⟧} ->
  (suc (∥ q ∥s)) ≤′ (∥ p ∥s) ->
  C⟦p⟧ ≐ C ⟦ p ⟧c ->
  C⟦q⟧ ≐ C ⟦ q ⟧c ->
  (suc ∥ C⟦q⟧ ∥s) ≤′ ∥ C⟦p⟧ ∥s
csteps sq≤p dchole dchole = sq≤p
csteps sq≤p (dcpar₁{pp}{pr}{pq} C⟦p⟧=C⟦p⟧c) (dcpar₁{qp}{qr}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith2 ∥ qp ∥s ∥ pp ∥s  ∥ pq ∥s sucnsp≰sp₁
csteps sq≤p (dcpar₂{pp}{pr}{pq} C⟦p⟧=C⟦p⟧c) (dcpar₂{qp}{qr}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith1 ∥ qp ∥s ∥ qq ∥s  ∥ pq ∥s sucnsp≰sp₁
csteps sq≤p (dcseq₁{pp}{pr}{pq} C⟦p⟧=C⟦p⟧c) (dcseq₁{qp}{qr}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith2 ∥ qp ∥s ∥ pp ∥s ∥ pq ∥s sucnsp≰sp₁
csteps sq≤p (dcseq₂{pp}{pr}{pq} C⟦p⟧=C⟦p⟧c) (dcseq₂{qp}{qr}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith1 ∥ pp ∥s ∥ qq ∥s ∥ pq ∥s sucnsp≰sp₁
csteps sq≤p (dcsuspend{p} C⟦p⟧=C⟦p⟧c) (dcsuspend{q} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = s≤′s sucnsp≰sp₁
csteps sq≤p (dctrap{p} C⟦p⟧=C⟦p⟧c) (dctrap{q} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = s≤′s sucnsp≰sp₁
csteps sq≤p (dcsignl{p} C⟦p⟧=C⟦p⟧c) (dcsignl{q} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = s≤′s (s≤′s (s≤′s sucnsp≰sp₁))
csteps sq≤p (dcpresent₁{pp}{pr}{pq} C⟦p⟧=C⟦p⟧c) (dcpresent₁{qp}{qr}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith2 ∥ qp ∥s  ∥ pp ∥s  ∥ pq ∥s  sucnsp≰sp₁
csteps sq≤p (dcpresent₂{pp}{pr}{pq} C⟦p⟧=C⟦p⟧c) (dcpresent₂{qp}{qr}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith1 ∥ pp ∥s ∥ qq ∥s ∥ pq ∥s sucnsp≰sp₁
csteps sq≤p (dcloop{p} C⟦p⟧=C⟦p⟧c) (dcloop{q} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith5 ∥ q ∥s ∥ p ∥s sucnsp≰sp₁
csteps sq≤p (dcloopˢ₁{pp}{pq} C⟦p⟧=C⟦p⟧c) (dcloopˢ₁{qp}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ =  arith2  ∥ qp ∥s  ∥ pp ∥s  ∥ pq ∥s sucnsp≰sp₁
csteps sq≤p (dcloopˢ₂{pp}{pq} C⟦p⟧=C⟦p⟧c) (dcloopˢ₂{qp}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith1 ∥ pp ∥s  ∥ qq ∥s ∥ pq ∥s sucnsp≰sp₁
csteps sq≤p (dcshared{p} C⟦p⟧=C⟦p⟧c) (dcshared{q} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = s≤′s (s≤′s (s≤′s sucnsp≰sp₁))
csteps sq≤p (dcvar{p} C⟦p⟧=C⟦p⟧c) (dcvar{q} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = s≤′s (s≤′s sucnsp≰sp₁)
csteps sq≤p (dcif₁{pp}{pr}{pq} C⟦p⟧=C⟦p⟧c) (dcif₁{qp}{qr}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith2 ∥ qp ∥s  ∥ pp ∥s  ∥ pq ∥s  sucnsp≰sp₁
csteps sq≤p (dcif₂{pp}{pr}{pq} C⟦p⟧=C⟦p⟧c) (dcif₂{qp}{qr}{qq} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith1 ∥ pp ∥s  ∥ qq ∥s  ∥ pq ∥s sucnsp≰sp₁
csteps sq≤p (dcenv{p = p1}{θ = θ} C⟦p⟧=C⟦p⟧c) (dcenv{p = p2} C⟦q⟧=C⟦q⟧c)
  with csteps sq≤p C⟦p⟧=C⟦p⟧c C⟦q⟧=C⟦q⟧c
... | sucnsp≰sp₁ = arith3  ∥ p2 ∥s  ∥ p1 ∥s (numstepsθ θ) sucnsp≰sp₁

noetherian : ∀ {p q} ->
  p sn⟶ q ->
  (suc (∥ q ∥s)) ≤′ (∥ p ∥s)
noetherian (rcontext C dc pinsn⟶₁qin) =
  csteps (noetherian₁ pinsn⟶₁qin) dc Crefl 
