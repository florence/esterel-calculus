{-
Basic properties of the Can function and utilities used in the reasoning.


The basic properties of the Can function include


- Can-θ function shadows the environment


    canθ-shadowing-irr' : ∀ sigs' S'' p S status θ θo →
      S ∈ map (_+_ S'') (SigMap.keys sigs') →
        Canθ sigs' S'' p ((θ ← [ (S ₛ) ↦ status ]) ← θo) ≡
        Canθ sigs' S'' p (θ ← θo)

    canθ-shadowing-irr : ∀ sigs' S'' p S status θ →
      Signal.unwrap S ∈ map (_+_ S'') (SigMap.keys sigs') →
        Canθ sigs' S'' p θ ≡
        Canθ sigs' S'' p (θ ← [ S ↦ status ])


- Can only look at signals in the environment. Actually, if we define Can on top
  of SigMap instead of the whole Env, this would be unnecessary:

  can-shr-var-irr : ∀ p θ θ' →
    Env.sig θ ≡ Env.sig θ' →
    Can p θ ≡ Can p θ'


- term-nothing captures those terms that cause a side-effect and reduce to nothin.

  canₖ-term-nothin : ∀ {r} θ → term-nothin r → Canₖ r θ ≡ (Code.nothin ∷ [])

  So the result of the Can function will not change:

  canₖ-term-nothin-lemma : ∀ {r₁ r₂} θ E →
    term-nothin r₁ → term-nothin r₂ →
    ∀ k →
      k ∈ Canₖ (E ⟦ r₁ ⟧e) θ →
      k ∈ Canₖ (E ⟦ r₂ ⟧e) θ



- paused terms have return code pause.

  canₖ-paused : ∀ {p} θ → paused p → Canₖ p θ ≡ (Code.pause ∷ [])


- done terms basically do nothing -- their Canₛ and Canₛₕ are empty.

  canₛ-done : ∀ {p} θ → done p → Canₛ p θ ≡ []


- Canₛ and Canₛₕ only captures free variables -- bound variables are removed. This
  property has a weaker converse: emit S and s ⇐ e in some *evaluation context*
  will be captured by Can.

  canₛ-⊆-FV-lemma : ∀ {p BV FV} θ →
    CorrectBinding p BV FV →
    ∀ S →
      S ∈ Canₛ p θ →
      S ∈ proj₁ FV

  (and its canₛₕ counterpart)

  canₛ-capture-emit-signal : ∀ {p S E} θ →
    p ≐ E ⟦ emit S ⟧e →
    Signal.unwrap S ∈ Canₛ p θ

  canₛₕ-capture-set-shared : ∀ {p s e E} θ →
    p ≐ E ⟦ s ⇐ e ⟧e →
    SharedVar.unwrap s ∈ Canₛₕ p θ


- Subset relation of Can bubbles up through Canθ (a weaker version). Note that
  the lemmas for codes and shared variables requires subset relation of the
  signals as well.

  canθₛ-subset : ∀ sigs S'' p q θ →
    (∀ θ' S →
       Signal.unwrap S ∈ Canₛ p θ' →
       Signal.unwrap S ∈ Canₛ q θ') →
    ∀ S →
      Signal.unwrap S ∈ Canθₛ sigs S'' p θ →
      Signal.unwrap S ∈ Canθₛ sigs S'' q θ

  canθₛₕ-subset : ∀ sigs S'' p q θ →
    (∀ θ' S →
       Signal.unwrap S ∈ Canₛ p θ' →
       Signal.unwrap S ∈ Canₛ q θ') →
    (∀ θ' s →
       SharedVar.unwrap s ∈ Canₛₕ p θ' →
       SharedVar.unwrap s ∈ Canₛₕ q θ') →
    ∀ s →
      SharedVar.unwrap s ∈ Canθₛₕ sigs S'' p θ →
      SharedVar.unwrap s ∈ Canθₛₕ sigs S'' q θ

  canθ'ₛ-subset-lemma : ∀ sigs S'' κ κ' θ →
    (∀ θ' S → S ∈ proj₁ (κ θ') → S ∈ proj₁ (κ' θ')) →
    (∀ θ S status S' →
      S' ∈ proj₁ (κ' (θ ← Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty)) →
      S' ∈ proj₁ (κ' (θ ← [S]-env S))) →
    ∀ S → S ∈ proj₁ (Canθ' sigs S'' κ θ) → S ∈ proj₁ (Canθ' sigs S'' κ' θ)


- Certain type of mootonicity relationship between the Can-θ function
  and the evaluation context

    canθₛ-p⊆canθₛ-E₁⟦p⟧ : ∀ sigs S'' θ E₁ pin →
      ∀ S' →
        Signal.unwrap S' ∈ Canθₛ sigs S'' pin θ →
        Signal.unwrap S' ∈ Canθₛ sigs S'' ((E₁ ∷ []) ⟦ pin ⟧e) θ

    canθₛ-E₁⟦p⟧⊆canθₛ-p : ∀ {pin E₁ E₁⟦nothin⟧ BV FV} sigs S'' θ →
      E₁⟦nothin⟧ ≐ (E₁ ∷ []) ⟦ nothin ⟧e →
      CorrectBinding E₁⟦nothin⟧ BV FV →

      distinct' (map (_+_ S'') (SigMap.keys sigs)) (proj₁ FV) →
      ∀ S' →
        Signal.unwrap S' ∉ proj₁ FV →
        Signal.unwrap S' ∈ Canθₛ sigs S'' ((E₁ ∷ []) ⟦ pin ⟧e) θ →
        Signal.unwrap S' ∈ Canθₛ sigs S'' pin θ

-}
module Esterel.Lang.CanFunction.Base where

open import utility
  renaming (_U̬_ to _∪_ ; _|̌_ to _-_)

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.CanFunction
open import Esterel.Lang.CanFunction.SetSigMonotonic public -- weird dependency here
open import Esterel.Lang.Properties
  using (halted ; paused ; done)
open import Esterel.Context
  using (EvaluationContext1 ; EvaluationContext ; _⟦_⟧e ; _≐_⟦_⟧e)
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

open EvaluationContext1
open _≐_⟦_⟧e

open import Data.Bool
  using (Bool ; not ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.List.Properties
  using (map-id)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using (++⁻)
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ)
open import Data.Maybe
  using (Maybe ; maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_)
open import Data.Nat.Properties.Simple
  using (+-comm ; +-right-identity)
open import Data.Product
  using (Σ ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; id ; _∋_ ; _$_)
open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; sym ; cong ; subst)

open halted
open paused
open done

open ListSet Data.Nat._≟_
  using (set-subtract ; set-subtract-[] ; set-subtract-merge ;  set-subtract-split ;
         set-remove ; set-remove-removed ; set-remove-mono-∈ ; set-remove-not-removed ;
         set-subtract-[a]≡set-remove)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

-- Shorter local notation used in Can lemmas
[_↦_] : Signal → Signal.Status → Env
[ S ↦ status ] = Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty

data term-nothin : Term → Set where
  tnothin : term-nothin nothin
  temit : ∀ S → term-nothin (emit S)
  tset-shr : ∀ s e → term-nothin (s ⇐ e)
  tset-var : ∀ x e → term-nothin (x ≔ e)


data term-raise : ShrMap.Map (SharedVar.Status × ℕ) → VarMap.Map ℕ → Term → Term → Set where
  tshared : ∀ n s e p →
    term-raise ShrMap.[ s ↦ (SharedVar.old ,′ n) ]
           VarMap.empty
           (shared s ≔ e in: p) p
  tvar : ∀ n x e p →
    term-raise ShrMap.empty
           VarMap.[ x ↦ n ]
           (var x ≔ e in: p)    p


canₖ-term-nothin : ∀ {r} θ → term-nothin r → Canₖ r θ ≡ (Code.nothin ∷ [])
canₖ-term-nothin θ tnothin = refl
canₖ-term-nothin θ (temit S) = refl
canₖ-term-nothin θ (tset-shr s e) = refl
canₖ-term-nothin θ (tset-var x e) = refl


canₖ-paused : ∀ {p} θ → paused p → Canₖ p θ ≡ (Code.pause ∷ [])
canₖ-paused θ ppause                                             = refl
canₖ-paused θ (psuspend p/paused) rewrite canₖ-paused θ p/paused = refl
canₖ-paused θ (ptrap p/paused) rewrite canₖ-paused θ p/paused    = refl
canₖ-paused θ (ppar p/paused q/paused)
  rewrite canₖ-paused θ p/paused | canₖ-paused θ q/paused
  = refl
canₖ-paused {p >> q} θ (pseq p/paused) with any (Code._≟_ Code.nothin) (Canₖ p θ)
... | no nothin∉can-p rewrite canₖ-paused θ p/paused = refl
... | yes nothin∈can-p rewrite canₖ-paused θ p/paused with nothin∈can-p
... | here ()
... | there ()

canₖ-paused {loopˢ p q} θ (ploopˢ p/paused) = canₖ-paused θ p/paused

canₛ-done : ∀ {p} θ → done p → Canₛ p θ ≡ []
canₛ-done θ (dhalted hnothin)   = refl
canₛ-done θ (dhalted (hexit _)) = refl
canₛ-done θ (dpaused ppause) = refl
canₛ-done θ (dpaused (ppar p/paused q/paused))
  rewrite canₛ-done θ (dpaused p/paused) | canₛ-done θ (dpaused q/paused)
  = refl
canₛ-done θ (dpaused (psuspend p/paused))
  rewrite canₛ-done θ (dpaused p/paused)
  = refl
canₛ-done θ (dpaused (ptrap p/paused))
  rewrite canₛ-done θ (dpaused p/paused)
  = refl
canₛ-done {loopˢ p q} θ (dpaused (ploopˢ p/paused)) = canₛ-done θ (dpaused p/paused)
canₛ-done {p >> q} θ (dpaused (pseq p/paused)) with any (Code._≟_ Code.nothin) (Canₖ p θ)
... | no  nothin∉can-p rewrite canₛ-done θ (dpaused p/paused) = refl
... | yes nothin∈can-p rewrite canₖ-paused θ p/paused with nothin∈can-p
... | here ()
... | there ()


canₛₕ-done : ∀ {p} θ → done p → Canₛₕ p θ ≡ []
canₛₕ-done θ (dhalted hnothin)   = refl
canₛₕ-done θ (dhalted (hexit _)) = refl
canₛₕ-done θ (dpaused ppause) = refl
canₛₕ-done θ (dpaused (ppar p/paused q/paused))
  rewrite canₛₕ-done θ (dpaused p/paused) | canₛₕ-done θ (dpaused q/paused)
  = refl
canₛₕ-done θ (dpaused (psuspend p/paused))
  rewrite canₛₕ-done θ (dpaused p/paused)
  = refl
canₛₕ-done θ (dpaused (ptrap p/paused))
  rewrite canₛₕ-done θ (dpaused p/paused)
  = refl
canₛₕ-done {loopˢ p q} θ (dpaused (ploopˢ p/paused)) = canₛₕ-done θ (dpaused p/paused)
canₛₕ-done {p >> q} θ (dpaused (pseq p/paused)) with any (Code._≟_ Code.nothin) (Canₖ p θ)
... | no  nothin∉can-p rewrite canₛₕ-done θ (dpaused p/paused) = refl
... | yes nothin∈can-p rewrite canₖ-paused θ p/paused with nothin∈can-p
... | here ()
... | there ()


can-shr-var-irr : ∀ p θ θ' →
  Env.sig θ ≡ Env.sig θ' →
  Can p θ ≡ Can p θ'

canθ-shr-var-irr : ∀ sigs S'' p θ θ' →
  Env.sig θ ≡ Env.sig θ' →
  Canθ sigs S'' p θ ≡ Canθ sigs S'' p θ'
canθ-shr-var-irr [] S'' p θ θ' θₛ≡θ'ₛ = can-shr-var-irr p θ θ' θₛ≡θ'ₛ
canθ-shr-var-irr (just Signal.present ∷ sigs) S'' p θ θ' θₛ≡θ'ₛ
  rewrite canθ-shr-var-irr sigs (suc S'') p
            (θ  ← [S]-env-present (S'' ₛ))
            (θ' ← [S]-env-present (S'' ₛ))
            (cong (λ sig* → SigMap.union sig* (Env.sig ([S]-env-present (S'' ₛ)))) θₛ≡θ'ₛ)
  = refl
canθ-shr-var-irr (just Signal.absent  ∷ sigs)  S'' p θ θ' θₛ≡θ'ₛ
  rewrite canθ-shr-var-irr sigs (suc S'') p
            (θ  ← [S]-env-absent (S'' ₛ))
            (θ' ← [S]-env-absent (S'' ₛ))
            (cong (λ sig* → SigMap.union sig* (Env.sig ([S]-env-absent (S'' ₛ)))) θₛ≡θ'ₛ)
  = refl
canθ-shr-var-irr (just Signal.unknown ∷ sigs) S'' p θ θ' θₛ≡θ'ₛ
  with any (S'' ≟_) (proj₁ (Canθ sigs (suc S'') p (θ  ← [S]-env (S'' ₛ))))
     | any (S'' ≟_) (proj₁ (Canθ sigs (suc S'') p (θ' ← [S]-env (S'' ₛ))))
... | yes S''∈canθ-θ←[S] | yes S''∈canθ-θ'←[S]
  rewrite canθ-shr-var-irr sigs (suc S'') p
            (θ ←  [S]-env (S'' ₛ))
            (θ' ← [S]-env (S'' ₛ))
            (cong (λ sig* → SigMap.union sig* (Env.sig ([S]-env (S'' ₛ)))) θₛ≡θ'ₛ)
  = refl
... | no  S''∉canθ-θ←[S] | no  S''∉canθ-θ'←[S]
  rewrite canθ-shr-var-irr sigs (suc S'') p
            (θ ← [S]-env-absent (S'' ₛ))
            (θ' ← [S]-env-absent (S'' ₛ))
            (cong (λ sig* → SigMap.union sig* (Env.sig ([S]-env-absent (S'' ₛ)))) θₛ≡θ'ₛ)
  = refl
... | no  S''∉canθ-θ←[S] | yes S''∈canθ-θ'←[S]
  rewrite canθ-shr-var-irr sigs (suc S'') p
            (θ ←  [S]-env (S'' ₛ))
            (θ' ← [S]-env (S'' ₛ))
            (cong (λ sig* → SigMap.union sig* (Env.sig ([S]-env (S'' ₛ)))) θₛ≡θ'ₛ)
  = ⊥-elim (S''∉canθ-θ←[S] S''∈canθ-θ'←[S])
... | yes S''∈canθ-θ←[S] | no  S''∉canθ-θ'←[S]
  rewrite canθ-shr-var-irr sigs (suc S'') p
            (θ ←  [S]-env (S'' ₛ))
            (θ' ← [S]-env (S'' ₛ))
            (cong (λ sig* → SigMap.union sig* (Env.sig ([S]-env (S'' ₛ)))) θₛ≡θ'ₛ)
  = ⊥-elim (S''∉canθ-θ'←[S] S''∈canθ-θ←[S])
canθ-shr-var-irr (nothing ∷ sigs) S'' p θ θ' θₛ≡θ'ₛ
  rewrite canθ-shr-var-irr sigs (suc S'') p θ θ' θₛ≡θ'ₛ
  = refl

can-shr-var-irr nothin θ θ' θₛ≡θ'ₛ = refl
can-shr-var-irr pause θ θ' θₛ≡θ'ₛ = refl
can-shr-var-irr (signl S p) θ θ' θₛ≡θ'ₛ
  rewrite canθ-shr-var-irr (Env.sig ([S]-env S)) 0 p θ θ' θₛ≡θ'ₛ
  = refl
can-shr-var-irr (present S ∣⇒ p ∣⇒ q) (Θ Ss ss xs) (Θ .Ss ss' xs') refl
  with Env.Sig∈ S (Θ Ss ss xs)
... | yes S∈
  rewrite can-shr-var-irr p (Θ Ss ss xs) (Θ Ss ss' xs') refl
        | can-shr-var-irr q (Θ Ss ss xs) (Θ Ss ss' xs') refl
  = refl
... | no  S∉
  rewrite can-shr-var-irr p (Θ Ss ss xs) (Θ Ss ss' xs') refl
        | can-shr-var-irr q (Θ Ss ss xs) (Θ Ss ss' xs') refl
  = refl
can-shr-var-irr (emit S) θ θ' θₛ≡θ'ₛ = refl
can-shr-var-irr (p ∥ q) θ θ' θₛ≡θ'ₛ
  rewrite can-shr-var-irr p θ θ' θₛ≡θ'ₛ
        | can-shr-var-irr q θ θ' θₛ≡θ'ₛ
  = refl
can-shr-var-irr (loop p) θ θ' θₛ≡θ'ₛ =
  can-shr-var-irr p θ θ' θₛ≡θ'ₛ
can-shr-var-irr (loopˢ p q) θ θ' θₛ≡θ'ₛ = can-shr-var-irr p θ θ' θₛ≡θ'ₛ
can-shr-var-irr (p >> q) θ θ' θₛ≡θ'ₛ
  with any (Code._≟_ Code.nothin) (Canₖ p θ)
     | any (Code._≟_ Code.nothin) (Canₖ p θ')
... | yes nothin∈can-p-θ | yes nothin∈can-p-θ'
  rewrite can-shr-var-irr p θ θ' θₛ≡θ'ₛ
        | can-shr-var-irr q θ θ' θₛ≡θ'ₛ
  = refl
... | yes nothin∈can-p-θ | (no nothin∉can-p-θ')
  rewrite can-shr-var-irr p θ θ' θₛ≡θ'ₛ
  = ⊥-elim (nothin∉can-p-θ' nothin∈can-p-θ)
... | no nothin∉can-p-θ | yes nothin∈can-p-θ'
  rewrite can-shr-var-irr p θ θ' θₛ≡θ'ₛ
  = ⊥-elim (nothin∉can-p-θ nothin∈can-p-θ')
... | no nothin∉can-p-θ | no nothin∉can-p-θ'
  rewrite can-shr-var-irr p θ θ' θₛ≡θ'ₛ
  = refl
can-shr-var-irr (suspend p S) θ θ' θₛ≡θ'ₛ =
  can-shr-var-irr p θ θ' θₛ≡θ'ₛ
can-shr-var-irr (trap p) θ θ' θₛ≡θ'ₛ
  rewrite can-shr-var-irr p θ θ' θₛ≡θ'ₛ
  = refl
can-shr-var-irr (exit x) θ θ' θₛ≡θ'ₛ = refl
can-shr-var-irr (shared s ≔ e in: p) θ θ' θₛ≡θ'ₛ
  rewrite can-shr-var-irr p θ θ' θₛ≡θ'ₛ
  = refl
can-shr-var-irr (s ⇐ e) θ θ' θₛ≡θ'ₛ = refl
can-shr-var-irr (var x ≔ e in: p) θ θ' θₛ≡θ'ₛ
  rewrite can-shr-var-irr p θ θ' θₛ≡θ'ₛ
  = refl
can-shr-var-irr (x ≔ e) θ θ' θₛ≡θ'ₛ = refl
can-shr-var-irr (if x ∣⇒ p ∣⇒ q) θ θ' θₛ≡θ'ₛ
  rewrite can-shr-var-irr p θ θ' θₛ≡θ'ₛ
        | can-shr-var-irr q θ θ' θₛ≡θ'ₛ
  = refl
can-shr-var-irr (ρ⟨ θ'' , A ⟩· p) θ θ' θₛ≡θ'ₛ
  rewrite canθ-shr-var-irr (Env.sig θ'') 0 p θ θ' θₛ≡θ'ₛ
  = refl


canₛ-capture-emit-signal : ∀ {p S E} θ →
  p ≐ E ⟦ emit S ⟧e →
  Signal.unwrap S ∈ Canₛ p θ
canₛ-capture-emit-signal θ dehole = here refl
canₛ-capture-emit-signal θ (depar₁ p≐E⟦emit⟧) =
  ++ˡ (canₛ-capture-emit-signal θ p≐E⟦emit⟧)
canₛ-capture-emit-signal {p ∥ _} θ (depar₂ p≐E⟦emit⟧) =
  ++ʳ (Canₛ p θ) (canₛ-capture-emit-signal θ p≐E⟦emit⟧)
canₛ-capture-emit-signal {loopˢ p _}  θ (deloopˢ p≐E⟦emit⟧) = canₛ-capture-emit-signal θ p≐E⟦emit⟧
canₛ-capture-emit-signal {p >> _}  θ (deseq p≐E⟦emit⟧)
  with any (Code._≟_ Code.nothin) (Canₖ p θ)
... | yes nothin∈can-p = ++ˡ (canₛ-capture-emit-signal θ p≐E⟦emit⟧)
... | no  nothin∉can-p = canₛ-capture-emit-signal θ p≐E⟦emit⟧
canₛ-capture-emit-signal θ (desuspend p≐E⟦emit⟧) =
  canₛ-capture-emit-signal θ p≐E⟦emit⟧
canₛ-capture-emit-signal θ (detrap p≐E⟦emit⟧) =
  canₛ-capture-emit-signal θ p≐E⟦emit⟧


canₛₕ-capture-set-shared : ∀ {p s e E} θ →
  p ≐ E ⟦ s ⇐ e ⟧e →
  SharedVar.unwrap s ∈ Canₛₕ p θ
canₛₕ-capture-set-shared θ dehole = here refl
canₛₕ-capture-set-shared θ (depar₁ p≐E⟦s⇐e⟧) =
  ++ˡ (canₛₕ-capture-set-shared θ p≐E⟦s⇐e⟧)
canₛₕ-capture-set-shared {p ∥ _} θ (depar₂ q≐E⟦s⇐e⟧) =
  ++ʳ (Canₛₕ p θ) (canₛₕ-capture-set-shared θ q≐E⟦s⇐e⟧)
canₛₕ-capture-set-shared {loopˢ p _} θ (deloopˢ p≐E⟦s⇐e⟧) = canₛₕ-capture-set-shared θ p≐E⟦s⇐e⟧
canₛₕ-capture-set-shared {p >> _} θ (deseq p≐E⟦s⇐e⟧)
  with any (Code._≟_ Code.nothin) (Canₖ p θ)
... | yes nothin∈can-p = ++ˡ (canₛₕ-capture-set-shared θ p≐E⟦s⇐e⟧)
... | no  nothin∉can-p = canₛₕ-capture-set-shared θ p≐E⟦s⇐e⟧
canₛₕ-capture-set-shared θ (desuspend p≐E⟦s⇐e⟧) =
  canₛₕ-capture-set-shared θ p≐E⟦s⇐e⟧
canₛₕ-capture-set-shared θ (detrap p≐E⟦s⇐e⟧) =
  canₛₕ-capture-set-shared θ p≐E⟦s⇐e⟧


canθₛ-membership : ∀ sigs S'' p θ S →
  (∀ θ' → Signal.unwrap S ∈ Canₛ p θ') →
  Signal.unwrap S ∈ Canθₛ sigs S'' p θ
canθₛ-membership [] S'' p θ S S∈can-p = S∈can-p θ
canθₛ-membership (nothing ∷ sigs) S'' p θ S S∈can-p =
  canθₛ-membership sigs (suc S'') p θ S S∈can-p
canθₛ-membership (just Signal.present ∷ sigs) S'' p θ S S∈can-p =
  canθₛ-membership sigs (suc S'') p (θ ← [S]-env-present (S'' ₛ)) S S∈can-p
canθₛ-membership (just Signal.absent ∷ sigs) S'' p θ S S∈can-p =
  canθₛ-membership sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) S S∈can-p
canθₛ-membership (just Signal.unknown ∷ sigs) S'' p θ S S∈can-p
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-p-θ←[S''] =
  canθₛ-membership sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) S S∈can-p
... | no  S''∉canθ-p-θ←[S''] =
  canθₛ-membership sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) S S∈can-p


canθₛₕ-membership : ∀ sigs S'' p θ s →
  (∀ θ' → SharedVar.unwrap s ∈ Canₛₕ p θ') →
  SharedVar.unwrap s ∈ Canθₛₕ sigs S'' p θ
canθₛₕ-membership [] S'' p θ s s∈can-p = s∈can-p θ
canθₛₕ-membership (nothing ∷ sigs) S'' p θ s s∈can-p =
  canθₛₕ-membership sigs (suc S'') p θ s s∈can-p
canθₛₕ-membership (just Signal.present ∷ sigs) S'' p θ s s∈can-p =
  canθₛₕ-membership sigs (suc S'') p (θ ← [S]-env-present (S'' ₛ)) s s∈can-p
canθₛₕ-membership (just Signal.absent ∷ sigs) S'' p θ s s∈can-p =
  canθₛₕ-membership sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) s s∈can-p
canθₛₕ-membership (just Signal.unknown ∷ sigs) S'' p θ s s∈can-p
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-p-θ←[S''] =
  canθₛₕ-membership sigs (suc S'') p (θ ← [S]-env (S'' ₛ)) s s∈can-p
... | no  S''∉canθ-p-θ←[S''] =
  canθₛₕ-membership sigs (suc S'') p (θ ← [S]-env-absent (S'' ₛ)) s s∈can-p


canₛ-⊆-FV-lemma : ∀ {p BV FV} θ →
  CorrectBinding p BV FV →
  ∀ S →
    S ∈ Canₛ p θ →
    S ∈ proj₁ FV

canθₛ-⊆-FV-lemma : ∀ {p BV FV} sigs S'' θ →
  CorrectBinding p BV FV →
  ∀ S →
    S ∈ proj₁ (Canθ sigs S'' p θ) →
    S ∈ proj₁ FV
canθₛ-⊆-FV-lemma {FV = FV} [] S'' θ cb S S∈canθ-p-θ =
  canₛ-⊆-FV-lemma θ cb S S∈canθ-p-θ
canθₛ-⊆-FV-lemma (just Signal.present ∷ sigs) S'' θ cb S S∈canθ-p-θ =
  canθₛ-⊆-FV-lemma sigs (suc S'') (θ ← [S]-env-present (S'' ₛ)) cb S S∈canθ-p-θ
canθₛ-⊆-FV-lemma (just Signal.absent  ∷ sigs) S'' θ cb S S∈canθ-p-θ =
  canθₛ-⊆-FV-lemma sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) cb S S∈canθ-p-θ
canθₛ-⊆-FV-lemma {p} (just Signal.unknown ∷ sigs) S'' θ cb S S∈canθ-p-θ
  with any (S'' ≟_) (proj₁ (Canθ sigs (suc S'') p (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ-p-θ←[S] =
  canθₛ-⊆-FV-lemma sigs (suc S'') (θ ← [S]-env (S'' ₛ)) cb S S∈canθ-p-θ
... | no  S''∉canθ-p-θ←[S] =
  canθₛ-⊆-FV-lemma sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) cb S S∈canθ-p-θ
canθₛ-⊆-FV-lemma (nothing ∷ sigs) S'' θ cb S S∈canθ-p-θ =
  canθₛ-⊆-FV-lemma sigs (suc S'') θ cb S S∈canθ-p-θ

canₛ-⊆-FV-lemma θ CBnothing S ()
canₛ-⊆-FV-lemma θ CBpause S ()
canₛ-⊆-FV-lemma {signl S' p} θ (CBsig {FV = FV} cb) S S∈can-sig-p
  with Signal.unwrap S' Data.Nat.≟ S
... | yes refl =
  ⊥-elim (set-remove-removed {S} {Canθₛ (Env.sig ([S]-env S')) 0 p θ} S∈can-sig-p)
... | no  S'≢S
  rewrite set-subtract-[a]≡set-remove (proj₁ FV) (Signal.unwrap S')
  = set-remove-not-removed S'≢S
    (canθₛ-⊆-FV-lemma (Env.sig ([S]-env S')) 0 θ cb S
      (set-remove-mono-∈ (Signal.unwrap S') S∈can-sig-p))
canₛ-⊆-FV-lemma {present S' ∣⇒ p ∣⇒ q} θ (CBpresent {FVp = FVp} cbp cbq) S S∈can-S'?p:q
  with Env.Sig∈ S' θ
canₛ-⊆-FV-lemma {present S' ∣⇒ p ∣⇒ q} θ (CBpresent {FVp = FVp} cbp cbq) S S∈can-S'ᵘ?p:q
  | no  S'∉Domθ with ++⁻ (Canₛ p θ) S∈can-S'ᵘ?p:q
... | inj₁ S∈can-p = ++ʳ (Signal.unwrap S' ∷  []) (++ˡ (canₛ-⊆-FV-lemma θ cbp S S∈can-p))
... | inj₂ S∈can-q = ++ʳ (Signal.unwrap S' ∷ proj₁ FVp) (canₛ-⊆-FV-lemma θ cbq S S∈can-q)
canₛ-⊆-FV-lemma {present S' ∣⇒ p ∣⇒ q} θ (CBpresent {FVp = FVp} cbp cbq) S S∈can-S'ᵘ?p:q
  | yes S'∈Domθ with Env.sig-stats {S'} θ S'∈Domθ
... | Signal.present = ++ʳ (Signal.unwrap S' ∷  []) (++ˡ (canₛ-⊆-FV-lemma θ cbp S S∈can-S'ᵘ?p:q))
... | Signal.absent  = ++ʳ (Signal.unwrap S' ∷ proj₁ FVp) (canₛ-⊆-FV-lemma θ cbq S S∈can-S'ᵘ?p:q)
... | Signal.unknown with ++⁻ (Canₛ p θ) S∈can-S'ᵘ?p:q
... | inj₁ S∈can-p = ++ʳ (Signal.unwrap S' ∷  []) (++ˡ (canₛ-⊆-FV-lemma θ cbp S S∈can-p))
... | inj₂ S∈can-q = ++ʳ (Signal.unwrap S' ∷ proj₁ FVp) (canₛ-⊆-FV-lemma θ cbq S S∈can-q)
canₛ-⊆-FV-lemma θ CBemit S S∈can-p = S∈can-p
canₛ-⊆-FV-lemma {p ∥ q} θ (CBpar {FVp = FVp} cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) S S∈can-p∥q
  with ++⁻ (Canₛ p θ) S∈can-p∥q
... | inj₁ S∈can-p = ++ˡ (canₛ-⊆-FV-lemma θ cbp S S∈can-p)
... | inj₂ S∈can-q = ++ʳ (proj₁ FVp) (canₛ-⊆-FV-lemma θ cbq S S∈can-q)
canₛ-⊆-FV-lemma θ (CBloop cb BV≠FV) S S∈can-p =
  canₛ-⊆-FV-lemma θ cb S S∈can-p
canₛ-⊆-FV-lemma θ (CBloopˢ CBp CBq BVp≠FVq BVq≠FVq) S S∈can-loopˢp
  with canₛ-⊆-FV-lemma θ CBp S S∈can-loopˢp
... | sub = ++ˡ sub
canₛ-⊆-FV-lemma {p >> q} θ (CBseq {FVp = FVp} cbp cbq BVp≠FVq) S S∈can-p>>q
  with any (Code._≟_ Code.nothin) (Canₖ p θ)
... | no  nothin∉can-p = ++ˡ (canₛ-⊆-FV-lemma θ cbp S S∈can-p>>q)
... | yes nothin∈can-p with ++⁻ (Canₛ p θ) S∈can-p>>q
... | inj₁ S∈can-p = ++ˡ (canₛ-⊆-FV-lemma θ cbp S S∈can-p)
... | inj₂ S∈can-q = ++ʳ (proj₁ FVp) (canₛ-⊆-FV-lemma θ cbq S S∈can-q)
canₛ-⊆-FV-lemma θ (CBsusp cb [S]≠BVp) S S∈can-p =
  there (canₛ-⊆-FV-lemma θ cb S S∈can-p)
canₛ-⊆-FV-lemma θ CBexit S ()
canₛ-⊆-FV-lemma θ (CBtrap cb) S S∈can-p =
  canₛ-⊆-FV-lemma θ cb S S∈can-p
canₛ-⊆-FV-lemma {shared _ ≔ e in: _} θ (CBshared {FV = FV} cb) S S∈can-p
  rewrite set-subtract-[] (proj₁ FV)
  = ++ʳ (proj₁ (FVₑ e)) (canₛ-⊆-FV-lemma θ cb S S∈can-p)
canₛ-⊆-FV-lemma θ CBsset S ()
canₛ-⊆-FV-lemma {var _ ≔ e in: _} θ (CBvar {FV = FV} cb) S S∈can-p
  rewrite set-subtract-[] (proj₁ FV)
  = ++ʳ (proj₁ (FVₑ e)) (canₛ-⊆-FV-lemma θ cb S S∈can-p)
canₛ-⊆-FV-lemma θ CBvset S ()
canₛ-⊆-FV-lemma {if _ ∣⇒ p ∣⇒ q} θ (CBif {FVp = FVp} cbp cbq) S S∈can-if-p-q
  with ++⁻ (Canₛ p θ) S∈can-if-p-q
... | inj₁ S∈can-p = ++ˡ (canₛ-⊆-FV-lemma θ cbp S S∈can-p)
... | inj₂ S∈can-q = ++ʳ (proj₁ FVp) (canₛ-⊆-FV-lemma θ cbq S S∈can-q)
canₛ-⊆-FV-lemma {ρ⟨ θ' , A ⟩· p} θ (CBρ cb) S S∈can-ρθp
  with set-subtract-merge {proj₁ (Canθ (Env.sig θ') 0 p θ)} {proj₁ (Dom θ')} S∈can-ρθp
... | S∈can-p-θ←θ' , S∉Domθ'
  with set-subtract-split (canθₛ-⊆-FV-lemma (Env.sig θ') 0 θ cb S S∈can-p-θ←θ')
... | inj₁ S∈FV = S∈FV
... | inj₂ S∈Domθ' = ⊥-elim (S∉Domθ' S∈Domθ')


canₛ-⊆-FV : ∀ {p BV FV} θ →
  CorrectBinding p BV FV →
  ∀ S →
    Signal.unwrap S ∈ Canₛ p θ →
    Signal.unwrap S ∈ proj₁ FV
canₛ-⊆-FV θ cb S = canₛ-⊆-FV-lemma θ cb (Signal.unwrap S)


canₛₕ-⊆-FV-lemma : ∀ {p BV FV} θ →
  CorrectBinding p BV FV →
  ∀ s →
    s ∈ Canₛₕ p θ →
    s ∈ proj₁ (proj₂ FV)

canθₛₕ-⊆-FV-lemma : ∀ {p BV FV} sigs S'' θ →
  CorrectBinding p BV FV →
  ∀ s →
    s ∈ proj₂ (proj₂ (Canθ sigs S'' p θ)) →
    s ∈ proj₁ (proj₂ FV)
canθₛₕ-⊆-FV-lemma {FV = FV} [] S'' θ cb s s∈canθ-p-θ =
  canₛₕ-⊆-FV-lemma θ cb s s∈canθ-p-θ
canθₛₕ-⊆-FV-lemma (just Signal.present ∷ sigs) S'' θ cb s s∈canθ-p-θ =
  canθₛₕ-⊆-FV-lemma sigs (suc S'') (θ ← [S]-env-present (S'' ₛ)) cb s s∈canθ-p-θ
canθₛₕ-⊆-FV-lemma (just Signal.absent  ∷ sigs) S'' θ cb s s∈canθ-p-θ =
  canθₛₕ-⊆-FV-lemma sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) cb s s∈canθ-p-θ
canθₛₕ-⊆-FV-lemma {p} (just Signal.unknown ∷ sigs) S'' θ cb s s∈canθ-p-θ
  with any (S'' ≟_) (proj₁ (Canθ sigs (suc S'') p (θ ← [S]-env (S'' ₛ))))
... | yes S''∈canθ-p-θ←[S] =
  canθₛₕ-⊆-FV-lemma sigs (suc S'') (θ ← [S]-env (S'' ₛ)) cb s s∈canθ-p-θ
... | no  S''∉canθ-p-θ←[S] =
  canθₛₕ-⊆-FV-lemma sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) cb s s∈canθ-p-θ
canθₛₕ-⊆-FV-lemma (nothing ∷ sigs) S'' θ cb s s∈canθ-p-θ =
  canθₛₕ-⊆-FV-lemma sigs (suc S'') θ cb s s∈canθ-p-θ

canₛₕ-⊆-FV-lemma θ CBnothing s ()
canₛₕ-⊆-FV-lemma θ CBpause s ()
canₛₕ-⊆-FV-lemma {signl S' p} θ (CBsig {FV = FV} cb) s s∈can-p
  rewrite set-subtract-[] (proj₁ (proj₂ FV))
  = canθₛₕ-⊆-FV-lemma (Env.sig ([S]-env S')) 0 θ cb s s∈can-p
canₛₕ-⊆-FV-lemma {present S' ∣⇒ p ∣⇒ q} θ (CBpresent {FVp = FVp} cbp cbq) s s∈can-S'?p:q
  with Env.Sig∈ S' θ
canₛₕ-⊆-FV-lemma {present S' ∣⇒ p ∣⇒ q} θ (CBpresent {FVp = FVp} cbp cbq) s s∈can-S'ᵘ?p:q
  | no  S'∉Domθ with ++⁻ (Canₛₕ p θ) s∈can-S'ᵘ?p:q
... | inj₁ s∈can-p = ++ˡ (canₛₕ-⊆-FV-lemma θ cbp s s∈can-p)
... | inj₂ s∈can-q = ++ʳ (proj₁ (proj₂ FVp)) (canₛₕ-⊆-FV-lemma θ cbq s s∈can-q)
canₛₕ-⊆-FV-lemma {present S' ∣⇒ p ∣⇒ q} θ (CBpresent {FVp = FVp} cbp cbq) s s∈can-S'ᵘ?p:q
  | yes S'∈Domθ with Env.sig-stats {S'} θ S'∈Domθ
... | Signal.present = ++ˡ (canₛₕ-⊆-FV-lemma θ cbp s s∈can-S'ᵘ?p:q)
... | Signal.absent  = ++ʳ (proj₁ (proj₂ FVp)) (canₛₕ-⊆-FV-lemma θ cbq s s∈can-S'ᵘ?p:q)
... | Signal.unknown with ++⁻ (Canₛₕ p θ) s∈can-S'ᵘ?p:q
... | inj₁ s∈can-p = ++ˡ (canₛₕ-⊆-FV-lemma θ cbp s s∈can-p)
... | inj₂ s∈can-q = ++ʳ (proj₁ (proj₂ FVp)) (canₛₕ-⊆-FV-lemma θ cbq s s∈can-q)
canₛₕ-⊆-FV-lemma θ CBemit s ()
canₛₕ-⊆-FV-lemma {p ∥ q} θ (CBpar {FVp = FVp} cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) s s∈can-p∥q
  with ++⁻ (Canₛₕ p θ) s∈can-p∥q
... | inj₁ s∈can-p = ++ˡ (canₛₕ-⊆-FV-lemma θ cbp s s∈can-p)
... | inj₂ s∈can-q = ++ʳ (proj₁ (proj₂ FVp)) (canₛₕ-⊆-FV-lemma θ cbq s s∈can-q)
canₛₕ-⊆-FV-lemma θ (CBloop cb BV≠FV) s s∈can-p =
  canₛₕ-⊆-FV-lemma θ cb s s∈can-p
canₛₕ-⊆-FV-lemma θ (CBloopˢ CBp CBq BVp≠FVq BVq≠FVq) s s∈can-loopˢpq
  with canₛₕ-⊆-FV-lemma θ CBp s s∈can-loopˢpq
... | sub = ++ˡ sub
canₛₕ-⊆-FV-lemma {p >> q} θ (CBseq {FVp = FVp} cbp cbq BVp≠FVq) s s∈can-p>>q
  with any (Code._≟_ Code.nothin) (Canₖ p θ)
... | no  nothin∉can-p = ++ˡ (canₛₕ-⊆-FV-lemma θ cbp s s∈can-p>>q)
... | yes nothin∈can-p with ++⁻ (Canₛₕ p θ) s∈can-p>>q
... | inj₁ s∈can-p = ++ˡ (canₛₕ-⊆-FV-lemma θ cbp s s∈can-p)
... | inj₂ s∈can-q = ++ʳ (proj₁ (proj₂ FVp)) (canₛₕ-⊆-FV-lemma θ cbq s s∈can-q)
canₛₕ-⊆-FV-lemma θ (CBsusp cb [S]≠BVp) s s∈can-p =
  canₛₕ-⊆-FV-lemma θ cb s s∈can-p
canₛₕ-⊆-FV-lemma θ CBexit s ()
canₛₕ-⊆-FV-lemma θ (CBtrap cb) s s∈can-p =
  canₛₕ-⊆-FV-lemma θ cb s s∈can-p
canₛₕ-⊆-FV-lemma {shared s' ≔ e in: p} θ (CBshared {FV = FV} cb) s s∈can-shared-p
  with SharedVar.unwrap s' Data.Nat.≟ s
... | yes refl = ⊥-elim (set-remove-removed {s} {Canₛₕ p θ} s∈can-shared-p)
... | no  s'≢s
  rewrite set-subtract-[a]≡set-remove (proj₁ (proj₂ FV)) (SharedVar.unwrap s')
  = ++ʳ (proj₁ (proj₂ (FVₑ e)))
    (set-remove-not-removed s'≢s
      (canₛₕ-⊆-FV-lemma θ cb s
        (set-remove-mono-∈ (SharedVar.unwrap s') s∈can-shared-p)))
canₛₕ-⊆-FV-lemma {s' ⇐ e} θ CBsset s s∈can-p = ++ˡ s∈can-p
canₛₕ-⊆-FV-lemma {var _ ≔ e in: _} θ (CBvar {FV = FV} cb) s s∈can-p
  rewrite set-subtract-[] (proj₁ (proj₂ FV))
  = ++ʳ (proj₁ (proj₂ (FVₑ e))) (canₛₕ-⊆-FV-lemma θ cb s s∈can-p)
canₛₕ-⊆-FV-lemma θ CBvset s ()
canₛₕ-⊆-FV-lemma {if _ ∣⇒ p ∣⇒ q} θ (CBif {FVp = FVp} cbp cbq) s s∈can-if-p-q
  with ++⁻ (Canₛₕ p θ) s∈can-if-p-q
... | inj₁ s∈can-p = ++ˡ (canₛₕ-⊆-FV-lemma θ cbp s s∈can-p)
... | inj₂ s∈can-q = ++ʳ (proj₁ (proj₂ FVp)) (canₛₕ-⊆-FV-lemma θ cbq s s∈can-q)
canₛₕ-⊆-FV-lemma {ρ⟨ θ' , A ⟩· p} θ (CBρ cb) s s∈can-ρθp
  with set-subtract-merge
         {proj₂ (proj₂ (Canθ (Env.sig θ') 0 p θ))}
         {proj₁ (proj₂ (Dom θ'))}
         s∈can-ρθp
... | s∈can-p-θ←θ' , s∉Domθ'
  with set-subtract-split (canθₛₕ-⊆-FV-lemma (Env.sig θ') 0 θ cb s s∈can-p-θ←θ')
... | inj₁ s∈FV = s∈FV
... | inj₂ s∈Domθ' = ⊥-elim (s∉Domθ' s∈Domθ')


canₛₕ-⊆-FV : ∀ {p BV FV} θ →
  CorrectBinding p BV FV →
  ∀ s →
    SharedVar.unwrap s ∈ Canₛₕ p θ →
    SharedVar.unwrap s ∈ proj₁ (proj₂ FV)
canₛₕ-⊆-FV θ cb s = canₛₕ-⊆-FV-lemma θ cb (SharedVar.unwrap s)

canₖ-term-nothin-lemma : ∀ {r₁ r₂} θ E →
  term-nothin r₁ → term-nothin r₂ →
  ∀ k →
    k ∈ Canₖ (E ⟦ r₁ ⟧e) θ →
    k ∈ Canₖ (E ⟦ r₂ ⟧e) θ
canₖ-term-nothin-lemma θ [] r₁' r₂' k k∈can-E⟦r2⟧-θ'
  rewrite canₖ-term-nothin θ r₁' | canₖ-term-nothin θ r₂' = k∈can-E⟦r2⟧-θ'
canₖ-term-nothin-lemma θ (epar₁ q ∷ E) r₁' r₂' k k∈can-E⟦r2⟧-θ' =
  map-mono² Code._⊔_
    (canₖ-term-nothin-lemma θ E r₁' r₂')
    (λ _ → id)
    k k∈can-E⟦r2⟧-θ'
canₖ-term-nothin-lemma θ (epar₂ p ∷ E) r₁' r₂' k k∈can-E⟦r2⟧-θ' =
  map-mono² {xs = Canₖ p θ} Code._⊔_
    (λ _ → id)
    (canₖ-term-nothin-lemma θ E r₁' r₂')
    k
    k∈can-E⟦r2⟧-θ'
canₖ-term-nothin-lemma {r₁} {r₂} θ (eloopˢ q ∷ E) r₁' r₂' k k∈can-E⟦r2⟧-θ' = canₖ-term-nothin-lemma θ E r₁' r₂' k k∈can-E⟦r2⟧-θ'
canₖ-term-nothin-lemma {r₁} {r₂} θ (eseq q ∷ E) r₁' r₂' k k∈can-E⟦r2⟧-θ'
  with any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r₁ ⟧e) θ)
     | any (Code._≟_ Code.nothin) (Canₖ (E ⟦ r₂ ⟧e) θ)
... | yes nothin∈can-E⟦r₁⟧ | no  nothin∉can-E⟦r₂⟧ =
  ⊥-elim (nothin∉can-E⟦r₂⟧ (canₖ-term-nothin-lemma θ E r₁' r₂' Code.nothin nothin∈can-E⟦r₁⟧))
... | no  nothin∉can-E⟦r₁⟧ | yes nothin∈can-E⟦r₂⟧ =
  ⊥-elim (nothin∉can-E⟦r₁⟧ (canₖ-term-nothin-lemma θ E r₂' r₁' Code.nothin nothin∈can-E⟦r₂⟧))
... | no  nothin∉can-E⟦r₁⟧ | no  nothin∉can-E⟦r₂⟧ =
  canₖ-term-nothin-lemma θ E r₁' r₂' k k∈can-E⟦r2⟧-θ'
... | yes nothin∈can-E⟦r₁⟧ | yes nothin∈can-E⟦r₂⟧
  with ++⁻ (CodeSet.set-remove (Canₖ (E ⟦ r₁ ⟧e) θ) Code.nothin) k∈can-E⟦r2⟧-θ'
... | inj₂ k∈can-q =
  ++ʳ (CodeSet.set-remove (Canₖ (E ⟦ r₂ ⟧e) θ) Code.nothin) k∈can-q
... | inj₁ k∈can-E⟦r1⟧-nothin with Code.nothin Code.≟ k
... | yes refl =
  ⊥-elim (CodeSet.set-remove-removed {Code.nothin} {Canₖ (E ⟦ r₁ ⟧e) θ} k∈can-E⟦r1⟧-nothin)
... | no nothin≢k =
  ++ˡ (CodeSet.set-remove-not-removed nothin≢k
        (canₖ-term-nothin-lemma θ E r₁' r₂' k
          (CodeSet.set-remove-mono-∈ Code.nothin k∈can-E⟦r1⟧-nothin)))
canₖ-term-nothin-lemma θ (esuspend S' ∷ E) r₁' r₂' k k∈can-E⟦r2⟧-θ' =
  canₖ-term-nothin-lemma θ E r₁' r₂' k k∈can-E⟦r2⟧-θ'
canₖ-term-nothin-lemma θ (etrap ∷ E) r₁' r₂' k k∈can-E⟦r2⟧-θ' =
  map-mono Code.↓* (canₖ-term-nothin-lemma θ E r₁' r₂') k k∈can-E⟦r2⟧-θ'


canθₛ-subset-lemma : ∀ sigs S'' p q θ →
  (∀ θ' S → S ∈ Canₛ p θ' → S ∈ Canₛ q θ') →
  ∀ S → S ∈ Canθₛ sigs S'' p θ → S ∈ Canθₛ sigs S'' q θ
canθₛ-subset-lemma [] S'' p q θ canₛ-p⊆canₛ-q S S∈canθ-p-θ =
  canₛ-p⊆canₛ-q θ S S∈canθ-p-θ
canθₛ-subset-lemma (nothing ∷ sigs) S'' p q θ canₛ-p⊆canₛ-q S S∈canθ-p-θ =
  canθₛ-subset-lemma sigs (suc S'') p q θ canₛ-p⊆canₛ-q S S∈canθ-p-θ
canθₛ-subset-lemma (just Signal.present ∷ sigs) S'' p q θ canₛ-p⊆canₛ-q S S∈canθ-p-θ =
  canθₛ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-present (S'' ₛ)) canₛ-p⊆canₛ-q S S∈canθ-p-θ
canθₛ-subset-lemma (just Signal.absent ∷ sigs) S'' p q θ canₛ-p⊆canₛ-q S S∈canθ-p-θ =
  canθₛ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-absent (S'' ₛ)) canₛ-p⊆canₛ-q S S∈canθ-p-θ
canθₛ-subset-lemma (just Signal.unknown ∷ sigs) S'' p q θ canₛ-p⊆canₛ-q S S∈canθ-p-θ
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') q (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-p-θ' | yes S''∈canθ-q-θ' =
  canθₛ-subset-lemma sigs (suc S'') p q (θ ← [S]-env (S'' ₛ)) canₛ-p⊆canₛ-q S S∈canθ-p-θ
... | no  S''∉canθ-p-θ' | no  S''∉canθ-q-θ' =
  canθₛ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-absent (S'' ₛ)) canₛ-p⊆canₛ-q S S∈canθ-p-θ
... | yes S''∈canθ-p-θ' | no  S''∉canθ-q-θ' =
  ⊥-elim
    (S''∉canθ-q-θ'
      (canθₛ-subset-lemma sigs (suc S'') p q (θ ← [S]-env (S'' ₛ)) canₛ-p⊆canₛ-q
        S'' S''∈canθ-p-θ'))
... | no  S''∉canθ-p-θ' | yes S''∈canθ-q-θ' =
  canθₛ-add-sig-monotonic sigs (suc S'') q θ (S'' ₛ) Signal.absent S
    (canθₛ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-absent (S'' ₛ)) canₛ-p⊆canₛ-q
      S S∈canθ-p-θ)


canθₛ-subset : ∀ sigs S'' p q θ →
  (∀ θ' S →
     Signal.unwrap S ∈ Canₛ p θ' →
     Signal.unwrap S ∈ Canₛ q θ') →
  ∀ S →
    Signal.unwrap S ∈ Canθₛ sigs S'' p θ →
    Signal.unwrap S ∈ Canθₛ sigs S'' q θ
canθₛ-subset sigs S'' p q θ canₛ-p⊆canₛ-q S S∈canθ-p-θ =
  canθₛ-subset-lemma sigs S'' p q θ
    (λ θ' S → canₛ-p⊆canₛ-q θ' (S ₛ))
    (Signal.unwrap S) S∈canθ-p-θ


canθₛₕ-subset-lemma : ∀ sigs S'' p q θ →
  (∀ θ' S → S ∈ Canₛ p θ' → S ∈ Canₛ q θ') →
  (∀ θ' s → s ∈ Canₛₕ p θ' → s ∈ Canₛₕ q θ') →
  ∀ s → s ∈ Canθₛₕ sigs S'' p θ → s ∈ Canθₛₕ sigs S'' q θ
canθₛₕ-subset-lemma [] S'' p q θ
  canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ =
  canₛₕ-p⊆canₛₕ-q θ s s∈canθ-p-θ
canθₛₕ-subset-lemma (nothing ∷ sigs) S'' p q θ
  canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ =
  canθₛₕ-subset-lemma sigs (suc S'') p q θ
    canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ
canθₛₕ-subset-lemma (just Signal.present ∷ sigs) S'' p q θ
  canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ =
  canθₛₕ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-present (S'' ₛ))
    canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ
canθₛₕ-subset-lemma (just Signal.absent ∷ sigs) S'' p q θ
  canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ =
  canθₛₕ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-absent (S'' ₛ))
    canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ
canθₛₕ-subset-lemma (just Signal.unknown ∷ sigs) S'' p q θ
  canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') q (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-p-θ' | yes S''∈canθ-q-θ' =
  canθₛₕ-subset-lemma sigs (suc S'') p q (θ ← [S]-env (S'' ₛ))
    canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ
... | no  S''∉canθ-p-θ' | no  S''∉canθ-q-θ' =
  canθₛₕ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-absent (S'' ₛ))
    canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ
... | yes S''∈canθ-p-θ' | no  S''∉canθ-q-θ' =
  ⊥-elim
    (S''∉canθ-q-θ'
      (canθₛ-subset-lemma sigs (suc S'') p q (θ ← [S]-env (S'' ₛ)) canₛ-p⊆canₛ-q
        S'' S''∈canθ-p-θ'))
... | no  S''∉canθ-p-θ' | yes S''∈canθ-q-θ' =
  canθₛₕ-add-sig-monotonic sigs (suc S'') q θ (S'' ₛ) Signal.absent s
    (canθₛₕ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-absent (S'' ₛ))
      canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ)


canθₛₕ-subset : ∀ sigs S'' p q θ →
  (∀ θ' S →
     Signal.unwrap S ∈ Canₛ p θ' →
     Signal.unwrap S ∈ Canₛ q θ') →
  (∀ θ' s →
     SharedVar.unwrap s ∈ Canₛₕ p θ' →
     SharedVar.unwrap s ∈ Canₛₕ q θ') →
  ∀ s →
    SharedVar.unwrap s ∈ Canθₛₕ sigs S'' p θ →
    SharedVar.unwrap s ∈ Canθₛₕ sigs S'' q θ
canθₛₕ-subset sigs S'' p q θ canₛ-p⊆canₛ-q canₛₕ-p⊆canₛₕ-q s s∈canθ-p-θ =
  canθₛₕ-subset-lemma sigs S'' p q θ
    (λ θ' S → canₛ-p⊆canₛ-q θ' (S ₛ)) (λ θ' s → canₛₕ-p⊆canₛₕ-q θ' (s ₛₕ))
    (SharedVar.unwrap s) s∈canθ-p-θ


canθₖ-subset-lemma : ∀ sigs S'' p q θ →
  (∀ θ' S → S ∈ Canₛ p θ' → S ∈ Canₛ q θ') →
  (∀ θ' k → k ∈ Canₖ p θ' → k ∈ Canₖ q θ') →
  ∀ k → k ∈ Canθₖ sigs S'' p θ → k ∈ Canθₖ sigs S'' q θ
canθₖ-subset-lemma [] S'' p q θ
  canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ =
  canₖ-p⊆canₖ-q θ k k∈canθ-p-θ
canθₖ-subset-lemma (nothing ∷ sigs) S'' p q θ
  canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ =
  canθₖ-subset-lemma sigs (suc S'') p q θ
    canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ
canθₖ-subset-lemma (just Signal.present ∷ sigs) S'' p q θ
  canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ =
  canθₖ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-present (S'' ₛ))
    canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ
canθₖ-subset-lemma (just Signal.absent ∷ sigs) S'' p q θ
  canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ =
  canθₖ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-absent (S'' ₛ))
    canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ
canθₖ-subset-lemma (just Signal.unknown ∷ sigs) S'' p q θ
  canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ
  with any (_≟_ S'') (Canθₛ sigs (suc S'') p (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') q (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-p-θ' | yes S''∈canθ-q-θ' =
  canθₖ-subset-lemma sigs (suc S'') p q (θ ← [S]-env (S'' ₛ))
    canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ
... | no  S''∉canθ-p-θ' | no  S''∉canθ-q-θ' =
  canθₖ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-absent (S'' ₛ))
    canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ
... | yes S''∈canθ-p-θ' | no  S''∉canθ-q-θ' =
  ⊥-elim
    (S''∉canθ-q-θ'
      (canθₛ-subset-lemma sigs (suc S'') p q (θ ← [S]-env (S'' ₛ)) canₛ-p⊆canₛ-q
        S'' S''∈canθ-p-θ'))
... | no  S''∉canθ-p-θ' | yes S''∈canθ-q-θ' =
  canθₖ-add-sig-monotonic sigs (suc S'') q θ (S'' ₛ) Signal.absent k
    (canθₖ-subset-lemma sigs (suc S'') p q (θ ← [S]-env-absent (S'' ₛ))
      canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ)


canθₖ-subset : ∀ sigs S'' p q θ →
  (∀ θ' S →
     Signal.unwrap S ∈ Canₛ p θ' →
     Signal.unwrap S ∈ Canₛ q θ') →
  (∀ θ' k →
     k ∈ Canₖ p θ' →
     k ∈ Canₖ q θ') →
  ∀ k →
    k ∈ Canθₖ sigs S'' p θ →
    k ∈ Canθₖ sigs S'' q θ
canθₖ-subset sigs S'' p q θ canₛ-p⊆canₛ-q canₖ-p⊆canₖ-q k k∈canθ-p-θ =
  canθₖ-subset-lemma sigs S'' p q θ
    (λ θ' S → canₛ-p⊆canₛ-q θ' (S ₛ)) canₖ-p⊆canₖ-q 
    k k∈canθ-p-θ


canθₛ-E₁⟦p⟧⊆canθₛ-p : ∀ {pin E₁ E₁⟦nothin⟧ BV FV} sigs S'' θ →
  -- distinct (Dom sigs) (FV (E₁ ⟦ nothin ⟧))
  E₁⟦nothin⟧ ≐ (E₁ ∷ []) ⟦ nothin ⟧e →
  CorrectBinding E₁⟦nothin⟧ BV FV →

  distinct' (map (_+_ S'') (SigMap.keys sigs)) (proj₁ FV) →
  ∀ S' →
    Signal.unwrap S' ∉ proj₁ FV →
    Signal.unwrap S' ∈ Canθₛ sigs S'' ((E₁ ∷ []) ⟦ pin ⟧e) θ →
    Signal.unwrap S' ∈ Canθₛ sigs S'' pin θ
canθₛ-E₁⟦p⟧⊆canθₛ-p {pin} [] S'' θ (depar₁ pin≐E₁⟦nothin⟧) cb@(CBpar {FVp = FVp} cbp cbq _ _ _ _)
  map-S''-+-sigs≠FV S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
  with ++⁻ (Canₛ pin θ) S'∈canθ-E₁⟦pin⟧-θ
... | inj₁ S'∈can-pin-θ = S'∈can-pin-θ
... | inj₂ S'∈can-q-θ = ⊥-elim (S'∉FV (++ʳ (proj₁ FVp) (canₛ-⊆-FV θ cbq S' S'∈can-q-θ)))
canθₛ-E₁⟦p⟧⊆canθₛ-p {pin} {epar₂ p} [] S'' θ (depar₂ pin≐E₁⟦nothin⟧) cb@(CBpar cbp cbq _ _ _ _)
  map-S''-+-sigs≠FV S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
  with ++⁻ (Canₛ p θ) S'∈canθ-E₁⟦pin⟧-θ
... | inj₂ S'∈can-pin-θ = S'∈can-pin-θ
... | inj₁ S'∈can-p-θ = ⊥-elim (S'∉FV (++ˡ (canₛ-⊆-FV θ cbp S' S'∈can-p-θ)))
canθₛ-E₁⟦p⟧⊆canθₛ-p {pin} [] S'' θ (deloopˢ pin≐E₁⟦nothin⟧) cb@(CBloopˢ {FVp = FVp} cbp cbq _ _) = λ _ S' _ z → z
canθₛ-E₁⟦p⟧⊆canθₛ-p {pin} [] S'' θ (deseq pin≐E₁⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _)
  map-S''-+-sigs≠FV S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
  with any (Code._≟_ Code.nothin) (Canₖ pin θ)
... | no  nothin∉can-pin = S'∈canθ-E₁⟦pin⟧-θ
... | yes nothin∈can-pin with ++⁻ (Canₛ pin θ) S'∈canθ-E₁⟦pin⟧-θ
... | inj₁ S∈can-pin-θ = S∈can-pin-θ
... | inj₂ S∈can-q-θ = ⊥-elim (S'∉FV (++ʳ (proj₁ FVp) (canₛ-⊆-FV θ cbq S' S∈can-q-θ)))
canθₛ-E₁⟦p⟧⊆canθₛ-p {pin} [] S'' θ (desuspend pin≐E₁⟦nothin⟧) cb@(CBsusp cb' _)
  map-S''-+-sigs≠FV S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ = S'∈canθ-E₁⟦pin⟧-θ
canθₛ-E₁⟦p⟧⊆canθₛ-p {pin} [] S'' θ (detrap pin≐E₁⟦nothin⟧) cb@(CBtrap cb')
  map-S''-+-sigs≠FV S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ = S'∈canθ-E₁⟦pin⟧-θ
canθₛ-E₁⟦p⟧⊆canθₛ-p (nothing ∷ sigs) S'' θ pin≐E₁⟦nothin⟧ cb
  map-S''-+-sigs≠FV S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛ-E₁⟦p⟧⊆canθₛ-p sigs (suc S'') θ pin≐E₁⟦nothin⟧ cb
      map-S''-+-sigs≠FV
      S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
canθₛ-E₁⟦p⟧⊆canθₛ-p (just Signal.present ∷ sigs) S'' θ pin≐E₁⟦nothin⟧ cb
  map-S''-+-sigs≠FV S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛ-E₁⟦p⟧⊆canθₛ-p sigs (suc S'') (θ ← [S]-env-present (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
      (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
      S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
canθₛ-E₁⟦p⟧⊆canθₛ-p (just Signal.absent ∷ sigs) S'' θ pin≐E₁⟦nothin⟧ cb
  map-S''-+-sigs≠FV S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛ-E₁⟦p⟧⊆canθₛ-p sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
      (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)) )
      S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
canθₛ-E₁⟦p⟧⊆canθₛ-p {pin} {E₁} (just Signal.unknown ∷ sigs) S'' θ pin≐E₁⟦nothin⟧ cb
  map-S''-+-sigs≠FV S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
  with any (_≟_ S'') (Canθₛ sigs (suc S'') pin (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') ((E₁ ∷ []) ⟦ pin ⟧e) (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-p-θ←[S] | yes S''∈canθ-E₁⟦p⟧-θ←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛ-E₁⟦p⟧⊆canθₛ-p sigs (suc S'') (θ ← [S]-env (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
      (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
      S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
... | no  S''∉canθ-p-θ←[S] | no  S''∉canθ-E₁⟦p⟧-θ←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛ-E₁⟦p⟧⊆canθₛ-p sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
      (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
      S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ
... | yes S''∈canθ-p-θ←[S] | no  S''∉canθ-E₁⟦p⟧-θ←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛ-add-sig-monotonic sigs (suc S'') pin θ (S'' ₛ) Signal.absent (Signal.unwrap S')
      (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
        (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
        S' S'∉FV S'∈canθ-E₁⟦pin⟧-θ)
... | no  S''∉canθ-p-θ←[S] | yes S''∈canθ-E₁⟦p⟧-θ←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = ⊥-elim
      (S''∉canθ-p-θ←[S]
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs (suc S'') (θ ← [S]-env (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
          (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
          (S'' ₛ) (map-S''-+-sigs≠FV S'' (here refl)) S''∈canθ-E₁⟦p⟧-θ←[S]))


canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p : ∀ {pin E₁ E₁⟦nothin⟧ BV FV} sigs S'' θ →
  -- distinct (Dom sigs) (FV (E₁ ⟦ nothin ⟧))
  E₁⟦nothin⟧ ≐ (E₁ ∷ []) ⟦ nothin ⟧e →
  CorrectBinding E₁⟦nothin⟧ BV FV →

  distinct' (map (_+_ S'') (SigMap.keys sigs)) (proj₁ FV) →
  ∀ s →
    SharedVar.unwrap s ∉ proj₁ (proj₂ FV) →
    SharedVar.unwrap s ∈ Canθₛₕ sigs S'' ((E₁ ∷ []) ⟦ pin ⟧e) θ →
    SharedVar.unwrap s ∈ Canθₛₕ sigs S'' pin θ
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p {pin} [] S'' θ (depar₁ pin≐E₁⟦nothin⟧) cb@(CBpar {FVp = FVp} cbp cbq _ _ _ _)
  map-S''-+-sigs≠FV s s∉FV s∈canθ-E₁⟦pin⟧-θ
  with ++⁻ (Canₛₕ pin θ) s∈canθ-E₁⟦pin⟧-θ
... | inj₁ s∈can-pin-θ = s∈can-pin-θ
... | inj₂ s∈can-q-θ = ⊥-elim (s∉FV (++ʳ (proj₁ (proj₂ FVp)) (canₛₕ-⊆-FV θ cbq s s∈can-q-θ)))
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p {pin} {epar₂ p} [] S'' θ (depar₂ pin≐E₁⟦nothin⟧) cb@(CBpar cbp cbq _ _ _ _)
  map-S''-+-sigs≠FV s s∉FV s∈canθ-E₁⟦pin⟧-θ
  with ++⁻ (Canₛₕ p θ) s∈canθ-E₁⟦pin⟧-θ
... | inj₂ s∈can-pin-θ = s∈can-pin-θ
... | inj₁ s∈can-p-θ = ⊥-elim (s∉FV (++ˡ (canₛₕ-⊆-FV θ cbp s s∈can-p-θ)))
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p {pin} [] S'' θ (deloopˢ pin≐E₁⟦nothin⟧) cb@(CBloopˢ {FVp = FVp} cbp cbq _ _) = λ _ s _ z → z
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p {pin} [] S'' θ (deseq pin≐E₁⟦nothin⟧) cb@(CBseq {FVp = FVp} cbp cbq _)
  map-S''-+-sigs≠FV s s∉FV s∈canθ-E₁⟦pin⟧-θ
  with any (Code._≟_ Code.nothin) (Canₖ pin θ)
... | no  nothin∉can-pin = s∈canθ-E₁⟦pin⟧-θ
... | yes nothin∈can-pin with ++⁻ (Canₛₕ pin θ) s∈canθ-E₁⟦pin⟧-θ
... | inj₁ s∈can-pin-θ = s∈can-pin-θ
... | inj₂ s∈can-q-θ = ⊥-elim (s∉FV (++ʳ (proj₁ (proj₂ FVp)) (canₛₕ-⊆-FV θ cbq s s∈can-q-θ)))
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p {pin} [] S'' θ (desuspend pin≐E₁⟦nothin⟧) cb@(CBsusp cb' _)
  map-S''-+-sigs≠FV s s∉FV s∈canθ-E₁⟦pin⟧-θ = s∈canθ-E₁⟦pin⟧-θ
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p {pin} [] S'' θ (detrap pin≐E₁⟦nothin⟧) cb@(CBtrap cb')
  map-S''-+-sigs≠FV s s∉FV s∈canθ-E₁⟦pin⟧-θ = s∈canθ-E₁⟦pin⟧-θ
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p (nothing ∷ sigs) S'' θ pin≐E₁⟦nothin⟧ cb
  map-S''-+-sigs≠FV s s∉FV s∈canθ-E₁⟦pin⟧-θ
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p sigs (suc S'') θ pin≐E₁⟦nothin⟧ cb
      map-S''-+-sigs≠FV
      s s∉FV s∈canθ-E₁⟦pin⟧-θ
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p (just Signal.present ∷ sigs) S'' θ pin≐E₁⟦nothin⟧ cb
  map-S''-+-sigs≠FV s s∉FV s∈canθ-E₁⟦pin⟧-θ
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p sigs (suc S'') (θ ← [S]-env-present (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
      (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
      s s∉FV s∈canθ-E₁⟦pin⟧-θ
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p (just Signal.absent ∷ sigs) S'' θ pin≐E₁⟦nothin⟧ cb
  map-S''-+-sigs≠FV s s∉FV s∈canθ-E₁⟦pin⟧-θ
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
      (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)) )
      s s∉FV s∈canθ-E₁⟦pin⟧-θ
canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p {pin} {E₁} (just Signal.unknown ∷ sigs) S'' θ pin≐E₁⟦nothin⟧ cb
  map-S''-+-sigs≠FV s s∉FV s∈canθ-E₁⟦pin⟧-θ
  with any (_≟_ S'') (Canθₛ sigs (suc S'') pin (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') ((E₁ ∷ []) ⟦ pin ⟧e) (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-p-θ←[S] | yes S''∈canθ-E₁⟦p⟧-θ←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p sigs (suc S'') (θ ← [S]-env (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
      (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
      s s∉FV s∈canθ-E₁⟦pin⟧-θ
... | no  S''∉canθ-p-θ←[S] | no  S''∉canθ-E₁⟦p⟧-θ←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
      (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
      s s∉FV s∈canθ-E₁⟦pin⟧-θ
... | yes S''∈canθ-p-θ←[S] | no  S''∉canθ-E₁⟦p⟧-θ←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
  = canθₛₕ-add-sig-monotonic sigs (suc S'') pin θ (S'' ₛ) Signal.absent (SharedVar.unwrap s)
      (canθₛₕ-E₁⟦p⟧⊆canθₛₕ-p sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
        (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
        s s∉FV s∈canθ-E₁⟦pin⟧-θ)
... | no  S''∉canθ-p-θ←[S] | yes S''∈canθ-E₁⟦p⟧-θ←[S]
  rewrite map-+-compose-suc S'' (SigMap.keys sigs)
        | +-comm S'' 0
  = ⊥-elim
      (S''∉canθ-p-θ←[S]
        (canθₛ-E₁⟦p⟧⊆canθₛ-p sigs (suc S'') (θ ← [S]-env (S'' ₛ)) pin≐E₁⟦nothin⟧ cb
          (distinct'-sym (dist':: (distinct'-sym map-S''-+-sigs≠FV)))
          (S'' ₛ) (map-S''-+-sigs≠FV S'' (here refl)) S''∈canθ-E₁⟦p⟧-θ←[S]))


canθₛ-p⊆canθₛ-E₁⟦p⟧ : ∀ sigs S'' θ E₁ pin →
  ∀ S' →
    Signal.unwrap S' ∈ Canθₛ sigs S'' pin θ →
    Signal.unwrap S' ∈ Canθₛ sigs S'' ((E₁ ∷ []) ⟦ pin ⟧e) θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ [] S'' θ (epar₁ q) pin S' S'∈canθ-sigs-pin-θ =
  ++ˡ S'∈canθ-sigs-pin-θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ [] S'' θ (epar₂ p) pin S' S'∈canθ-sigs-pin-θ =
  ++ʳ (Canₛ p θ) S'∈canθ-sigs-pin-θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ [] S'' θ (eloopˢ q) pin S' S'∈canθ-sigs-pin-θ = S'∈canθ-sigs-pin-θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ [] S'' θ (eseq q) pin S' S'∈canθ-sigs-pin-θ
  with any (Code._≟_ Code.nothin) (Canₖ pin θ)
... | yes nothin∈can-pin = ++ˡ S'∈canθ-sigs-pin-θ
... | no  nothin∉can-pin = S'∈canθ-sigs-pin-θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ [] S'' θ (esuspend S) pin S' S'∈canθ-sigs-pin-θ =
  S'∈canθ-sigs-pin-θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ [] S'' θ etrap pin S' S'∈canθ-sigs-pin-θ =
  S'∈canθ-sigs-pin-θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ (nothing ∷ sigs) S'' θ E₁ pin S' S'∈canθ-sigs-pin-θ =
  canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs (suc S'') θ E₁ pin S' S'∈canθ-sigs-pin-θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ (just Signal.present ∷ sigs) S'' θ E₁ pin S' S'∈canθ-sigs-pin-θ =
  canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env-present (S'' ₛ)) E₁ pin
    S' S'∈canθ-sigs-pin-θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ (just Signal.absent ∷ sigs) S'' θ E₁ pin S' S'∈canθ-sigs-pin-θ =
  canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) E₁ pin
    S' S'∈canθ-sigs-pin-θ
canθₛ-p⊆canθₛ-E₁⟦p⟧ (just Signal.unknown ∷ sigs) S'' θ E₁ pin S' S'∈canθ-sigs-pin-θ
  with any (_≟_ S'') (Canθₛ sigs (suc S'') ((E₁ ∷ []) ⟦ pin ⟧e) (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') pin (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sigs-E₁⟦pin⟧-θ | yes S''∈canθ-sigs-pin-θ =
  canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env (S'' ₛ)) E₁ pin
    S' S'∈canθ-sigs-pin-θ
... | no  S''∉canθ-sigs-E₁⟦pin⟧   | no  S''∉canθ-sigs-pin-θ =
  canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) E₁ pin
    S' S'∈canθ-sigs-pin-θ
... | yes S''∈canθ-sigs-E₁⟦pin⟧   | no  S''∉canθ-sigs-pin-θ =
  canθₛ-add-sig-monotonic sigs (suc S'') ((E₁ ∷ []) ⟦ pin ⟧e)
    θ (S'' ₛ) Signal.absent (Signal.unwrap S')
    (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) E₁ pin
      S' S'∈canθ-sigs-pin-θ)
... | no  S''∉canθ-sigs-E₁⟦pin⟧   | yes S''∈canθ-sigs-pin-θ =
  ⊥-elim
    (S''∉canθ-sigs-E₁⟦pin⟧
      (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env (S'' ₛ)) E₁ pin
        (S'' ₛ) S''∈canθ-sigs-pin-θ))


canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ : ∀ sigs S'' θ E₁ pin →
  ∀ s →
    SharedVar.unwrap s ∈ Canθₛ sigs S'' pin θ →
    SharedVar.unwrap s ∈ Canθₛ sigs S'' ((E₁ ∷ []) ⟦ pin ⟧e) θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ [] S'' θ (epar₁ q) pin s s∈canθ-sigs-pin-θ =
  ++ˡ s∈canθ-sigs-pin-θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ [] S'' θ (epar₂ p) pin s s∈canθ-sigs-pin-θ =
  ++ʳ (Canₛ p θ) s∈canθ-sigs-pin-θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ [] S'' θ (eloopˢ q) pin s s∈canθ-sigs-pin-θ = s∈canθ-sigs-pin-θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ [] S'' θ (eseq q) pin s s∈canθ-sigs-pin-θ
  with any (Code._≟_ Code.nothin) (Canₖ pin θ)
... | yes nothin∈can-pin = ++ˡ s∈canθ-sigs-pin-θ
... | no  nothin∉can-pin = s∈canθ-sigs-pin-θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ [] S'' θ (esuspend S) pin s s∈canθ-sigs-pin-θ =
  s∈canθ-sigs-pin-θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ [] S'' θ etrap pin s s∈canθ-sigs-pin-θ =
  s∈canθ-sigs-pin-θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ (nothing ∷ sigs) S'' θ E₁ pin s s∈canθ-sigs-pin-θ =
  canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ sigs (suc S'') θ E₁ pin s s∈canθ-sigs-pin-θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ (just Signal.present ∷ sigs) S'' θ E₁ pin s s∈canθ-sigs-pin-θ =
  canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env-present (S'' ₛ)) E₁ pin
    s s∈canθ-sigs-pin-θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ (just Signal.absent ∷ sigs) S'' θ E₁ pin s s∈canθ-sigs-pin-θ =
  canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) E₁ pin
    s s∈canθ-sigs-pin-θ
canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ (just Signal.unknown ∷ sigs) S'' θ E₁ pin s s∈canθ-sigs-pin-θ
  with any (_≟_ S'') (Canθₛ sigs (suc S'') ((E₁ ∷ []) ⟦ pin ⟧e) (θ ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs (suc S'') pin (θ ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sigs-E₁⟦pin⟧-θ | yes S''∈canθ-sigs-pin-θ =
  canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env (S'' ₛ)) E₁ pin
    s s∈canθ-sigs-pin-θ
... | no  S''∉canθ-sigs-E₁⟦pin⟧   | no  S''∉canθ-sigs-pin-θ =
  canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) E₁ pin
    s s∈canθ-sigs-pin-θ
... | yes S''∈canθ-sigs-E₁⟦pin⟧   | no  S''∉canθ-sigs-pin-θ =
  canθₛ-add-sig-monotonic sigs (suc S'') ((E₁ ∷ []) ⟦ pin ⟧e)
    θ (S'' ₛ) Signal.absent (SharedVar.unwrap s)
    (canθₛₕ-p⊆canθₛₕ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env-absent (S'' ₛ)) E₁ pin
      s s∈canθ-sigs-pin-θ)
... | no  S''∉canθ-sigs-E₁⟦pin⟧   | yes S''∈canθ-sigs-pin-θ =
  ⊥-elim
    (S''∉canθ-sigs-E₁⟦pin⟧
      (canθₛ-p⊆canθₛ-E₁⟦p⟧ sigs (suc S'') (θ ← [S]-env (S'' ₛ)) E₁ pin
        (S'' ₛ) S''∈canθ-sigs-pin-θ))


canθ-shadowing-irr' : ∀ sigs' S'' p S status θ θo →
  S ∈ map (_+_ S'') (SigMap.keys sigs') →
    Canθ sigs' S'' p ((θ ← [ (S ₛ) ↦ status ]) ← θo) ≡
    Canθ sigs' S'' p (θ ← θo)
canθ-shadowing-irr' [] S'' p S status θ θo ()
canθ-shadowing-irr' (nothing ∷ sigs') S'' p S status θ θo S∈map-+-S''-sigs'
  rewrite map-+-compose-suc S'' (SigMap.keys sigs')
  = canθ-shadowing-irr' sigs' (suc S'') p S status θ θo S∈map-+-S''-sigs'
canθ-shadowing-irr' (just Signal.present ∷ sigs') S'' p S status θ θo (here refl)
  rewrite +-comm S'' 0
        | Env.sig-set-inner-clobber θ θo ([S]-env-present (S'' ₛ)) (S'' ₛ) status (Env.sig-∈-single (S'' ₛ) Signal.present)
  = refl
canθ-shadowing-irr' (just Signal.absent ∷ sigs') S'' p S status θ θo (here refl)
  rewrite +-comm S'' 0
        | Env.sig-set-inner-clobber θ θo ([S]-env-absent (S'' ₛ)) (S'' ₛ) status (Env.sig-∈-single (S'' ₛ) Signal.absent)
  = refl
canθ-shadowing-irr' (just Signal.unknown ∷ sigs') S'' p S status θ θo (here refl)
  with any (_≟_ S'') (Canθₛ sigs' (suc S'') p (((θ ← [ (S ₛ) ↦ status ]) ← θo) ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs' (suc S'') p ((θ ← θo) ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sigs-θ←[S]-absent←θo←[S''] | yes S''∈canθ-sigs-θ←[S]←θo←[S'']
  rewrite +-comm S'' 0
        | Env.sig-set-inner-clobber θ θo ([S]-env (S'' ₛ)) (S'' ₛ) status (Env.sig-∈-single (S'' ₛ) Signal.unknown)
  = refl
... | no  S''∉canθ-sigs-θ←[S]-absent←θo←[S''] | no  S''∉canθ-sigs-θ←[S]←θo←[S'']
  rewrite +-comm S'' 0
        | Env.sig-set-inner-clobber θ θo ([S]-env-absent (S'' ₛ)) (S'' ₛ) status (Env.sig-∈-single (S'' ₛ) Signal.absent)
  = refl
... | yes S''∈canθ-sigs-θ←[S]-absent←θo←[S''] | no  S''∉canθ-sigs-θ←[S]←θo←[S'']
  rewrite +-comm S'' 0
        | Env.sig-set-inner-clobber θ θo ([S]-env (S'' ₛ)) (S'' ₛ) status (Env.sig-∈-single (S'' ₛ) Signal.unknown)
  = ⊥-elim (S''∉canθ-sigs-θ←[S]←θo←[S''] S''∈canθ-sigs-θ←[S]-absent←θo←[S''])
... | no  S''∉canθ-sigs-θ←[S]-absent←θo←[S''] | yes S''∈canθ-sigs-θ←[S]←θo←[S'']
  rewrite +-comm S'' 0
        | Env.sig-set-inner-clobber θ θo ([S]-env (S'' ₛ)) (S'' ₛ) status (Env.sig-∈-single (S'' ₛ) Signal.unknown)
  = ⊥-elim (S''∉canθ-sigs-θ←[S]-absent←θo←[S''] S''∈canθ-sigs-θ←[S]←θo←[S''])
canθ-shadowing-irr' (just Signal.present ∷ sigs') S'' p S status θ θo (there S∈map-+-S''-sigs')
  rewrite map-+-compose-suc S'' (SigMap.keys sigs')
        | sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env-present (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env-present (S'' ₛ)))
  = canθ-shadowing-irr' sigs' (suc S'') p S status θ (θo ← [S]-env-present (S'' ₛ)) S∈map-+-S''-sigs'
canθ-shadowing-irr' (just Signal.absent ∷ sigs') S'' p S status θ θo (there S∈map-+-S''-sigs')
  rewrite map-+-compose-suc S'' (SigMap.keys sigs')
        | sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env-absent (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env-absent (S'' ₛ)))
  = canθ-shadowing-irr' sigs' (suc S'') p S status θ (θo ← [S]-env-absent (S'' ₛ)) S∈map-+-S''-sigs'
canθ-shadowing-irr' (just Signal.unknown ∷ sigs') S'' p S status θ θo (there S∈map-+-S''-sigs')
  with any (_≟_ S'') (Canθₛ sigs' (suc S'') p (((θ ← [ (S ₛ) ↦ status ]) ← θo) ← [S]-env (S'' ₛ)))
     | any (_≟_ S'') (Canθₛ sigs' (suc S'') p ((θ ← θo) ← [S]-env (S'' ₛ)))
... | yes S''∈canθ-sigs-θ←[S]-absent←θo←[S''] | yes S''∈canθ-sigs-θ←[S]←θo←[S'']
  rewrite map-+-compose-suc S'' (SigMap.keys sigs')
        | sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env (S'' ₛ)))
  = canθ-shadowing-irr' sigs' (suc S'') p S status θ (θo ← [S]-env (S'' ₛ)) S∈map-+-S''-sigs'
... | no  S''∉canθ-sigs-θ←[S]-absent←θo←[S''] | no  S''∉canθ-sigs-θ←[S]←θo←[S'']
  rewrite map-+-compose-suc S'' (SigMap.keys sigs')
        | sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env-absent (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env-absent (S'' ₛ)))
  = canθ-shadowing-irr' sigs' (suc S'') p S status θ (θo ← [S]-env-absent (S'' ₛ)) S∈map-+-S''-sigs'
... | yes S''∈canθ-sigs-θ←[S]-absent←θo←[S''] | no  S''∉canθ-sigs-θ←[S]←θo←[S'']
  rewrite map-+-compose-suc S'' (SigMap.keys sigs')
        | sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env (S'' ₛ)))
        | canθ-shadowing-irr' sigs' (suc S'') p S status θ (θo ← [S]-env (S'' ₛ)) S∈map-+-S''-sigs'
  = ⊥-elim (S''∉canθ-sigs-θ←[S]←θo←[S''] S''∈canθ-sigs-θ←[S]-absent←θo←[S''])
... | no  S''∉canθ-sigs-θ←[S]-absent←θo←[S''] | yes S''∈canθ-sigs-θ←[S]←θo←[S'']
  rewrite map-+-compose-suc S'' (SigMap.keys sigs')
        | sym (Env.←-assoc (θ ← [ (S ₛ) ↦ status ]) θo ([S]-env (S'' ₛ)))
        | sym (Env.←-assoc θ θo ([S]-env (S'' ₛ)))
        | canθ-shadowing-irr' sigs' (suc S'') p S status θ (θo ← [S]-env (S'' ₛ)) S∈map-+-S''-sigs'
  = ⊥-elim (S''∉canθ-sigs-θ←[S]-absent←θo←[S''] S''∈canθ-sigs-θ←[S]←θo←[S''])


canθ-shadowing-irr : ∀ sigs' S'' p S status θ →
  Signal.unwrap S ∈ map (_+_ S'') (SigMap.keys sigs') →
    Canθ sigs' S'' p θ ≡
    Canθ sigs' S'' p (θ ← [ S ↦ status ])
canθ-shadowing-irr sigs' S'' p S status θ S∈map-+-S''-sigs'
  rewrite Env.←-comm Env.[]env (θ ← [ S ↦ status ]) distinct-empty-left
        | cong (Canθ sigs' S'' p) (Env.←-comm Env.[]env θ distinct-empty-left)
  = sym (canθ-shadowing-irr' sigs' S'' p (Signal.unwrap S) status
          θ Env.[]env S∈map-+-S''-sigs')


Canθₛunknown->Canₛunknown-help : ∀ S S' p →
  (S + S') ∈ Canθₛ SigMap.[ (S ₛ) ↦ Signal.unknown ] S' p Env.[]env →
  (S + S') ∈ Canₛ p [ ((S + S') ₛ) ↦ Signal.unknown ]
Canθₛunknown->Canₛunknown-help zero    S' p S+S'∈canθ-[S↦unknown]-S'
  with any (S' ≟_) (Canₛ p [ (S' ₛ) ↦ Signal.unknown ])
... | yes S'∈can-p-[S↦unknown] = S+S'∈canθ-[S↦unknown]-S'
... | no  S'∉can-p-[S↦unknown] =
  Data.Empty.⊥-elim
    (S'∉can-p-[S↦unknown]
      (Esterel.Lang.CanFunction.SetSigMonotonic.canθₛ-add-sig-monotonic
       [] 0 p Env.[]env (S' ₛ) Signal.absent S'
       S+S'∈canθ-[S↦unknown]-S'))
Canθₛunknown->Canₛunknown-help (suc S) S' p S+S'∈canθ-[S↦unknown]-S'
  -- trans (cong suc (+-comm S S')) (+-comm (suc S') S) : suc (S + S') ≡ S + (suc S')
  rewrite cong (λ n → Canₛ p [ (n ₛ) ↦ Signal.unknown ])
               (trans (cong suc (+-comm S S')) (+-comm (suc S') S))
        |       trans (cong suc (+-comm S S')) (+-comm (suc S') S)
  = Canθₛunknown->Canₛunknown-help S (suc S') p S+S'∈canθ-[S↦unknown]-S'

Canθₛunknown->Canₛunknown : ∀ S p ->
  (Signal.unwrap S) ∈ Canθₛ SigMap.[ S ↦ Signal.unknown ] 0 p Env.[]env →
  (Signal.unwrap S) ∈ Canₛ p [ S ↦ Signal.unknown ]
Canθₛunknown->Canₛunknown S p fact
  rewrite +-right-identity (Signal.unwrap S)
  with Canθₛunknown->Canₛunknown-help
          (Signal.unwrap S) zero p (add-zero (Signal.unwrap S) _ fact)
    where
    add-zero : ∀ s x -> s ∈ x -> (s + 0) ∈ x
    add-zero s x s+0∈x rewrite +-right-identity s = s+0∈x
... | thing rewrite +-right-identity (Signal.unwrap S) = thing
