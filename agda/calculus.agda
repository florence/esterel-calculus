module calculus where

open import utility

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
open import Esterel.Lang.PotentialFunction
  using (Canθₛ ; Canθₛₕ ; [S]-env)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; sig ; []env ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
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
  using (ℕ ; zero ; suc ; _+_) renaming (_⊔_ to _⊔ℕ_)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; _,′_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality

open import sn-calculus

open _≐_⟦_⟧e
open _≐_⟦_⟧c

open EvaluationContext1
open Context1

infix 4 _⟶₁_
infix 4 _⟶_
infix 4 _⟶*_

data _⟶₁_ : Term → Term → Set where
  [par-swap] : ∀{p q} →
    (p ∥ q) ⟶₁ (q ∥ p)

  [par-nothing] : ∀ {q} ->
    done q ->
    (nothin ∥ q) ⟶₁ q

  [par-1exit] : ∀ {q} -> ∀ n ->
    (pausedq : paused q) ->
    (exit n ∥ q) ⟶₁ exit n

  [par-2exit] : ∀ n m ->
    (exit n ∥ exit m) ⟶₁ exit (n ⊔ℕ m)

  [is-present] : ∀{θ r p q E} → ∀ S ->
    (S∈ : (Env.isSig∈ S θ)) →
    (θ[S]≡present : Env.sig-stats{S} θ S∈ ≡ Signal.present) →
    (de : r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e) →
    (ρ θ · r) ⟶₁ (ρ θ · E ⟦ p ⟧e)

  [is-absent] : ∀{θ r p q E} → ∀ S ->
    (S∈ : (Env.isSig∈ S θ)) →
    (θ[S]≡absent : Env.sig-stats{S} θ S∈ ≡ Signal.absent) →
    (de : r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e) →
    (ρ θ · r) ⟶₁ (ρ θ · E ⟦ q ⟧e)

  [emit] : ∀{θ r S E} →
    (S∈ : (Env.isSig∈ S θ)) →
    (¬S≡a : ¬ (Env.sig-stats{S} θ S∈) ≡ Signal.absent) →
    (de : r ≐ E ⟦ emit S ⟧e) →
    (ρ θ · r) ⟶₁
    (ρ (Env.set-sig{S} θ S∈ Signal.present) ·
      E ⟦ nothin ⟧e)

  [loop-unroll] : ∀{p} →
    (loop p)
    ⟶₁
    (loopˢ p p)

  [seq-done] : ∀{q} →
    (nothin >> q) ⟶₁ q

  [seq-exit] : ∀{q n} →
    (exit n >> q) ⟶₁ (exit n)

  [loopˢ-exit] : ∀{q n} →
    (loopˢ (exit n) q) ⟶₁ (exit n)

  [suspend-done] : ∀{p S} →
    (haltedp : halted p) →
    (suspend p S) ⟶₁ p

  -- traps
  [trap-done] : ∀{p} →
    (haltedp : halted p) →
    (trap p) ⟶₁ (↓ haltedp)

  -- lifting signals
  [raise-signal] : ∀{p S} →
    (signl S p) ⟶₁
    (ρ (Θ SigMap.[ S ↦ Signal.unknown ] ShrMap.empty VarMap.empty) ·
      p)

  -- shared state
  [raise-shared] : ∀{θ r s e p E} →
    (all-readyeθ : all-ready e θ) →
    (de : r ≐ E ⟦ shared s ≔ e in: p ⟧e) →
    (ρ θ · r) ⟶₁
    (ρ θ · E ⟦ (ρ [s,δe]-env s (δ all-readyeθ) · p) ⟧e)

  [set-shared-value-old] : ∀{θ r s e E} →
    (e' : all-ready e θ) →
    (s∈ : (Env.isShr∈ s θ)) →
    (θ[s]≡old : Env.shr-stats{s} θ s∈ ≡ SharedVar.old) →
    (de : r ≐ E ⟦ s ⇐ e ⟧e) →
    (ρ θ · r) ⟶₁
    (ρ (Env.set-shr{s} θ s∈ (SharedVar.new) (δ e')) ·
      E ⟦ nothin ⟧e)

  [set-shared-value-new] : ∀{θ r s e E} →
    (e' : all-ready e θ) →
    (s∈ : (Env.isShr∈ s θ)) →
    (θ[s]≡n : Env.shr-stats{s} θ s∈ ≡ SharedVar.new) →
    (de : r ≐ E ⟦ s ⇐ e ⟧e) →
    (ρ θ · r) ⟶₁
    (ρ (Env.set-shr{s} θ s∈ (SharedVar.new) (Env.shr-vals{s} θ s∈ + δ e')) ·
      E ⟦ nothin ⟧e)

  -- unshared state
  [raise-var] : ∀{θ r x p e E} →
    (all-readyeθ : all-ready e θ) →
    (de : r ≐ E ⟦ var x ≔ e in: p ⟧e) →
    (ρ θ · r) ⟶₁
    (ρ θ ·
      E ⟦ (ρ [x,δe]-env x (δ all-readyeθ) · p) ⟧e)

  [set-var] : ∀{θ r x e E} →
    (x∈ : (Env.isVar∈ x θ)) →
    (all-readyeθ : all-ready e θ) →
    (de : r ≐ E ⟦ x ≔ e ⟧e) →
    (ρ θ · r) ⟶₁
    (ρ (Env.set-var{x} θ x∈ (δ all-readyeθ)) ·
      E ⟦ nothin ⟧e)

  -- if
  [if-false] : ∀{θ r p q x E} →
    (x∈ : (Env.isVar∈ x θ)) →
    (θ[x]≡z : Env.var-vals{x} θ x∈ ≡ zero) →
    (de : r ≐ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) →
    (ρ θ · r) ⟶₁ (ρ θ · E ⟦ q ⟧e)

  [if-true] : ∀{θ r p q x E n} →
    (x∈ : (Env.isVar∈ x θ)) →
    (θ[x]≡s : Env.var-vals{x} θ x∈ ≡ suc n) →
    (de : r ≐ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e) →
    (ρ θ · r) ⟶₁ (ρ θ · E ⟦ p ⟧e)

  -- progression
  [absence] : ∀{θ p} -> ∀ S →
    (S∈ : (Env.isSig∈ S θ)) →
    (θ[S]≡unknown : Env.sig-stats{S} θ S∈ ≡ Signal.unknown) →
    (S∉Canθₛ : (Signal.unwrap S) ∉ Canθₛ (sig θ) 0 p []env) →
    (ρ θ · p) ⟶₁
    (ρ (Env.set-sig{S} θ S∈ (Signal.absent)) ·
      p)

  [readyness] : ∀{θ p} -> ∀ s →
    (s∈ : (Env.isShr∈ s θ)) →
    (θ[s]≡old⊎θ[s]≡new : (Env.shr-stats{s} θ s∈ ≡ SharedVar.old) ⊎
                         (Env.shr-stats{s} θ s∈ ≡ SharedVar.new)) →
    (s∉Canθₛₕ : (SharedVar.unwrap s) ∉ Canθₛₕ (sig θ) 0 p []env) →
    (ρ θ · p) ⟶₁
    (ρ (Env.set-shr{s} θ s∈ (SharedVar.ready) (Env.shr-vals{s} θ s∈)) ·
      p)

  [merge] : ∀{θ₁ θ₂ r p E} →
    (de : r ≐ E ⟦ ρ θ₂ · p ⟧e) →
    (ρ θ₁ · r) ⟶₁ (ρ (θ₁ ← θ₂) · E ⟦ p ⟧e)

-- The compatible closure of _⟶₁_.
data _⟶_ : Term → Term → Set where
  [context] : ∀{r p p'} →
    (C : Context) →
    (dc : r ≐ C ⟦ p ⟧c) →
    (p⟶₁p' : p ⟶₁ p') →
    r ⟶ (C ⟦ p' ⟧c)

-- The reflexive transitive closure of ⟶
data _⟶*_ : Term → Term → Set where
  [refl] : ∀{p} → (p ⟶* p)
  [step] : ∀{p q r} → (p⟶q : p ⟶ q) → (q⟶*r : q ⟶* r) → (p ⟶* r)

data _≡ₑ_#_ : Term -> Term -> List Context1 -> Set where

  ≡ₑrefl : ∀ {p C} ->

    ------------
     p ≡ₑ p # C

  ≡ₑtran : ∀ {p r q C} ->

     (p≡ₑr#C : p ≡ₑ r # C) ->
     (r≡ₑq#C : r ≡ₑ q # C) ->
    -----------------------
      p ≡ₑ q # C

  ≡ₑsymm : ∀ {p q C BVq FVq} ->

     (CBq : CorrectBinding (C ⟦ q ⟧c) BVq FVq) ->
     (q≡ₑp : q ≡ₑ p # C) ->
    -------------------------------------------
      p ≡ₑ q # C

  ≡ₑctxt : ∀ {C C′ p q C′⟦p⟧ C′⟦q⟧ } ->

     (C′⟦p⟧≐C′⟦p⟧c : C′⟦p⟧ ≐ C′ ⟦ p ⟧c) ->
     (C′⟦q⟧≐C′⟦q⟧c : C′⟦q⟧ ≐ C′ ⟦ q ⟧c) ->
     (p≡ₑq : p ≡ₑ q # (C ++ C′)) ->
    -----------------------------------
     C′⟦p⟧ ≡ₑ C′⟦q⟧ # C

  ≡ₑstep : ∀ {C p q} ->

     (p⟶₁q : p ⟶₁ q) ->
    --------------------
     p ≡ₑ q # C
