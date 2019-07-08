{-

This module implements data structures and lemma's for working with Can in the std reduction.

-}

module std-reduction.Can where

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open EvaluationContext1
open import Esterel.Environment as Env
  using (Env ; []env)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)
open import Esterel.Lang.CanFunction
  using (Canₛ ; Canₛₕ ; Canθₛ ; Canθₛₕ)
open import Esterel.Lang.CanFunction.Base
  using (canθₛ-membership ; canθₛₕ-membership)
open import Esterel.Lang.CanFunction.SetSigMonotonic
open import utility using (_∈_ ; _∉_) renaming (module UniquedSet to US)
open US using (UniquedSet ; uniqued-set ; c ; UniquedList)


open import Data.List
  using (List; _∷_ ; [] ; mapMaybe)
open import Data.List.Any
  using (any ; here ; there)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_ ; ∃-syntax; Σ-syntax ; ∃ ; Σ)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; sym ; subst)
open _≡_
import Data.Nat as Nat
open import Relation.Nullary using (yes ; no ; ¬_)
open import Function using (_∘_ ; id ; _$_)
open import Data.Maybe
  using (Maybe)
open Maybe
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Data.Bool
  using (if_then_else_)
open import Level
open import Data.Unit using (tt ; ⊤)

open import utility
  using (_∉_)
  renaming (module UniquedSet to US)
open US using (UniquedSet ; uniqued-set)

open import Relation.Binary.PropositionalEquality using (_≡_ ; sym)
open import Function
  using (_∘_ ; _$_ ; _∋_)
open import Data.List using (_∷_ ; map ; [])
open import Data.Product using (_,_ ; proj₁ ; proj₂)


{- 

These records encapsulate the proofs that must hold to set
to set a variable to absent/ready in some term (ρ θ · p).

note that this uses `Can` not `Canθ`: It is not needed (as
at least some progress is made) and using Can makes testing
more feasable because it avoids some of the exponential
behavior of Can.

-}

record CanSetToAbsent (θ : Env) (p : Term) (S : Signal) : Set where
  constructor canSetToAbsent
  field
    S∈ : Env.isSig∈ S θ
    S∉ : ((Signal.unwrap S) ∉ Canₛ p θ)
    S≡u : (Env.sig-stats{S} θ S∈ ≡ Signal.unknown)

record CanSetToReady (θ : Env) (p : Term) (s : SharedVar) : Set where
  constructor canSetToReady
  field
    s∈ : (Env.isShr∈ s θ)
    s∉ : ((SharedVar.unwrap s) ∉ Canₛₕ p θ)
    s≠r : (Env.shr-stats{s} θ s∈ ≡ SharedVar.old ⊎ Env.shr-stats{s} θ s∈ ≡ SharedVar.new)

{-
These represent the actual set of things which can
-}
AbsentSet : Env → Term → Set
AbsentSet θ p = UniquedSet (CanSetToAbsent θ p)

ReadySet : Env → Term → Set
ReadySet θ p = UniquedSet (CanSetToReady θ p) 



mutual
  set-all-absent : (θ : Env) → (p : Term) → (Ss : List $ ∃ (CanSetToAbsent θ p)) → UniquedList proj₁ Ss → Env
  set-all-absent θ p [] _ = θ
  set-all-absent θ p ((S , CA) ∷ Ss) (c _ _ _ x)
    = Env.set-sig{S} (set-all-absent θ p Ss x) (set-all-absent∈ θ p S Ss x S∈) Signal.absent
   where open CanSetToAbsent CA

  set-all-absent∈ : ∀ θ p S Ss ul → Env.isSig∈ S θ → Env.isSig∈ S (set-all-absent θ p Ss ul)
  set-all-absent∈ θ p S [] _ S∈ = S∈
  set-all-absent∈ θ p S ((S' , x) ∷ Ss) (c _ _ _ r) S∈
    = Env.sig-set-mono'{S = S}{S' = S'}{θ = set-all-absent θ p Ss r}{S'∈ = S'∈2} S∈2
   where
     S∈2 = (set-all-absent∈ θ p S Ss r S∈)
     S'∈2 = (set-all-absent∈ θ p S' Ss r (CanSetToAbsent.S∈ x))
  

mutual
  set-all-ready : (θ : Env) → (p : Term) → (ss : List $ ∃ (CanSetToReady θ p)) → UniquedList proj₁ ss → Env
  set-all-ready θ p [] _ = θ
  set-all-ready θ p ((s , x) ∷  ss) (c _ _ _ r)
    = Env.set-shr {s} θ2 s∈2 SharedVar.ready (Env.shr-vals{s} θ s∈)
      where
        open CanSetToReady x
        s∈2 = (set-all-ready∈ θ p s ss r s∈)
        θ2 = (set-all-ready θ p ss r)

  set-all-ready∈ : ∀ θ p s ss ul → Env.isShr∈ s θ → Env.isShr∈ s (set-all-ready θ p ss ul)
  set-all-ready∈ θ p s [] _ s∈ = s∈
  set-all-ready∈ θ p s ((s' , x) ∷ ss) (c _ _ _ r) s∈
    = Env.shr-set-mono' {s = s} {s' = s'} {θ = set-all-ready θ p ss r}
        {s'∈ = set-all-ready∈ θ p s' ss r (CanSetToReady.s∈ x)} (set-all-ready∈ θ p s ss r s∈)

can-set-absent∈-update : ∀{θ p} → ∀ Ss ul S → (S∈ : Env.isSig∈ S θ) → S ∉ (Data.List.map proj₁ Ss) → Env.sig-stats{S = S} θ S∈ ≡ Signal.unknown
                        → Σ[ S∈ ∈ Env.isSig∈ S (set-all-absent θ p Ss ul) ] Env.sig-stats{S = S} (set-all-absent θ p Ss ul) S∈ ≡ Signal.unknown

can-set-absent∈-update {θ} {p} [] _ S S∈ S∉Ss S≡u = S∈ , S≡u
can-set-absent∈-update {θ} {p} ((S' , x) ∷ Ss) (c .(S' , x) .Ss ∉ ul) S S∈ S∉Ss S≡u with can-set-absent∈-update Ss ul S S∈ (S∉Ss ∘ there) S≡u
... | S∈' , S≡u' = S∈2 , Env.sig-putputget{θ = θ'}{stat2 = Signal.absent} S≠S' S∈' (proj₁ $ can-set-absent∈-update Ss ul S' (CanSetToAbsent.S∈ x) ∉ $ CanSetToAbsent.S≡u x) S∈2 S≡u'
  where
   S≠S' : ¬ S ≡ S'
   S≠S' = S∉Ss ∘ here
   θ' = (set-all-absent θ p Ss ul)
   S∈2 =  (Env.sig-set-mono'{S = S}{S' = S'}{θ'}{Signal.absent}{(proj₁ $ can-set-absent∈-update Ss ul S' (CanSetToAbsent.S∈ x) ∉ $ CanSetToAbsent.S≡u x)} S∈' ) 



can-set-absent : (θ : Env) → (p : Term) → AbsentSet θ p 
can-set-absent θ p = US.set-map-maybe $ Env.SigMap.key-unique-map (Env.sig θ) _ get-res
  where
    get-res : (S : Signal) → Env.isSig∈ S θ → Maybe (CanSetToAbsent θ p S)
    get-res S S∈ with any (Nat._≟_ (Signal.unwrap S)) (Canₛ p θ) | Signal._≟ₛₜ_ (Env.sig-stats{S} θ S∈) Signal.unknown
    ... | no ∉ | yes eq = just $ canSetToAbsent S∈ ∉ $ eq
    ... | _ | _ = nothing


can-set-ready : (θ : Env) → (p : Term) → ReadySet θ p
can-set-ready θ p = US.set-map-maybe $ Env.ShrMap.key-unique-map (Env.shr θ) _ get-res
  where
    get-res : (s : SharedVar) → Env.isShr∈ s θ → Maybe (CanSetToReady θ p s)
    get-res s s∈ with any (Nat._≟_ (SharedVar.unwrap s)) (Canₛₕ p θ)
                    | SharedVar._≟ₛₜ_ (Env.shr-stats{s} θ s∈) SharedVar.old
                    | SharedVar._≟ₛₜ_ (Env.shr-stats{s} θ s∈) SharedVar.new
    ... | no ∉ | yes eq |  _   = just $ canSetToReady s∈ ∉ $ inj₁ eq
    ... | no ∉ | no _ | yes eq = just $ canSetToReady s∈ ∉ $ inj₂ eq
    ... | _ | yes _ | yes _ = nothing
    ... | _ | yes _ | no _ = nothing
    ... | _ | no _ | yes _ = nothing
    ... | _ | no _ | no _ = nothing

