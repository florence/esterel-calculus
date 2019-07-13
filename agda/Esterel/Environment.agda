module Esterel.Environment where

open import utility renaming (module UniquedSet to UL)

open import Data.Empty
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)
open import Data.Product

import Data.FiniteMap
open import Data.Nat as Nat
  using (ℕ)
open import Data.List as List
  using (List ; [] ; _∷_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂ ; [_,_])

open import Function
  using (_∘_)
open import Relation.Nullary
  using (Dec ; yes ; no ; ¬_)
open import Relation.Binary
  using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; sym ; module ≡-Reasoning ; trans ; subst ; inspect)
open import Data.List.Any
  using (Any)

open ≡-Reasoning using (_≡⟨_⟩_ ; _≡⟨⟩_ ; _∎ ; begin_)

open UL using (UniquedSet)


module SigMap = Data.FiniteMap Signal
module ShrMap = Data.FiniteMap SharedVar
module VarMap = Data.FiniteMap SeqVar

record Env : Set where
  constructor Θ
  field
    sig  : SigMap.Map Signal.Status
    shr  : ShrMap.Map (SharedVar.Status × ℕ)
    var  : VarMap.Map ℕ

open Env public

-- A VarList is a three-tuple of lists of unwrapped signals,
-- shared variables and sequential variables.
VarList : Set
VarList = List ℕ × List ℕ × List ℕ

Dom : Env -> VarList
Dom (Θ sig shr var) = (SigMap.keys sig) , (ShrMap.keys shr) , (VarMap.keys var)

[]env = Θ [] [] []

Sig∈ : (S : Signal) →
       (e : Env) →
       Relation.Nullary.Dec
          (Any (SigMap.inj= S)
               (SigMap.keys (sig e)))
Sig∈ s e = SigMap.∈Check s (sig e)

Shr∈ : (s : SharedVar) → (e : Env) →
       Relation.Nullary.Dec
       (Any (ShrMap.inj= s)
            (ShrMap.keys (shr e)))
Shr∈ s e = ShrMap.∈Check s (shr e)

Var∈ : (x : SeqVar) → (e : Env) →
       Relation.Nullary.Dec
       (Any (VarMap.inj= x)
            (VarMap.keys (var e)))
Var∈ x e = VarMap.∈Check x (var e)

isSig∈ : (S : Signal) → (e : Env) → Set
isSig∈ S e = (SigMap.∈Dom S (sig e))

isShr∈ : SharedVar → Env → Set
isShr∈ s e = ShrMap.∈Dom s (shr e)

isVar∈ : SeqVar → Env → Set
isVar∈ x e = VarMap.∈Dom x (var e)

SigDomMap : ∀{a}{L : Set a} →  (θ : Env) → (f : (S : Signal) → isSig∈ S θ → L) → List L
SigDomMap = SigMap.key-map ∘ sig

ShrDomMap : ∀{a}{L : Set a} →  (θ : Env) → (f : (S : SharedVar) → isShr∈ S θ → L) → List L
ShrDomMap = ShrMap.key-map ∘ shr

SigDomMap+Uniqued : ∀{L : Signal → Set} → (θ : Env) → (f : (S : Signal) → isSig∈ S θ → (L S)) → UniquedSet L 
SigDomMap+Uniqued {L} θ f = SigMap.key-unique-map (sig θ) L f

ShrDomMap+Uniqued : ∀{L : SharedVar → Set} → (θ : Env) → (f : (s : SharedVar) → isShr∈ s θ → (L s)) → UniquedSet L 
ShrDomMap+Uniqued {L} θ f = ShrMap.key-unique-map (shr θ) L f

SigDom : Env → List ℕ
SigDom (Θ sig shr var) = (SigMap.keys sig)
ShrDom : Env → List ℕ
ShrDom (Θ sig shr var) = (ShrMap.keys shr)
VarDom : Env → List ℕ
VarDom (Θ sig shr var) = (VarMap.keys var)

sig-stats : ∀{S} → (θ : Env) → (SigMap.∈Dom S (sig θ)) → Signal.Status
sig-stats{S} θ S∈ = SigMap.lookup{k = S} (sig θ) S∈

shr-stats : ∀{s} → (θ : Env) → (ShrMap.∈Dom s (shr θ)) → SharedVar.Status
shr-stats{s} θ s∈ = proj₁ (ShrMap.lookup{k = s} (shr θ) s∈)

shr-vals : ∀{s} → (θ : Env) → (ShrMap.∈Dom s (shr θ)) → ℕ
shr-vals{s} θ s∈ = proj₂ (ShrMap.lookup{k = s} (shr θ) s∈)

var-vals : ∀{x} → (θ : Env) → (VarMap.∈Dom x (var θ)) → ℕ
var-vals{x} θ x∈ = VarMap.lookup{k = x} (var θ) x∈

set-sig : ∀{S} → (θ : Env) → (SigMap.∈Dom S (sig θ)) → Signal.Status → Env
set-sig{S} (Θ sig shr var) S∈ status =
  Θ (SigMap.update sig S status) shr var

set-shr : ∀{s} → (θ : Env) → (ShrMap.∈Dom s (shr θ)) → SharedVar.Status → ℕ → Env
set-shr{s} (Θ sig shr var) s∈ status n =
  Θ sig (ShrMap.update shr s (status , n)) var

set-var : ∀{x} → (θ : Env) → (VarMap.∈Dom x (var θ)) → ℕ → Env
set-var{x} (Θ sig shr var) x∈ n =
  Θ sig shr (VarMap.update var x n)

_←_ : Env → Env → Env
Θ sig₁ shr₁ seq₁ ← Θ sig₂ shr₂ seq₂ =
  Θ (SigMap.union sig₁ sig₂)
    (ShrMap.union shr₁ shr₂)
    (VarMap.union seq₁ seq₂)

data EnvVar : Set where
 vsig : Signal → EnvVar
 vshr : SharedVar → EnvVar
 vvar : SeqVar → EnvVar

data ∈map : EnvVar → Env → Set where
  ∈sig : ∀{S θ} → (isSig∈ S θ) → ∈map (vsig S) θ
  ∈shr : ∀{s θ} → (isShr∈ s θ) → ∈map (vshr s) θ
  ∈var : ∀{x θ} → (isVar∈ x θ) → ∈map (vvar x) θ

-- thrms

sig-set-mono' : ∀{S S' θ stat} → ∀{S'∈ : (isSig∈ S' θ)} → (isSig∈ S θ) → (isSig∈ S (set-sig{S'} θ S'∈ stat))
sig-set-mono'{S}{S'}{θ}{stat}{S'∈} i =  SigMap.insert-mono{_}{k = S}{m = sig θ}{S'}{stat} i

shr-set-mono' : ∀{s s' θ stat n} → ∀{s'∈ : (isShr∈ s' θ)} → (isShr∈ s θ) → (isShr∈ s (set-shr{s'} θ s'∈ stat n))
shr-set-mono'{s}{s'}{θ}{stat}{n}{s'∈} i =  ShrMap.insert-mono{_}{k = s}{m = shr θ}{s'}{stat ,′ n} i

seq-set-mono' : ∀{x x' θ n} → ∀{x'∈ : (isVar∈ x' θ)} → (isVar∈ x θ) → (isVar∈ x (set-var{x'} θ x'∈ n))
seq-set-mono'{x}{x'}{θ}{n}{x'∈} i =  VarMap.insert-mono{_}{k = x}{m = var θ}{x'}{n} i

sig-set-mono : ∀{V S' θ stat} → ∀{S'∈ : (isSig∈ S' θ)} → ∈map V θ → (∈map V (set-sig{S'} θ S'∈ stat))
sig-set-mono{S' = S'}{θ}{S'∈ = S'∈} (∈sig{S} x) = ∈sig{S} (sig-set-mono'{S = S}{S' = S'}{θ = θ}{S'∈ = S'∈} x)
sig-set-mono (∈shr x) = ∈shr x
sig-set-mono (∈var x₁) = ∈var x₁

shr-set-mono : ∀{V s' θ stat n} → ∀{s'∈ : (isShr∈ s' θ)} → (∈map V θ) → (∈map V (set-shr{s'} θ s'∈ stat n))
shr-set-mono (∈sig x) = ∈sig x
shr-set-mono{s' = s'}{θ}{stat}{n}{s'∈}(∈shr{s} x) = ∈shr{s} (shr-set-mono'{s}{s'}{θ}{stat}{n}{s'∈}  x)
shr-set-mono (∈var x₁) = ∈var x₁

seq-set-mono : ∀{V x' θ n} → ∀{x'∈ : (isVar∈ x' θ)} → (∈map V θ) → (∈map V (set-var{x'} θ x'∈ n))
seq-set-mono (∈sig x) = ∈sig x
seq-set-mono (∈shr x) = ∈shr x
seq-set-mono{x' = x'}{θ}{n}{x'∈} (∈var{x} x₁) = ∈var {x} (seq-set-mono'{x}{x'}{θ}{n}{x'∈} x₁)

←-mono : ∀{θ θ' V} → ∈map V θ → ∈map V (θ ← θ')
←-mono{θ}{θ'}{vsig S}  (∈sig x) = ∈sig{S}{(θ ← θ')} (SigMap.U-mono{_}{sig θ}{sig θ'}{S} x)
←-mono{θ}{θ'}{vshr s} (∈shr x) = ∈shr{s}{(θ ← θ')} (ShrMap.U-mono{_}{shr θ}{shr θ'}{s} x)
←-mono{θ}{θ'}{vvar x} (∈var x₁) = ∈var{x}{(θ ← θ')} (VarMap.U-mono{_}{var θ}{var θ'}{x} x₁)

←-comm : ∀ θ θ' → distinct (Dom θ) (Dom θ') → (θ ← θ') ≡ (θ' ← θ)
←-comm (Θ Ss ss xs) (Θ Ss' ss' xs') (Ss≠Ss' , ss≠ss' , xs≠xs')
  rewrite SigMap.union-comm Ss Ss' Ss≠Ss'
        | ShrMap.union-comm ss ss' ss≠ss'
        | VarMap.union-comm xs xs' xs≠xs' = refl

←-assoc : ∀ θ θ' θ'' → (θ ← (θ' ← θ'')) ≡ ((θ ← θ') ← θ'')
←-assoc (Θ Ss ss xs) (Θ Ss' ss' xs') (Θ Ss'' ss'' xs'')
  rewrite SigMap.union-assoc Ss Ss' Ss''
        | ShrMap.union-assoc ss ss' ss''
        | VarMap.union-assoc xs xs' xs'' = refl

←-assoc-comm : ∀ θ θ' θ'' → distinct (Dom θ') (Dom θ'') → ((θ ← θ') ← θ'') ≡ ((θ ← θ'') ← θ')
←-assoc-comm θ θ' θ'' Domθ'≠Domθ'' =
    (θ ← θ') ← θ''
   ≡⟨ sym (←-assoc θ θ' θ'') ⟩
     θ ← (θ' ← θ'')
   ≡⟨ cong (θ ←_) (←-comm θ' θ'' Domθ'≠Domθ'') ⟩
     θ ← (θ'' ← θ')
   ≡⟨ ←-assoc θ θ'' θ' ⟩
     (θ ← θ'') ← θ' ∎

Dom-←-assoc-comm : ∀ θ θ' θ'' → Dom ((θ ← θ') ← θ'') ≡ Dom ((θ ← θ'') ← θ')
Dom-←-assoc-comm (Θ Ss ss xs) (Θ Ss' ss' xs') (Θ Ss'' ss'' xs'')
  rewrite SigMap.keys-assoc-comm Ss Ss' Ss''
        | ShrMap.keys-assoc-comm ss ss' ss''
        | VarMap.keys-assoc-comm xs xs' xs'' = refl

Dom-←-comm : ∀ θ θ' → Dom (θ ← θ') ≡ Dom (θ' ← θ)
Dom-←-comm θ θ' = Dom-←-assoc-comm []env θ θ'

sig-←-monoʳ : ∀ S θ θ' → isSig∈ S θ → isSig∈ S (θ' ← θ)
sig-←-monoʳ S θ θ' S∈Domθ
  rewrite cong proj₁ (Dom-←-comm θ' θ)
  = SigMap.U-mono {_} {Env.sig θ} {Env.sig θ'} {S} S∈Domθ

shr-←-monoʳ : ∀ s θ θ' → isShr∈ s θ → isShr∈ s (θ' ← θ)
shr-←-monoʳ s θ θ' s∈Domθ
  rewrite cong (proj₁ ∘ proj₂) (Dom-←-comm θ' θ)
  = ShrMap.U-mono {_} {Env.shr θ} {Env.shr θ'} {s} s∈Domθ

seq-←-monoʳ : ∀ x θ θ' → isVar∈ x θ → isVar∈ x (θ' ← θ)
seq-←-monoʳ x θ θ' x∈Domθ
  rewrite cong (proj₂ ∘ proj₂) (Dom-←-comm θ' θ)
  = VarMap.U-mono {_} {var θ} {var θ'} {x} x∈Domθ

sig-←-monoˡ : ∀ S θ θ' → isSig∈ S θ → isSig∈ S (θ ← θ')
sig-←-monoˡ S θ θ' S∈Domθ
  = SigMap.U-mono {_} {Env.sig θ} {Env.sig θ'} {S} S∈Domθ

shr-←-monoˡ : ∀ s θ θ' → isShr∈ s θ → isShr∈ s (θ ← θ')
shr-←-monoˡ s θ θ' s∈Domθ
  = ShrMap.U-mono {_} {Env.shr θ} {Env.shr θ'} {s} s∈Domθ

seq-←-monoˡ : ∀ x θ θ' → isVar∈ x θ → isVar∈ x (θ ← θ')
seq-←-monoˡ x θ θ' x∈Domθ
  = VarMap.U-mono {_} {var θ} {var θ'} {x} x∈Domθ



sig-←⁻ : ∀ {θ₁ θ₂} S → isSig∈ S (θ₁ ← θ₂) → isSig∈ S θ₁ ⊎ isSig∈ S θ₂
sig-←⁻ {θ₁} {θ₂} S = SigMap.U⁻-m {Signal.Status} {sig θ₁} {sig θ₂} {S}

shr-←⁻ : ∀ {θ₁ θ₂} s → isShr∈ s (θ₁ ← θ₂) → isShr∈ s θ₁ ⊎ isShr∈ s θ₂
shr-←⁻ {θ₁} {θ₂} s = ShrMap.U⁻-m {_} {shr θ₁} {shr θ₂} {s}

seq-←⁻ : ∀ {θ₁ θ₂} x → isVar∈ x (θ₁ ← θ₂) → isVar∈ x θ₁ ⊎ isVar∈ x θ₂
seq-←⁻ {θ₁} {θ₂} x = VarMap.U⁻-m {_} {var θ₁} {var θ₂} {x}

sig-↚⁻ : ∀ {θ₁ θ₂} S → ¬ isSig∈ S θ₁ → ¬ isSig∈ S θ₂ → ¬ isSig∈ S (θ₁ ← θ₂)
sig-↚⁻ {θ₁} {θ₂} S S∉Domθ₁ S∉Domθ₂ = [ S∉Domθ₁ , S∉Domθ₂ ] ∘ sig-←⁻ {θ₁} {θ₂} S


sig-stats-∈-irr : ∀{S θ} → (∈1 : (SigMap.∈Dom S (sig θ))) → (∈2 : (SigMap.∈Dom S (sig θ))) → sig-stats{S} θ ∈1 ≡ sig-stats{S} θ ∈2
sig-stats-∈-irr{S} {θ} ∈1 ∈2 = SigMap.lookup-∈-irr{k = S}{m = (sig θ)} ∈1 ∈2

shr-stats-∈-irr : ∀{s θ} → (∈1 : ShrMap.∈Dom s (shr θ)) → (∈2 : ShrMap.∈Dom s (shr θ)) → shr-stats{s} θ ∈1 ≡ shr-stats{s} θ ∈2
shr-stats-∈-irr{s}{θ} ∈1 ∈2 = cong proj₁ (ShrMap.lookup-∈-irr{k = s}{m = (shr θ)} ∈1 ∈2)
shr-vals-∈-irr : ∀{s θ} → (∈1 : ShrMap.∈Dom s (shr θ)) → (∈2 : ShrMap.∈Dom s (shr θ)) → shr-vals{s} θ ∈1 ≡ shr-vals{s} θ ∈2
shr-vals-∈-irr{s}{θ} ∈1 ∈2 = cong proj₂ (ShrMap.lookup-∈-irr{k = s}{m = (shr θ)} ∈1 ∈2)

var-vals-∈-irr : ∀{x θ} → (∈1 : VarMap.∈Dom x (var θ)) →  (∈2 : VarMap.∈Dom x (var θ)) → var-vals{x} θ ∈1 ≡ var-vals{x} θ ∈2
var-vals-∈-irr{x} {θ} ∈1 ∈2 = VarMap.lookup-∈-irr{_}{x}{var θ} ∈1 ∈2

sig-←-∉-irr-stats' : ∀ S θ θ' →
  (S∈ : isSig∈ S θ) →
  (S∉ : ¬ isSig∈ S θ') →
  (S∈Dom⟨θ←θ'⟩ : isSig∈ S (θ ← θ')) →
  sig-stats {S} θ S∈ ≡ sig-stats {S} (θ ← θ') S∈Dom⟨θ←θ'⟩
sig-←-∉-irr-stats' S θ θ' S∈ S∉ S∈' =
  SigMap.U-∉-irr-get-help-m {_} {Env.sig θ} {Env.sig θ'} {S} S∈ S∉ S∈'

sig-←-∉-irr-stats : ∀ S θ θ' →
  (S∈ : isSig∈ S θ) →
  (S∉ : ¬ isSig∈ S θ') →
  ∃ λ S∈Dom⟨θ←θ'⟩ →
    sig-stats {S} θ S∈ ≡ sig-stats {S} (θ ← θ') S∈Dom⟨θ←θ'⟩
sig-←-∉-irr-stats S θ θ' S∈ S∉ =
  SigMap.U-∉-irr-get-m {_} {Env.sig θ} {Env.sig θ'} {S} S∈ S∉

shr-←-∉-irr-stats' : ∀ s θ θ' →
  (s∈ : isShr∈ s θ) →
  (s∉ : ¬ isShr∈ s θ') →
  (s∈Dom⟨θ←θ'⟩ : isShr∈ s (θ ← θ')) →
  shr-stats {s} θ s∈ ≡ shr-stats {s} (θ ← θ') s∈Dom⟨θ←θ'⟩
shr-←-∉-irr-stats' s θ θ' s∈ s∉ s∈'
  rewrite ShrMap.U-∉-irr-get-help-m {_} {Env.shr θ} {Env.shr θ'} {s} s∈ s∉ s∈'
  = refl

shr-←-∉-irr-stats : ∀ s θ θ' →
  (s∈ : isShr∈ s θ) →
  (s∉ : ¬ isShr∈ s θ') →
  ∃ λ s∈Dom⟨θ←θ'⟩ →
    shr-stats {s} θ s∈ ≡ shr-stats {s} (θ ← θ') s∈Dom⟨θ←θ'⟩
shr-←-∉-irr-stats s θ θ' s∈ s∉
  rewrite proj₂ (ShrMap.U-∉-irr-get-m {_} {Env.shr θ} {Env.shr θ'} {s} s∈ s∉)
  = (_ , refl)

shr-←-∉-irr-vals' : ∀ s θ θ' →
  (s∈ : isShr∈ s θ) →
  (s∉ : ¬ isShr∈ s θ') →
  (s∈Dom⟨θ←θ'⟩ : isShr∈ s (θ ← θ')) →
  shr-vals {s} θ s∈ ≡ shr-vals {s} (θ ← θ') s∈Dom⟨θ←θ'⟩
shr-←-∉-irr-vals' s θ θ' s∈ s∉ s∈'
  rewrite ShrMap.U-∉-irr-get-help-m {_} {Env.shr θ} {Env.shr θ'} {s} s∈ s∉ s∈'
  = refl

shr-←-∉-irr-vals : ∀ s θ θ' →
  (s∈ : isShr∈ s θ) →
  (s∉ : ¬ isShr∈ s θ') →
  ∃ λ s∈Dom⟨θ←θ'⟩ →
    shr-vals {s} θ s∈ ≡ shr-vals {s} (θ ← θ') s∈Dom⟨θ←θ'⟩
shr-←-∉-irr-vals s θ θ' s∈ s∉
  rewrite proj₂ (ShrMap.U-∉-irr-get-m {_} {Env.shr θ} {Env.shr θ'} {s} s∈ s∉)
  = (_ , refl)

var-←-∉-irr-vals' : ∀ x θ θ' →
  (x∈ : isVar∈ x θ) →
  (x∉ : ¬ isVar∈ x θ') →
  (x∈Dom⟨θ←θ'⟩ : isVar∈ x (θ ← θ')) →
  var-vals {x} θ x∈ ≡ var-vals {x} (θ ← θ') x∈Dom⟨θ←θ'⟩
var-←-∉-irr-vals' x θ θ' x∈ x∉ x∈' =
  VarMap.U-∉-irr-get-help-m {_} {Env.var θ} {Env.var θ'} {x} x∈ x∉ x∈'

var-←-∉-irr-vals : ∀ x θ θ' →
  (x∈ : isVar∈ x θ) →
  (x∉ : ¬ isVar∈ x θ') →
  ∃ λ x∈Dom⟨θ←θ'⟩ →
    var-vals {x} θ x∈ ≡ var-vals {x} (θ ← θ') x∈Dom⟨θ←θ'⟩
var-←-∉-irr-vals x θ θ' x∈ x∉ =
  VarMap.U-∉-irr-get-m {_} {Env.var θ} {Env.var θ'} {x} x∈ x∉

sig-stats-←-right-irr' : ∀ S θ θ' →
  (S∈  : isSig∈ S θ') →
  (S∈' : isSig∈ S (θ ← θ')) →
  sig-stats {S} (θ ← θ') S∈' ≡ sig-stats {S} θ' S∈
sig-stats-←-right-irr' S θ θ' S∈ S∈' =
  SigMap.get-U-right-irr-m S (Env.sig θ) (Env.sig θ') S∈' S∈

sig-stats-←-right-irr : ∀ S θ θ' →
  (S∈  : isSig∈ S θ') →
  ∃ λ S∈' →
    sig-stats {S} (θ ← θ') S∈' ≡ sig-stats {S} θ' S∈
sig-stats-←-right-irr S θ θ' S∈ =
  sig-←-monoʳ S θ' θ S∈ ,
  SigMap.get-U-right-irr-m S (Env.sig θ) (Env.sig θ') (sig-←-monoʳ S θ' θ S∈) S∈

shr-stats-←-right-irr' : ∀ s θ θ' →
  (s∈  : isShr∈ s θ') →
  (s∈' : isShr∈ s (θ ← θ')) →
  shr-stats {s} (θ ← θ') s∈' ≡ shr-stats {s} θ' s∈
shr-stats-←-right-irr' s θ θ' s∈ s∈'
  rewrite ShrMap.get-U-right-irr-m s (Env.shr θ) (Env.shr θ') s∈' s∈
  = refl

shr-stats-←-right-irr : ∀ s θ θ' →
  (s∈ : isShr∈ s θ') →
  ∃ λ s∈' →
    shr-stats {s} (θ ← θ') s∈' ≡ shr-stats {s} θ' s∈
shr-stats-←-right-irr s θ θ' s∈ =
  shr-←-monoʳ s θ' θ s∈ ,
  cong proj₁
    (ShrMap.get-U-right-irr-m s (Env.shr θ) (Env.shr θ')
      (shr-←-monoʳ s θ' θ s∈) s∈)

shr-vals-←-right-irr' : ∀ s θ θ' →
  (s∈  : isShr∈ s θ') →
  (s∈' : isShr∈ s (θ ← θ')) →
  shr-vals {s} (θ ← θ') s∈' ≡ shr-vals {s} θ' s∈
shr-vals-←-right-irr' s θ θ' s∈ s∈'
  rewrite ShrMap.get-U-right-irr-m s (Env.shr θ) (Env.shr θ') s∈' s∈
  = refl

shr-vals-←-right-irr : ∀ s θ θ' →
  (s∈ : isShr∈ s θ') →
  ∃ λ s∈' →
    shr-vals {s} (θ ← θ') s∈' ≡ shr-vals {s} θ' s∈
shr-vals-←-right-irr s θ θ' s∈ =
  shr-←-monoʳ s θ' θ s∈ ,
  cong proj₂
    (ShrMap.get-U-right-irr-m s (Env.shr θ) (Env.shr θ')
      (shr-←-monoʳ s θ' θ s∈) s∈)

var-vals-←-right-irr' : ∀ x θ θ' →
  (x∈  : isVar∈ x θ') →
  (x∈' : isVar∈ x (θ ← θ')) →
  var-vals {x} (θ ← θ') x∈' ≡ var-vals {x} θ' x∈
var-vals-←-right-irr' x θ θ' x∈ x∈' =
  VarMap.get-U-right-irr-m x (Env.var θ) (Env.var θ') x∈' x∈

var-vals-←-right-irr : ∀ x θ θ' →
  (x∈  : isVar∈ x θ') →
  ∃ λ x∈' →
    var-vals {x} (θ ← θ') x∈' ≡ var-vals {x} θ' x∈
var-vals-←-right-irr x θ θ' x∈ =
  seq-←-monoʳ x θ' θ x∈ ,
  VarMap.get-U-right-irr-m x (Env.var θ) (Env.var θ') (seq-←-monoʳ x θ' θ x∈) x∈

sig-stats-←-irr' : ∀ S θ θ' θ'' →
  (S∈   : isSig∈ S θ'') →
  (S∈'  : isSig∈ S (θ  ← θ'')) →
  (S∈'' : isSig∈ S (θ' ← θ'')) →
  sig-stats {S} (θ ← θ'') S∈' ≡ sig-stats {S} (θ' ← θ'') S∈''
sig-stats-←-irr' S θ θ' θ'' S∈ S∈' S∈'' =
  SigMap.∈-get-U-irr-m S (sig θ) (sig θ') (sig θ'') S∈' S∈'' S∈

sig-stats-←-irr : ∀ S θ θ' θ'' →
  (S∈   : isSig∈ S θ'') →
  ∃ λ S∈' →
    ∃ λ S∈'' →
      sig-stats {S} (θ ← θ'') S∈' ≡ sig-stats {S} (θ' ← θ'') S∈''
sig-stats-←-irr S θ θ' θ'' S∈ =
  sig-←-monoʳ S θ'' θ S∈ ,
  sig-←-monoʳ S θ'' θ' S∈ ,
  SigMap.∈-get-U-irr-m S (sig θ) (sig θ') (sig θ'')
    (sig-←-monoʳ S θ'' θ S∈) (sig-←-monoʳ S θ'' θ' S∈) S∈

shr-stats-←-irr' : ∀ s θ θ' θ'' →
  (s∈   : isShr∈ s θ'') →
  (s∈'  : isShr∈ s (θ  ← θ'')) →
  (s∈'' : isShr∈ s (θ' ← θ'')) →
  shr-stats {s} (θ ← θ'') s∈' ≡ shr-stats {s} (θ' ← θ'') s∈''
shr-stats-←-irr' s θ θ' θ'' s∈ s∈' s∈''
  rewrite ShrMap.∈-get-U-irr-m s (shr θ) (shr θ') (shr θ'') s∈' s∈'' s∈
  = refl

shr-stats-←-irr : ∀ s θ θ' θ'' →
  (s∈   : isShr∈ s θ'') →
  ∃ λ s∈' →
    ∃ λ s∈'' →
      shr-stats {s} (θ ← θ'') s∈' ≡ shr-stats {s} (θ' ← θ'') s∈''
shr-stats-←-irr s θ θ' θ'' s∈ =
  shr-←-monoʳ s θ'' θ s∈ ,
  shr-←-monoʳ s θ'' θ' s∈ ,
  cong proj₁
    (ShrMap.∈-get-U-irr-m s (shr θ) (shr θ') (shr θ'')
      (shr-←-monoʳ s θ'' θ s∈) (shr-←-monoʳ s θ'' θ' s∈) s∈)

shr-vals-←-irr' : ∀ s θ θ' θ'' →
  (s∈   : isShr∈ s θ'') →
  (s∈'  : isShr∈ s (θ  ← θ'')) →
  (s∈'' : isShr∈ s (θ' ← θ'')) →
  shr-vals {s} (θ ← θ'') s∈' ≡ shr-vals {s} (θ' ← θ'') s∈''
shr-vals-←-irr' s θ θ' θ'' s∈ s∈' s∈''
  rewrite ShrMap.∈-get-U-irr-m s (shr θ) (shr θ') (shr θ'') s∈' s∈'' s∈
  = refl

shr-vals-←-irr : ∀ s θ θ' θ'' →
  (s∈   : isShr∈ s θ'') →
  ∃ λ s∈' →
    ∃ λ s∈'' →
      shr-vals {s} (θ ← θ'') s∈' ≡ shr-vals {s} (θ' ← θ'') s∈''
shr-vals-←-irr s θ θ' θ'' s∈ =
  shr-←-monoʳ s θ'' θ s∈ ,
  shr-←-monoʳ s θ'' θ' s∈ ,
  cong proj₂
    (ShrMap.∈-get-U-irr-m s (shr θ) (shr θ') (shr θ'')
      (shr-←-monoʳ s θ'' θ s∈) (shr-←-monoʳ s θ'' θ' s∈) s∈)

var-vals-←-irr' : ∀ x θ θ' θ'' →
  (x∈   : isVar∈ x θ'') →
  (x∈'  : isVar∈ x (θ  ← θ'')) →
  (x∈'' : isVar∈ x (θ' ← θ'')) →
  var-vals {x} (θ ← θ'') x∈' ≡ var-vals {x} (θ' ← θ'') x∈''
var-vals-←-irr' x θ θ' θ'' x∈ x∈' x∈'' =
  VarMap.∈-get-U-irr-m x (var θ) (var θ') (var θ'') x∈' x∈'' x∈

var-vals-←-irr : ∀ x θ θ' θ'' →
  (x∈   : isVar∈ x θ'') →
  ∃ λ x∈' →
    ∃ λ x∈'' →
      var-vals {x} (θ ← θ'') x∈' ≡ var-vals {x} (θ' ← θ'') x∈''
var-vals-←-irr x θ θ' θ'' x∈ =
  seq-←-monoʳ x θ'' θ x∈ ,
  seq-←-monoʳ x θ'' θ' x∈ ,
  VarMap.∈-get-U-irr-m x (var θ) (var θ') (var θ'')
    (seq-←-monoʳ x θ'' θ x∈) (seq-←-monoʳ x θ'' θ' x∈) x∈

sig-stats-←-both-irr' : ∀ S θ θ' θ'' S∈ S∈' S∈Dom⟨θ←θ''⟩ S∈Dom⟨θ'←θ''⟩ →
  sig-stats {S} θ S∈ ≡ sig-stats {S} θ' S∈' →
    sig-stats {S} (θ ← θ'') S∈Dom⟨θ←θ''⟩ ≡ sig-stats {S} (θ' ← θ'') S∈Dom⟨θ'←θ''⟩
sig-stats-←-both-irr' S θ θ' θ'' S∈ S∈' S∈Dom⟨θ←θ''⟩ S∈Dom⟨θ'←θ''⟩ θS≡θ'S =
  SigMap.get-U-both-irr-m S (Env.sig θ) (Env.sig θ') (Env.sig θ'')
    S∈ S∈' S∈Dom⟨θ←θ''⟩ S∈Dom⟨θ'←θ''⟩ θS≡θ'S

sig-stats-←-both-irr : ∀ S θ θ' θ'' S∈ S∈' →
  sig-stats {S} θ S∈ ≡ sig-stats {S} θ' S∈' →
  ∃ λ S∈Dom⟨θ←θ''⟩ → ∃ λ S∈Dom⟨θ'←θ''⟩ →
    sig-stats {S} (θ ← θ'') S∈Dom⟨θ←θ''⟩ ≡ sig-stats {S} (θ' ← θ'') S∈Dom⟨θ'←θ''⟩
sig-stats-←-both-irr S θ θ' θ'' S∈ S∈' θS≡θ'S =
  S∈Dom⟨θ←θ''⟩ ,
  S∈Dom⟨θ'←θ''⟩ ,
  SigMap.get-U-both-irr-m S (Env.sig θ) (Env.sig θ') (Env.sig θ'')
    S∈ S∈' S∈Dom⟨θ←θ''⟩ S∈Dom⟨θ'←θ''⟩ θS≡θ'S
  where S∈Dom⟨θ←θ''⟩  = sig-←-monoˡ S θ  θ'' S∈
        S∈Dom⟨θ'←θ''⟩ = sig-←-monoˡ S θ' θ'' S∈'

shr-stats-←-both-irr' : ∀ s θ θ' θ'' s∈ s∈' s∈Dom⟨θ←θ''⟩ s∈Dom⟨θ'←θ''⟩ →
  shr-stats {s} θ s∈ ≡ shr-stats {s} θ' s∈' →
  shr-vals {s} θ s∈ ≡ shr-vals {s} θ' s∈' →
    shr-stats {s} (θ ← θ'') s∈Dom⟨θ←θ''⟩ ≡ shr-stats {s} (θ' ← θ'') s∈Dom⟨θ'←θ''⟩
shr-stats-←-both-irr' s θ θ' θ'' s∈ s∈' s∈Dom⟨θ←θ''⟩ s∈Dom⟨θ'←θ''⟩ proj₁θs≡proj₁θ's proj₂θs≡proj₂θ's =
  cong proj₁
    (ShrMap.get-U-both-irr-m s (Env.shr θ) (Env.shr θ') (Env.shr θ'')
      s∈ s∈' s∈Dom⟨θ←θ''⟩ s∈Dom⟨θ'←θ''⟩ (prod-ind proj₁θs≡proj₁θ's proj₂θs≡proj₂θ's))
  where prod-ind : {A B : Set} {x,y x',y' : A × B} →
          proj₁ x,y ≡ proj₁ x',y' → proj₂ x,y ≡ proj₂ x',y' → x,y ≡ x',y'
        prod-ind {_} {_} {x , y} {x' , y'} refl refl = refl

shr-stats-←-both-irr : ∀ s θ θ' θ'' s∈ s∈' →
  shr-stats {s} θ s∈ ≡ shr-stats {s} θ' s∈' →
  shr-vals {s} θ s∈ ≡ shr-vals {s} θ' s∈' →
  ∃ λ s∈Dom⟨θ←θ''⟩ → ∃ λ s∈Dom⟨θ'←θ''⟩ →
    shr-stats {s} (θ ← θ'') s∈Dom⟨θ←θ''⟩ ≡ shr-stats {s} (θ' ← θ'') s∈Dom⟨θ'←θ''⟩
shr-stats-←-both-irr s θ θ' θ'' s∈ s∈' proj₁θs≡proj₁θ's proj₂θs≡proj₂θ's =
  s∈Dom⟨θ←θ''⟩ ,
  s∈Dom⟨θ'←θ''⟩ ,
  cong proj₁
    (ShrMap.get-U-both-irr-m s (Env.shr θ) (Env.shr θ') (Env.shr θ'')
      s∈ s∈' s∈Dom⟨θ←θ''⟩ s∈Dom⟨θ'←θ''⟩ (prod-ind proj₁θs≡proj₁θ's proj₂θs≡proj₂θ's))
  where s∈Dom⟨θ←θ''⟩  = shr-←-monoˡ s θ  θ'' s∈
        s∈Dom⟨θ'←θ''⟩ = shr-←-monoˡ s θ' θ'' s∈'
        prod-ind : {A B : Set} {x,y x',y' : A × B} →
          proj₁ x,y ≡ proj₁ x',y' → proj₂ x,y ≡ proj₂ x',y' → x,y ≡ x',y'
        prod-ind {_} {_} {x , y} {x' , y'} refl refl = refl

shr-vals-←-both-irr' : ∀ s θ θ' θ'' s∈ s∈' s∈Dom⟨θ←θ''⟩ s∈Dom⟨θ'←θ''⟩ →
  shr-stats {s} θ s∈ ≡ shr-stats {s} θ' s∈' →
  shr-vals {s} θ s∈ ≡ shr-vals {s} θ' s∈' →
    shr-vals {s} (θ ← θ'') s∈Dom⟨θ←θ''⟩ ≡ shr-vals {s} (θ' ← θ'') s∈Dom⟨θ'←θ''⟩
shr-vals-←-both-irr' s θ θ' θ'' s∈ s∈' s∈Dom⟨θ←θ''⟩ s∈Dom⟨θ'←θ''⟩ proj₁θs≡proj₁θ's proj₂θs≡proj₂θ's =
  cong proj₂
    (ShrMap.get-U-both-irr-m s (Env.shr θ) (Env.shr θ') (Env.shr θ'')
      s∈ s∈' s∈Dom⟨θ←θ''⟩ s∈Dom⟨θ'←θ''⟩ (prod-ind proj₁θs≡proj₁θ's proj₂θs≡proj₂θ's))
  where prod-ind : {A B : Set} {x,y x',y' : A × B} →
          proj₁ x,y ≡ proj₁ x',y' → proj₂ x,y ≡ proj₂ x',y' → x,y ≡ x',y'
        prod-ind {_} {_} {x , y} {x' , y'} refl refl = refl

shr-vals-←-both-irr : ∀ s θ θ' θ'' s∈ s∈' →
  shr-stats {s} θ s∈ ≡ shr-stats {s} θ' s∈' →
  shr-vals {s} θ s∈ ≡ shr-vals {s} θ' s∈' →
  ∃ λ s∈Dom⟨θ←θ''⟩ → ∃ λ s∈Dom⟨θ'←θ''⟩ →
    shr-vals {s} (θ ← θ'') s∈Dom⟨θ←θ''⟩ ≡ shr-vals {s} (θ' ← θ'') s∈Dom⟨θ'←θ''⟩
shr-vals-←-both-irr s θ θ' θ'' s∈ s∈' proj₁θs≡proj₁θ's proj₂θs≡proj₂θ's =
  s∈Dom⟨θ←θ''⟩ ,
  s∈Dom⟨θ'←θ''⟩ ,
  cong proj₂
    (ShrMap.get-U-both-irr-m s (Env.shr θ) (Env.shr θ') (Env.shr θ'')
      s∈ s∈' s∈Dom⟨θ←θ''⟩ s∈Dom⟨θ'←θ''⟩ (prod-ind proj₁θs≡proj₁θ's proj₂θs≡proj₂θ's))
  where s∈Dom⟨θ←θ''⟩  = shr-←-monoˡ s θ  θ'' s∈
        s∈Dom⟨θ'←θ''⟩ = shr-←-monoˡ s θ' θ'' s∈'
        prod-ind : {A B : Set} {x,y x',y' : A × B} →
          proj₁ x,y ≡ proj₁ x',y' → proj₂ x,y ≡ proj₂ x',y' → x,y ≡ x',y'
        prod-ind {_} {_} {x , y} {x' , y'} refl refl = refl

var-vals-←-both-irr' : ∀ x θ θ' θ'' x∈ x∈' x∈Dom⟨θ←θ''⟩ x∈Dom⟨θ'←θ''⟩ →
  var-vals {x} θ x∈ ≡ var-vals {x} θ' x∈' →
    var-vals {x} (θ ← θ'') x∈Dom⟨θ←θ''⟩ ≡ var-vals {x} (θ' ← θ'') x∈Dom⟨θ'←θ''⟩
var-vals-←-both-irr' x θ θ' θ'' x∈ x∈' x∈Dom⟨θ←θ''⟩ x∈Dom⟨θ'←θ''⟩ θx≡θ'x =
  VarMap.get-U-both-irr-m x (Env.var θ) (Env.var θ') (Env.var θ'')
    x∈ x∈' x∈Dom⟨θ←θ''⟩ x∈Dom⟨θ'←θ''⟩ θx≡θ'x

var-vals-←-both-irr : ∀ x θ θ' θ'' x∈ x∈' →
  var-vals {x} θ x∈ ≡ var-vals {x} θ' x∈' →
  ∃ λ x∈Dom⟨θ←θ''⟩ → ∃ λ x∈Dom⟨θ'←θ''⟩ →
    var-vals {x} (θ ← θ'') x∈Dom⟨θ←θ''⟩ ≡ var-vals {x} (θ' ← θ'') x∈Dom⟨θ'←θ''⟩
var-vals-←-both-irr x θ θ' θ'' x∈ x∈' θx≡θ'x =
  S∈Dom⟨θ←θ''⟩ ,
  S∈Dom⟨θ'←θ''⟩ ,
  VarMap.get-U-both-irr-m x (Env.var θ) (Env.var θ') (Env.var θ'')
    x∈ x∈' S∈Dom⟨θ←θ''⟩ S∈Dom⟨θ'←θ''⟩ θx≡θ'x
  where S∈Dom⟨θ←θ''⟩  = seq-←-monoˡ x θ  θ'' x∈
        S∈Dom⟨θ'←θ''⟩ = seq-←-monoˡ x θ' θ'' x∈'

sig-putputget : ∀{S S' θ stat1 stat2}
                → ¬ S ≡ S'
                → (∈1  : SigMap.∈Dom S (sig θ))
                → (∈S' : SigMap.∈Dom S' (sig θ))
                → (∈2  : SigMap.∈Dom S (sig (set-sig{S'} θ ∈S' stat2)))
                → sig-stats{S} θ ∈1 ≡ stat1
                → sig-stats{S} (set-sig{S'} θ ∈S' stat2) ∈2 ≡ stat1
sig-putputget {θ = θ} neq ∈1 ∈S' ∈2 eq = SigMap.putputget {m = (sig θ)} neq ∈1 ∈2 eq

sig-putputget/m : ∀{S S' θ stat2}
                → ¬ S ≡ S'
                → (∈1  : SigMap.∈Dom S (sig θ))
                → (∈S' : SigMap.∈Dom S' (sig θ))
                → (∈2  : SigMap.∈Dom S (sig (set-sig{S'} θ ∈S' stat2)))
                → sig-stats{S} (set-sig{S'} θ ∈S' stat2) ∈2 ≡ sig-stats{S} θ ∈1
sig-putputget/m {S}{S'}{θ} neq ∈1 ∈S' ∈2 with sig-stats{S} θ ∈1 | inspect (sig-stats{S} θ) ∈1
sig-putputget/m {S} {S'} {θ} neq ∈1 ∈S' ∈2 | k | Relation.Binary.PropositionalEquality.[ eq ] = SigMap.putputget {m = (sig θ)} neq ∈1 ∈2 eq



shr-putputget : ∀{s s' θ v1l v1r v2l v2r}
                → ¬ s ≡ s'
                → (∈1  : ShrMap.∈Dom s (shr θ))
                → (∈s' : ShrMap.∈Dom s' (shr θ))
                → (∈2  : ShrMap.∈Dom s (shr (set-shr{s'} θ ∈s' v2l v2r)))
                → shr-stats{s} θ ∈1 ≡ v1l
                → shr-vals{s} θ ∈1 ≡ v1r
                → (shr-stats{s} (set-shr{s'} θ ∈s' v2l v2r) ∈2) ≡ v1l × (shr-vals{s} (set-shr{s'} θ ∈s' v2l v2r) ∈2) ≡ v1r
shr-putputget {θ = θ}{v1l}{v1r}{v2l}{v2r} neq ∈1 ∈S' ∈2 refl refl with ShrMap.putputget {m = (shr θ)}{v = (v1l ,′ v1r)}{(v2l ,′ v2r)} neq ∈1 ∈2 refl
... | res = (cong proj₁ res) ,′ (cong proj₂ res)

seq-putputget : ∀{x x' θ v1 v2}
                → ¬ x ≡ x'
                → (∈1  : VarMap.∈Dom x  (var θ))
                → (∈x' : VarMap.∈Dom x' (var θ))
                → (∈2  : VarMap.∈Dom x  (var (set-var{x'} θ ∈x' v2)))
                → var-vals{x} θ ∈1 ≡ v1
                → var-vals{x} (set-var{x'} θ ∈x' v2) ∈2 ≡ v1
seq-putputget {θ = θ} neq ∈1 ∈x' ∈2 eq = VarMap.putputget {m = (var θ)} neq ∈1 ∈2 eq

sig-getput : ∀ {θ} S →
  (S∈ : isSig∈ S θ) →
  θ ≡ set-sig {S} θ S∈ (sig-stats {S} θ S∈)
sig-getput {θ} S S∈
  rewrite sym (SigMap.getput-m S (Env.sig θ) S∈)
  = refl

shr-getput : ∀ {θ} s →
  (s∈ : isShr∈ s θ) →
    θ ≡
      set-shr {s} θ s∈
        (shr-stats {s} θ s∈)
        (shr-vals {s} θ s∈)
shr-getput {θ} s s∈
  rewrite sym (ShrMap.getput-m s (Env.shr θ) s∈)
  = refl

var-getput : ∀ {θ} x →
  (x∈ : isVar∈ x θ) →
  θ ≡ set-var {x} θ x∈ (var-vals {x} θ x∈)
var-getput {θ} x x∈
  rewrite sym (VarMap.getput-m x (Env.var θ) x∈)
  = refl

sig-putget : ∀{S θ stat}
             → (∈1 : SigMap.∈Dom S (sig θ))
             → (∈2 : SigMap.∈Dom S (sig (set-sig{S} θ ∈1 stat)))
             → (sig-stats{S} (set-sig{S} θ ∈1 stat) ∈2) ≡ stat
sig-putget {S}{θ}{stat} ∈1 ∈2 = SigMap.putget-m{_}{(sig θ)}{S}{stat} ∈2

shr-putget : ∀{s θ stat n}
             → (∈1 : ShrMap.∈Dom s (shr θ))
             → (∈2 : ShrMap.∈Dom s (shr (set-shr{s} θ ∈1 stat n)))
             → (shr-stats{s} (set-shr{s} θ ∈1 stat n) ∈2) ≡ stat × (shr-vals{s} (set-shr{s} θ ∈1 stat n) ∈2) ≡ n
shr-putget {s}{θ}{stat}{n} ∈1 ∈2 with ShrMap.putget-m{_}{(shr θ)}{s}{stat ,′ n} ∈2
... | eq rewrite eq = refl , refl

shr-putput-overwrite : ∀ s θ stat1 n1 stat2 n2
                       → (∈1 : (isShr∈ s θ))
                       → (∈2 : isShr∈ s (set-shr{s} θ ∈1 stat1 n1))
                       → (set-shr{s} (set-shr{s} θ ∈1 stat1 n1) ∈2 stat2 n2)
                         ≡ (set-shr{s} θ ∈1 stat2 n2)
shr-putput-overwrite s θ stat1 n1 stat2 n2 _ _ rewrite
  ShrMap.putput-overwrite (shr θ) s (stat1 ,′ n1) (stat2 ,′ n2) = refl




sig-set-←-← : ∀ S v θ θ' →
  (S∈Domθ  : isSig∈ S θ) →
  (S∈Domθ' : isSig∈ S θ') →
    θ ← θ' ≡
    (set-sig {S} θ S∈Domθ v) ← θ'
sig-set-←-← S v θ θ' S∈Domθ S∈Domθ'
  rewrite SigMap.update-union-union S v (Env.sig θ) (Env.sig θ') S∈Domθ S∈Domθ'
  = refl

shr-set-←-← : ∀ s v n θ θ' →
  (s∈Domθ  : isShr∈ s θ) →
  (s∈Domθ' : isShr∈ s θ') →
    θ ← θ' ≡
    (set-shr {s} θ s∈Domθ v n) ← θ'
shr-set-←-← s v n θ θ' s∈Domθ s∈Domθ'
  rewrite ShrMap.update-union-union s (v , n) (Env.shr θ) (Env.shr θ') s∈Domθ s∈Domθ'
  = refl

var-set-←-← : ∀ x v θ θ' →
  (x∈Domθ  : isVar∈ x θ) →
  (x∈Domθ' : isVar∈ x θ') →
    θ ← θ' ≡
    (set-var {x} θ x∈Domθ v) ← θ'
var-set-←-← x v θ θ' x∈Domθ x∈Domθ'
  rewrite VarMap.update-union-union x v (Env.var θ) (Env.var θ') x∈Domθ x∈Domθ'
  = refl

sig∈-eq : ∀{S θ} → (∈1 : SigMap.∈Dom S (sig θ)) → (∈2 : SigMap.∈Dom S (sig θ)) → ∈1 ≡ ∈2
sig∈-eq {S}{θ} ∈1 ∈2 = SigMap.ineq-m{_}{S}{sig θ} ∈1 ∈2

shr∈-eq : ∀{s θ} → (∈1 : ShrMap.∈Dom s (shr θ)) → (∈2 : ShrMap.∈Dom s (shr θ)) → ∈1 ≡ ∈2
shr∈-eq {s}{θ} ∈1 ∈2 = ShrMap.ineq-m{_}{s}{shr θ} ∈1 ∈2

seq∈-eq : ∀{x θ} → (∈1 : VarMap.∈Dom x (var θ)) → (∈2 : VarMap.∈Dom x (var θ)) → ∈1 ≡ ∈2
seq∈-eq {x}{θ} ∈1 ∈2 = VarMap.ineq-m{_}{x}{var θ} ∈1 ∈2


sig∈-eq' : ∀{S θ} → (∈1 : SigMap.∈Dom{Signal.Status} S θ) → (∈2 : SigMap.∈Dom S θ) → ∈1 ≡ ∈2
sig∈-eq' {S}{θ} ∈1 ∈2 = SigMap.ineq-m{_}{S}{θ} ∈1 ∈2

shr∈-eq' : ∀{s θ} → (∈1 : ShrMap.∈Dom{(SharedVar.Status × ℕ)} s θ) → (∈2 : ShrMap.∈Dom s θ) → ∈1 ≡ ∈2
shr∈-eq' {s}{θ} ∈1 ∈2 = ShrMap.ineq-m{_}{s}{θ} ∈1 ∈2

seq∈-eq' : ∀{x : SeqVar} {θ : VarMap.Map ℕ} → (∈1 : VarMap.∈Dom{ℕ} x θ) → (∈2 : VarMap.∈Dom x θ) → ∈1 ≡ ∈2
seq∈-eq' {x}{θ} ∈1 ∈2 = VarMap.ineq-m{_}{x}{θ} ∈1 ∈2

sig-set-comm : ∀{θ S1 S2 stat1 stat2} → (S1∈ : isSig∈ S1 θ) → (S2∈ : isSig∈ S2 θ)
               → ¬ S1 ≡ S2 → ∃ λ S1∈' → ∃ λ S2∈'
               → (set-sig{S2} (set-sig{S1} θ S1∈ stat1) S2∈' stat2) ≡ (set-sig{S1} (set-sig{S2} θ S2∈ stat2) S1∈' stat1)
sig-set-comm{θ}{S1}{S2}{stat1}{stat2} S1∈ S2∈ ¬S1≡S2
    rewrite SigMap.put-comm{_}{sig θ}{S1}{S2}{stat1}{stat2} ¬S1≡S2 = sig-set-mono'{S1}{S2}{θ}{stat2}{S2∈} S1∈ , sig-set-mono'{S2}{S1}{θ}{S'∈ = S1∈} S2∈ , refl

shr-set-comm : ∀ θ s1 s2 stat1 n1 stat2 n2 → (s1∈ : isShr∈ s1 θ) → (s2∈ : isShr∈ s2 θ)
               → ¬ s1 ≡ s2 → ∃ λ s1∈' → ∃ λ s2∈'
               → (set-shr{s2} (set-shr{s1} θ s1∈ stat1 n1) s2∈' stat2 n2) ≡ (set-shr{s1} (set-shr{s2} θ s2∈ stat2 n2) s1∈' stat1 n1)
shr-set-comm θ s1 s2 stat1 n1 stat2 n2 s1∈ s2∈ ¬s1≡s2
    rewrite ShrMap.put-comm{_}{shr θ}{s1}{s2}{stat1 , n1}{stat2 , n2} ¬s1≡s2 = shr-set-mono'{s1}{s2}{θ}{_}{_}{s2∈} s1∈ , shr-set-mono'{s2}{s1}{θ}{s'∈ = s1∈} s2∈ , refl



seq-set-comm : ∀ θ x1 x2 n1 n2 → (x1∈ : isVar∈ x1 θ) → (x2∈ : isVar∈ x2 θ)
               → ¬ x1 ≡ x2 → ∃ λ x1∈' → ∃ λ x2∈'
               → (set-var{x2} (set-var{x1} θ x1∈ n1) x2∈' n2) ≡ (set-var{x1} (set-var{x2} θ x2∈ n2) x1∈' n1)
seq-set-comm θ x1 x2 n1 n2  x1∈ x2∈ ¬x1≡x2
    rewrite VarMap.put-comm{_}{var θ}{x1}{x2}{n1}{n2} ¬x1≡x2 = seq-set-mono'{x1}{x2}{θ}{n2}{x2∈} x1∈ , seq-set-mono'{x2}{x1}{θ}{x'∈ = x1∈} x2∈ , refl


sig-←-irr-get : ∀ {θ₁ θ₂ S} → (S∈Domθ₁ : isSig∈ S θ₁) → ¬ (isSig∈ S θ₂) → ∃ λ S∈Dom⟨θ₁←θ₂⟩ → sig-stats {S} θ₁ S∈Domθ₁ ≡ sig-stats {S} (θ₁ ← θ₂) S∈Dom⟨θ₁←θ₂⟩
sig-←-irr-get {θ₁@(Θ Ss _ _)} {θ₂@(Θ Ss' _ _)} {S} S∈Domθ₁ S∉Domθ₂ with SigMap.U-∉-irr-get-m {_} {Ss} {Ss'} {S} S∈Domθ₁ S∉Domθ₂
... | a , b rewrite b = a , refl

shr-←-irr-get : ∀ {θ₁ θ₂ s} → (s∈Domθ₁ : isShr∈ s θ₁) → ¬ (isShr∈ s θ₂) → ∃ λ s∈Dom⟨θ₁←θ₂⟩ → shr-stats {s} θ₁ s∈Domθ₁ ≡ shr-stats {s} (θ₁ ← θ₂) s∈Dom⟨θ₁←θ₂⟩
shr-←-irr-get {θ₁@(Θ _ ss _)} {θ₂@(Θ _ ss' _)} {s} s∈Domθ₁ s∉Domθ₂ with ShrMap.U-∉-irr-get-m {_} {ss} {ss'} {s} s∈Domθ₁ s∉Domθ₂
... | a , b rewrite b = a , refl


seq-←-irr-get : ∀ {θ₁ θ₂ x} → (x∈Domθ₁ : isVar∈ x θ₁) → ¬ (isVar∈ x θ₂) → ∃ λ x∈Dom⟨θ₁←θ₂⟩ → var-vals {x} θ₁ x∈Domθ₁ ≡ var-vals {x} (θ₁ ← θ₂) x∈Dom⟨θ₁←θ₂⟩
seq-←-irr-get {θ₁@(Θ _ _ xs)} {θ₂@(Θ _ _ xs')} {x} x∈Domθ₁ x∉Domθ₂ with VarMap.U-∉-irr-get-m {_} {xs} {xs'} {x} x∈Domθ₁ x∉Domθ₂
... | a , b rewrite b = a , refl

sig-←-irr-get' : ∀ {θ₁ θ₂ S} → (S∈Domθ₁ : isSig∈ S θ₁) → ¬ (isSig∈ S θ₂) → (S∈Dom⟨θ₁←θ₂⟩ : isSig∈ S (θ₁ ← θ₂)) → sig-stats {S} θ₁ S∈Domθ₁ ≡ sig-stats {S} (θ₁ ← θ₂) S∈Dom⟨θ₁←θ₂⟩
sig-←-irr-get' {θ₁@(Θ Ss _ _)} {θ₂@(Θ Ss' _ _)} {S} S∈Domθ₁ S∉Domθ₂ S∈Dom⟨θ₁←θ₂⟩ with SigMap.U-∉-irr-get-m {_} {Ss} {Ss'} {S} S∈Domθ₁ S∉Domθ₂
... | a , b rewrite b | sig∈-eq{S}{θ₁ ← θ₂} a S∈Dom⟨θ₁←θ₂⟩ = refl

shr-←-irr-get' : ∀ {θ₁ θ₂ s} → (s∈Domθ₁ : isShr∈ s θ₁) → ¬ (isShr∈ s θ₂) → (s∈Dom⟨θ₁←θ₂⟩ : isShr∈ s (θ₁ ← θ₂)) → shr-stats {s} θ₁ s∈Domθ₁ ≡ shr-stats {s} (θ₁ ← θ₂) s∈Dom⟨θ₁←θ₂⟩
shr-←-irr-get' {θ₁@(Θ _ ss _)} {θ₂@(Θ _ ss' _)} {s} s∈Domθ₁ s∉Domθ₂ s∈Dom⟨θ₁←θ₂⟩ with ShrMap.U-∉-irr-get-m {_} {ss} {ss'} {s} s∈Domθ₁ s∉Domθ₂
... | a , b rewrite (cong proj₁ b) | shr∈-eq{s}{θ₁ ← θ₂} a s∈Dom⟨θ₁←θ₂⟩ = refl

shr-←-irr-get/vals' : ∀ {θ₁ θ₂ s} → (s∈Domθ₁ : isShr∈ s θ₁) → ¬ (isShr∈ s θ₂) → (s∈Dom⟨θ₁←θ₂⟩ : isShr∈ s (θ₁ ← θ₂)) → shr-vals {s} θ₁ s∈Domθ₁ ≡ shr-vals {s} (θ₁ ← θ₂) s∈Dom⟨θ₁←θ₂⟩
shr-←-irr-get/vals' {θ₁@(Θ _ ss _)} {θ₂@(Θ _ ss' _)} {s} s∈Domθ₁ s∉Domθ₂ s∈Dom⟨θ₁←θ₂⟩ with ShrMap.U-∉-irr-get-m {_} {ss} {ss'} {s} s∈Domθ₁ s∉Domθ₂
... | a , b rewrite (cong proj₂ b) | shr∈-eq{s}{θ₁ ← θ₂} a s∈Dom⟨θ₁←θ₂⟩ = refl

seq-←-irr-get' : ∀ {θ₁ θ₂ x} → (x∈Domθ₁ : isVar∈ x θ₁) → ¬ (isVar∈ x θ₂) → (x∈Dom⟨θ₁←θ₂⟩ : isVar∈ x (θ₁ ← θ₂)) → var-vals {x} θ₁ x∈Domθ₁ ≡ var-vals {x} (θ₁ ← θ₂) x∈Dom⟨θ₁←θ₂⟩
seq-←-irr-get' {θ₁@(Θ _ _ xs)} {θ₂@(Θ _ _ xs')} {x} x∈Domθ₁ x∉Domθ₂ x∈Dom⟨θ₁←θ₂⟩ with VarMap.U-∉-irr-get-m {_} {xs} {xs'} {x} x∈Domθ₁ x∉Domθ₂
... | a , b rewrite b | seq∈-eq{x}{θ₁ ← θ₂} a x∈Dom⟨θ₁←θ₂⟩ = refl

sig-set-←-comm' : ∀ S v θ θ' →
  (S∈ : isSig∈ S θ) →
  ¬ (isSig∈ S θ') →
  (S∈' : isSig∈ S (θ ← θ')) →
    (set-sig {S} θ S∈ v) ← θ' ≡
    set-sig {S} (θ ← θ') S∈' v
sig-set-←-comm' S v θ θ' S∈ S∉Domθ' S∈'
  rewrite SigMap.put-union-comm {_} S v (Env.sig θ) (Env.sig θ') S∉Domθ'
  = refl

sig-set-←-comm : ∀ S v θ θ' →
  (S∈ : isSig∈ S θ) →
  ¬ (isSig∈ S θ') →
  ∃ λ S∈Dom⟨θ←θ'⟩ →
    (set-sig {S} θ S∈ v) ← θ' ≡
    set-sig {S} (θ ← θ') S∈Dom⟨θ←θ'⟩ v
sig-set-←-comm S v θ θ' S∈ S∉Domθ'
  rewrite SigMap.put-union-comm {_} S v (Env.sig θ) (Env.sig θ') S∉Domθ'
  = SigMap.U-mono {_} {Env.sig θ} {Env.sig θ'} {S} S∈ , refl

shr-set-←-comm' : ∀ s v n θ θ' →
  (s∈ : isShr∈ s θ) →
  ¬ (isShr∈ s θ') →
  (s∈' : isShr∈ s (θ ← θ')) →
  (set-shr {s} θ s∈ v n) ← θ' ≡
  set-shr {s} (θ ← θ') s∈' v n
shr-set-←-comm' s v n θ θ' s∈ s∉Domθ' s∈'
  rewrite ShrMap.put-union-comm {_} s (v , n) (Env.shr θ) (Env.shr θ') s∉Domθ'
  = refl

shr-set-←-comm : ∀ s v n θ θ' →
  (s∈ : isShr∈ s θ) →
  ¬ (isShr∈ s θ') →
  ∃ λ s∈Dom⟨θ←θ'⟩ →
    (set-shr {s} θ s∈ v n) ← θ' ≡
    set-shr {s} (θ ← θ') s∈Dom⟨θ←θ'⟩ v n
shr-set-←-comm s v n θ θ' s∈ s∉Domθ'
  rewrite ShrMap.put-union-comm {_} s (v , n) (Env.shr θ) (Env.shr θ') s∉Domθ'
  = ShrMap.U-mono {_} {Env.shr θ} {Env.shr θ'} {s} s∈ , refl

var-set-←-comm' : ∀ x v θ θ' →
  (x∈ : isVar∈ x θ) →
  ¬ (isVar∈ x θ') →
  (x∈' : isVar∈ x (θ ← θ')) →
    (set-var {x} θ x∈ v) ← θ' ≡
    set-var {x} (θ ← θ') x∈' v
var-set-←-comm' x v θ θ' x∈ x∉Domθ' x∈'
  rewrite VarMap.put-union-comm {_} x v (Env.var θ) (Env.var θ') x∉Domθ'
  = refl

var-set-←-comm : ∀ x v θ θ' →
  (x∈ : isVar∈ x θ) →
  ¬ (isVar∈ x θ') →
  ∃ λ x∈Dom⟨θ←θ'⟩ →
    (set-var {x} θ x∈ v) ← θ' ≡
    set-var {x} (θ ← θ') x∈Dom⟨θ←θ'⟩ v
var-set-←-comm x v θ θ' x∈ x∉Domθ'
  rewrite VarMap.put-union-comm {_} x v (Env.var θ) (Env.var θ') x∉Domθ'
  = VarMap.U-mono {_} {Env.var θ} {Env.var θ'} {x} x∈ , refl

lookup-S-eq : ∀{a b} θ S S∈ S∈₁ → sig-stats{S = S} θ S∈ ≡ a → sig-stats{S = S} θ S∈₁ ≡ b → ¬ a ≡ b → ⊥
lookup-S-eq θ S S∈ S∈' eq1 eq2 neg rewrite sig∈-eq{S}{θ} S∈ S∈'  = neg (trans (sym eq1) eq2)

lookup-s-eq : ∀{a b} θ s s∈ s∈₁ → shr-stats{s = s} θ s∈ ≡ a → shr-stats{s = s} θ s∈₁ ≡ b → ¬ a ≡ b → ⊥
lookup-s-eq θ s s∈ s∈' eq1 eq2 neg rewrite shr∈-eq{s}{θ} s∈ s∈'  = neg (trans (sym eq1) eq2)

lookup-S-¬eq : ∀{a b} θ S S' S∈ S'∈ → sig-stats{S = S} θ S∈ ≡ a → sig-stats{S = S'} θ S'∈ ≡ b → ¬ a ≡ b → ¬ S ≡ S'
lookup-S-¬eq θ S S' S∈ S'∈ S≡ S'≡ a≠b with S Signal.≟ S'
... | yes refl = ⊥-elim (lookup-S-eq θ S S∈ S'∈ S≡ S'≡ a≠b) 
... | no x = x

lookup-s-stat-¬eq : ∀{a b} θ s s' s∈ s'∈ → shr-stats{s = s} θ s∈ ≡ a → shr-stats{s = s'} θ s'∈ ≡ b → ¬ a ≡ b → ¬ s ≡ s'
lookup-s-stat-¬eq θ s s' s∈ s'∈ s≡ s'≡ a≠b with s SharedVar.≟ s'
... | yes refl = ⊥-elim (lookup-s-eq θ s s∈ s'∈ s≡ s'≡ a≠b) 
... | no x = x



←-=-irr-S : ∀ θ θ' → (Dom θ) ≡ (Dom θ') → ∀ S → (S∈ : isSig∈ S (θ ← θ')) → (S∈2 : isSig∈ S θ')
            → sig-stats{S} (θ ← θ') S∈ ≡ sig-stats{S} θ' S∈2
←-=-irr-S θ θ' eq = SigMap.union-=-irr (sig θ) (sig θ') (cong proj₁ eq)

←-=-irr-s-stats : ∀ θ θ' → (Dom θ) ≡ (Dom θ') → ∀ s → (s∈ : isShr∈ s (θ ← θ')) → (s∈2 : isShr∈ s θ')
            → shr-stats{s} (θ ← θ') s∈ ≡ shr-stats{s} θ' s∈2
←-=-irr-s-stats θ θ' eq a b = (cong proj₁) ∘ (ShrMap.union-=-irr (shr θ) (shr θ') (cong (proj₁ ∘ proj₂) eq) a b)
←-=-irr-s-vals : ∀ θ θ' → (Dom θ) ≡ (Dom θ') → ∀ s → (s∈ : isShr∈ s (θ ← θ')) → (s∈2 : isShr∈ s θ')
            → shr-vals{s} (θ ← θ') s∈ ≡ shr-vals{s} θ' s∈2
←-=-irr-s-vals θ θ' eq a b = (cong proj₂) ∘ (ShrMap.union-=-irr (shr θ) (shr θ') (cong (proj₁ ∘ proj₂) eq) a b)

←-=-irr-x : ∀ θ θ' → (Dom θ) ≡ (Dom θ') → ∀ x → (x∈ : isVar∈ x (θ ← θ')) → (x∈2 : isVar∈ x θ')
            → var-vals{x} (θ ← θ') x∈ ≡ var-vals{x} θ' x∈2
←-=-irr-x θ θ' eq = (VarMap.union-=-irr (var θ) (var θ') (cong (proj₂ ∘ proj₂) eq))

←-single-overwrite-sig : ∀ S stat θ → isSig∈ S θ → ((Θ SigMap.[ S ↦ stat ] [] []) ← θ) ≡ θ
←-single-overwrite-sig S stat θ k∈ rewrite SigMap.single-val-overwrite S stat (sig θ) k∈ = refl

←-single-overwrite-shr : ∀ s stat v θ → isShr∈ s θ → ((Θ [] ShrMap.[ s ↦ (stat ,′ v) ] []) ← θ) ≡ θ
←-single-overwrite-shr s stat v θ k∈ rewrite ShrMap.single-val-overwrite s (stat ,′ v) (shr θ) k∈ = refl

←-single-overwrite-seq : ∀ x n θ → isVar∈ x θ → ((Θ [] [] VarMap.[ x ↦ n ]) ← θ) ≡ θ
←-single-overwrite-seq x n θ k∈ rewrite VarMap.single-val-overwrite x n (var θ) k∈ = refl

sig-set=← : ∀ θ S stat → (S∈ : isSig∈ S θ) → (set-sig{S = S} θ S∈ stat) ≡ (θ ← (Θ SigMap.[ S ↦ stat ] [] []))
sig-set=← θ S stat S∈
    rewrite SigMap.union-insert-eq S stat (sig θ)
          | ShrMap.union-comm (shr θ) [] (λ z _ → λ ())
          | VarMap.union-comm (var θ) [] (λ z _ → λ ())
    = refl

shr-set=← : ∀ θ s stat n → (s∈ : isShr∈ s θ) → (set-shr{s = s} θ s∈ stat n) ≡ (θ ← (Θ [] ShrMap.[ s ↦ (stat ,′ n) ] []))
shr-set=← θ s stat n s∈
    rewrite ShrMap.union-insert-eq s (stat ,′ n) (shr θ)
          | SigMap.union-comm (sig θ) [] (λ z _ → λ ())
          | VarMap.union-comm (var θ) [] (λ z _ → λ ())
    = refl

seq-set=← : ∀ θ x n → (x∈ : isVar∈ x θ) → (set-var{x = x} θ x∈ n) ≡ (θ ← (Θ [] [] VarMap.[ x ↦ n ]))
seq-set=← θ x n x∈
    rewrite VarMap.union-insert-eq x n (var θ)
          | SigMap.union-comm (sig θ) [] (λ z _ → λ ())
          | ShrMap.union-comm (shr θ) [] (λ z _ → λ ())
    = refl

sig-set-clobber : ∀ S stat θ θi S∈ → isSig∈ S θi → (set-sig{S = S} θ S∈ stat) ← θi ≡ θ ← θi
sig-set-clobber S stat θ θi S∈θ S∈θi
  =
   (set-sig{S = S} θ S∈θ stat) ← θi
   ≡⟨ cong (_← θi)(sig-set=← θ S stat S∈θ) ⟩
   (θ ← θ2) ← θi
   ≡⟨ sym (←-assoc θ θ2 θi) ⟩
   (θ ← (θ2 ← θi))
   ≡⟨ cong (θ ←_) (←-single-overwrite-sig S stat θi S∈θi) ⟩
   (θ ← θi) ∎
 where θ2 = Θ SigMap.[ S ↦ stat ] [] []
  
shr-set-clobber : ∀ v stat n θ θi v∈ → isShr∈ v θi → (set-shr{s = v} θ v∈ stat n) ← θi ≡ θ ← θi
shr-set-clobber v stat n θ θi v∈θ v∈θi
  =
   (set-shr{s = v} θ v∈θ stat n) ← θi
   ≡⟨ cong (_← θi) (shr-set=← θ v stat n v∈θ) ⟩
   (θ ← θ2) ← θi
   ≡⟨ sym (←-assoc θ θ2 θi) ⟩
   (θ ← (θ2 ← θi))
   ≡⟨ cong (θ ←_) (←-single-overwrite-shr v stat n θi v∈θi) ⟩
   (θ ← θi) ∎
 where θ2 = Θ [] ShrMap.[ v ↦ (stat ,′ n) ] []

  
seq-set-clobber : ∀ v n θ θi v∈ → isVar∈ v θi → (set-var{x = v} θ v∈ n) ← θi ≡ θ ← θi
seq-set-clobber v n θ θi v∈θ v∈θi
  =
   (set-var{x = v} θ v∈θ n) ← θi
   ≡⟨ cong (_← θi) (seq-set=← θ v n v∈θ) ⟩
   (θ ← θ2) ← θi
   ≡⟨ sym (←-assoc θ θ2 θi) ⟩
   (θ ← (θ2 ← θi))
   ≡⟨ cong (θ ←_) (←-single-overwrite-seq v n θi v∈θi) ⟩
   (θ ← θi) ∎
 where θ2 = Θ [] [] VarMap.[ v ↦ n ] 




sig-switch : ∀ S stat θ θi S∈ S∈2 → ¬ isSig∈ S θi → set-sig{S = S} (θ ← θi) S∈2 stat ≡ (set-sig{S = S} θ S∈ stat) ← θi
sig-switch S stat θ θi S∈ S∈2 S∉
  = set-sig{S = S} (θ ← θi) S∈2 stat
   ≡⟨ sig-set=← (θ ← θi) S stat S∈2 ⟩
    (θ ← θi) ← θ2
   ≡⟨ ←-assoc-comm θ θi θ2 ((λ z x x₁ → S∉ (subst (_∈ (SigMap.keys (sig θi))) (∈:: (subst (z ∈_) (SigMap.keys-1map S stat) x₁)) x)) , ((λ x x₁ → λ ()) , (λ x x₁ → λ ()))) ⟩
    (θ ← θ2) ← θi
   ≡⟨ cong (_← θi) (sym (sig-set=← θ S stat S∈ )) ⟩
   (set-sig{S = S} θ S∈ stat) ← θi ∎
  where θ2 = Θ SigMap.[ S ↦ stat ] [] []

shr-switch : ∀ s stat n θ θi s∈ s∈2 → ¬ isShr∈ s θi → set-shr{s = s} (θ ← θi) s∈2 stat n ≡ (set-shr{s = s} θ s∈ stat n) ← θi
shr-switch s stat n θ θi s∈ s∈2 s∉
  = set-shr{s = s} (θ ← θi) s∈2 stat n
   ≡⟨ shr-set=← (θ ← θi) s stat n s∈2 ⟩
    (θ ← θi) ← θ2
   ≡⟨ ←-assoc-comm θ θi θ2 ((λ x x₁ → λ ()) , ((λ z x x₁ → s∉ (subst (_∈ (ShrMap.keys (shr θi))) (∈:: (subst (z ∈_) (ShrMap.keys-1map s (stat ,′ n)) x₁)) x)) , (λ x x₁ → λ ()))) ⟩
    (θ ← θ2) ← θi
   ≡⟨ cong (_← θi) (sym (shr-set=← θ s stat n s∈ )) ⟩
   (set-shr{s = s} θ s∈ stat n) ← θi ∎
  where θ2 = Θ [] ShrMap.[ s ↦ (stat ,′ n) ] []

seq-switch : ∀ x n θ θi x∈ x∈2 → ¬ isVar∈ x θi → set-var{x = x} (θ ← θi) x∈2 n ≡ (set-var{x = x} θ x∈ n) ← θi
seq-switch x n θ θi x∈ x∈2 x∉
  = set-var{x = x} (θ ← θi) x∈2 n
   ≡⟨ seq-set=← (θ ← θi) x n x∈2 ⟩
    (θ ← θi) ← θ2
   ≡⟨ ←-assoc-comm θ θi θ2 ((λ x x₁ → λ ()) , ((λ x x₁ → λ ()) , (λ z j x₁ → x∉ (subst (_∈ (VarMap.keys (var θi))) (∈:: (subst (z ∈_) (VarMap.keys-1map x n) x₁)) j)))) ⟩
    (θ ← θ2) ← θi
   ≡⟨ cong (_← θi) (sym (seq-set=← θ x n x∈ )) ⟩
   (set-var{x = x} θ x∈ n) ← θi ∎
  where θ2 = Θ [] [] VarMap.[ x ↦ n ]

sig-switch-right : ∀ S stat θl θr S∈ S∈2 → (θl ← (set-sig{S} θr S∈ stat)) ≡ (set-sig{S} (θl ← θr) S∈2 stat)
sig-switch-right S stat θl θr S∈ S∈2 =
  (θl ← (set-sig{S} θr S∈ stat))
  ≡⟨ cong (θl ←_) (sig-set=← θr S stat S∈) ⟩
  (θl ← (θr ← (Θ SigMap.[ S ↦ stat ] [] [])))
  ≡⟨ ←-assoc θl θr _ ⟩
  ((θl ← θr) ← (Θ SigMap.[ S ↦ stat ] [] []))
  ≡⟨ sym (sig-set=← (θl ← θr) S stat S∈2) ⟩
  (set-sig{S} (θl ← θr) S∈2 stat) ∎

shr-switch-right : ∀ s stat n θl θr s∈ s∈2 → (θl ← (set-shr{s} θr s∈ stat n)) ≡ (set-shr{s} (θl ← θr) s∈2 stat n)
shr-switch-right s stat n θl θr s∈ s∈2 =
  (θl ← (set-shr{s} θr s∈ stat n))
  ≡⟨ cong (θl ←_) (shr-set=← θr s stat n s∈) ⟩
  (θl ← (θr ← (Θ [] ShrMap.[ s ↦ (stat ,′ n) ] [])))
  ≡⟨ ←-assoc θl θr _ ⟩
  ((θl ← θr) ← (Θ [] ShrMap.[ s ↦ (stat ,′ n) ] []))
  ≡⟨ sym (shr-set=← (θl ← θr) s stat n s∈2) ⟩
  (set-shr{s} (θl ← θr) s∈2 stat n) ∎

seq-switch-right : ∀ x n θl θr x∈ x∈2 → (θl ← (set-var{x} θr x∈ n)) ≡ (set-var{x} (θl ← θr) x∈2 n)
seq-switch-right x n θl θr x∈ x∈2 =
  (θl ← (set-var{x} θr x∈ n))
  ≡⟨ cong (θl ←_) (seq-set=← θr x n x∈) ⟩
  (θl ← (θr ← (Θ [] [] VarMap.[ x ↦ n ])))
  ≡⟨ ←-assoc θl θr _ ⟩
  ((θl ← θr) ← (Θ [] [] VarMap.[ x ↦ n ]))
  ≡⟨ sym (seq-set=← (θl ← θr) x n x∈2) ⟩
  (set-var{x} (θl ← θr) x∈2 n) ∎

sig-set-dom-eq : ∀ S stat θ S∈ → (Dom θ) ≡ (Dom (set-sig{S = S} θ S∈ stat))
sig-set-dom-eq S stat θ S∈ rewrite SigMap.update-domain-eq S stat (sig θ) S∈ = refl

shr-set-dom-eq : ∀ s stat n θ s∈ → (Dom θ) ≡ (Dom (set-shr{s = s} θ s∈ stat n))
shr-set-dom-eq s stat n θ s∈ rewrite ShrMap.update-domain-eq s (stat ,′ n) (shr θ) s∈ = refl

seq-set-dom-eq : ∀ x n θ x∈ → (Dom θ) ≡ (Dom (set-var{x = x} θ x∈ n))
seq-set-dom-eq x n θ x∈ rewrite VarMap.update-domain-eq x n (var θ) x∈ = refl

sig-∉-maint : ∀ S S' stat θ S'∈ → ¬ isSig∈ S θ → ¬ isSig∈ S (set-sig{S = S'} θ S'∈ stat)
sig-∉-maint S S' stat θ S'∈ S∉ x rewrite cong proj₁ (sig-set-dom-eq S' stat θ S'∈) = S∉ x

shr-∉-maint : ∀ s s' stat n θ s'∈ → ¬ isShr∈ s θ → ¬ isShr∈ s (set-shr{s = s'} θ s'∈ stat n)
shr-∉-maint s s' stat n θ s'∈ s∉ x rewrite cong snd (shr-set-dom-eq s' stat n θ s'∈) = s∉ x

sig-∉-single : ∀ S S' stat → ¬ S ≡ S' → ¬ isSig∈ S (Θ SigMap.[ S' ↦ stat ] [] [])
sig-∉-single S S' stat neg x rewrite SigMap.keys-1map S' stat with x
... | Any.here px = (Signal.unwrap-neq neg) px
... | Any.there ()

shr-∉-single : ∀ s s' stat n → ¬ s ≡ s' → ¬ isShr∈ s (Θ [] ShrMap.[ s' ↦ (stat ,′ n) ] [])
shr-∉-single s s' stat n neg x rewrite ShrMap.keys-1map s' (stat ,′ n) with x
... | Any.here px = (SharedVar.unwrap-neq neg) px
... | Any.there ()

sig-∈-single : ∀ S stat →  isSig∈ S (Θ SigMap.[ S ↦ stat ] [] [])
sig-∈-single S stat rewrite SigMap.keys-1map S stat = Data.List.Any.here refl

sig-∈-single-right-← : ∀ S stat θ → isSig∈ S (θ ← (Θ SigMap.[ S ↦ stat ] [] []))
sig-∈-single-right-← S stat θ = sig-←-monoʳ S (Θ SigMap.[ S ↦ stat ] [] []) θ (sig-∈-single S stat)

shr-∈-single : ∀ s stat n →  isShr∈ s (Θ [] ShrMap.[ s ↦ (stat ,′ n) ] [])
shr-∈-single s stat n rewrite ShrMap.keys-1map s (stat ,′ n) = Data.List.Any.here refl

sig-single-∈-eq : ∀ S S' stat' →
  isSig∈ S (Θ SigMap.[ S' ↦ stat' ] [] []) →
  Signal.unwrap S ≡ Signal.unwrap S'
sig-single-∈-eq S S' stat' S∈Dom[S'] rewrite SigMap.keys-1map S' stat' = ∈:: S∈Dom[S']

sig-put-mby-overwrite : ∀ S S' θ statneq statput S∈ S'∈ S∈2
                        → ¬ statneq ≡ statput
                        → ¬ (sig-stats{S} θ S∈ ≡ statneq)
                        → ¬ (sig-stats{S} (set-sig{S'} θ S'∈ statput) S∈2 ≡ statneq)
sig-put-mby-overwrite S S' θ statneq statput S∈ S'∈ S∈2 neq≠put ¬ref ref
  with S Signal.≟ S'
... | yes refl = lookup-S-eq (set-sig{S} θ S'∈ statput) S S∈2 S∈2 (sig-putget{S}{θ}{statput} S'∈ S∈2) ref (neq≠put ∘ sym)
... | no ¬refl = ¬ref (trans (sym (sig-putputget/m{S}{S'}{θ} ¬refl S∈ S'∈ S∈2)) ref) 

sig-stats-1map' : ∀ S status →
  (S∈ : isSig∈ S (Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty)) →
  sig-stats {S} (Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty) S∈
    ≡ status
sig-stats-1map' S status S∈ = SigMap.putget-m {_} {SigMap.empty} {S} {status} S∈

sig-stats-1map-right-← : ∀ S status θ → 
   (S∈ : isSig∈ S (θ ← (Θ SigMap.[ S ↦ status ] [] []))) →
   (sig-stats{S} (θ ← (Θ SigMap.[ S ↦ status ] [] [])) S∈ ≡ status)
sig-stats-1map-right-← S stat θ S∈
  = trans (sig-stats-←-right-irr' S θ (Θ SigMap.[ S ↦ stat ] [] []) (sig-∈-single S stat) S∈) (sig-stats-1map' S stat (sig-∈-single S stat))

sig-put-1map-overwrite' : ∀ S status status' →
  (S∈ : isSig∈ S (Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty)) →
  set-sig {S} (Θ SigMap.[ S ↦ status ] ShrMap.empty VarMap.empty) S∈ status'
    ≡ Θ SigMap.[ S ↦ status' ] ShrMap.empty VarMap.empty
sig-put-1map-overwrite' S status status' S∈
  rewrite SigMap.putput-overwrite SigMap.empty S status status'
  = refl

sig-set-inner-clobber : ∀ θ θ' θ'' S stat → isSig∈ S θ''
                        → ((θ ← (Θ SigMap.[ S ↦ stat ] [] [])) ← θ') ← θ''
                          ≡
                          ((θ ← θ') ← θ'')
sig-set-inner-clobber θ θ' θ'' S stat S∈θ'' with Sig∈ S θ'
... | yes S∈θ' = (((θ ← (Θ SigMap.[ S ↦ stat ] [] [])) ← θ') ← θ'')
                 ≡⟨ cong (λ x → (x ← θ'')) (sym (←-assoc θ (Θ SigMap.[ S ↦ stat ] [] []) θ')) ⟩
                 ((θ ← ((Θ SigMap.[ S ↦ stat ] [] []) ← θ')) ← θ'')
                 ≡⟨ cong (λ x → (θ ← x) ← θ'' )
                         (←-single-overwrite-sig S stat (Θ (sig θ') (shr θ') (var θ')) S∈θ') ⟩
                 ((θ ← θ') ← θ'') ∎
... | no  S∉θ'  = (((θ ← (Θ SigMap.[ S ↦ stat ] [] [])) ← θ') ← θ'')
                  ≡⟨ cong (λ x → (x ← θ'')) (sym (←-assoc θ (Θ SigMap.[ S ↦ stat ] [] []) θ')) ⟩
                  ((θ ← ((Θ SigMap.[ S ↦ stat ] [] []) ← θ')) ← θ'')
                  ≡⟨ cong (λ x → (θ ← x) ← θ'' )
                          ( ←-comm (Θ SigMap.[ S ↦ stat ] [] []) θ' (ds , ((λ z → λ ()) , (λ z → λ ())))) ⟩
                  ((θ ← (θ' ← (Θ SigMap.[ S ↦ stat ] [] []))) ← θ'')
                  ≡⟨ cong (_← θ'') (←-assoc θ θ' (Θ SigMap.[ S ↦ stat ] [] [])) ⟩
                  (((θ ← θ') ← (Θ SigMap.[ S ↦ stat ] [] [])) ← θ'')
                  ≡⟨ sym (←-assoc (θ ← θ') (Θ SigMap.[ S ↦ stat ] [] []) θ'')  ⟩
                  ((θ ← θ') ← ((Θ SigMap.[ S ↦ stat ] [] []) ← θ''))
                  ≡⟨ cong ((θ ← θ') ←_) (←-single-overwrite-sig S stat (Θ (sig θ'') (shr θ'') (var θ''))
                                           S∈θ'') ⟩
                  ((θ ← θ') ← θ'')
                  ∎
             where
               ds : distinct' (proj₁ (Dom (Θ SigMap.[ S ↦ stat ] [] []))) (proj₁ (Dom θ'))
               ds z x y rewrite SigMap.keys-1map S stat with x
               ... | Any.here refl = ⊥-elim (S∉θ' y)
               ... | Any.there ()

sig-single-notin-distinct : ∀ S status θ →
  Signal.unwrap S ∉ proj₁ (Dom θ) →
  distinct (Dom (Θ SigMap.[ S ↦ status ] [] [])) (Dom θ)
sig-single-notin-distinct S status θ S∉Domθ =
  (λ S'' S''∈[S] S''∈Domθ →
    S∉Domθ
      (subst (_∈ proj₁ (Dom θ))
        (∈:: (subst (S'' ∈_) (SigMap.keys-1map S status) S''∈[S]))
        S''∈Domθ)) ,′
  (λ _ ()) ,′
  (λ _ ())


-- a special case of sig-single-notin-distinct
sig-single-noteq-distinct : ∀ S status S' status' →
  ¬ Signal.unwrap S ≡ Signal.unwrap S' →
  distinct (Dom (Θ SigMap.[ S ↦ status ] [] [])) (Dom (Θ SigMap.[ S' ↦ status' ] [] []))
sig-single-noteq-distinct S status S' status' S≢S' =
  (λ S'' S''∈[S] S''∈[S'] →
    S≢S'
      (trans
        (sym (∈:: (subst (S'' ∈_) (SigMap.keys-1map S status) S''∈[S])))
        (∈:: (subst (S'' ∈_) (SigMap.keys-1map S' status') S''∈[S'])))) ,′
  (λ _ ()) ,′
  (λ _ ())


sig-single-←-←-overwrite : ∀ θ S status status' →
  (θ ← Θ SigMap.[ S ↦ status ] [] []) ← Θ SigMap.[ S ↦ status' ] [] [] ≡
  θ ← Θ SigMap.[ S ↦ status' ] [] []
sig-single-←-←-overwrite θ S status status'
  rewrite sym (←-assoc θ (Θ SigMap.[ S ↦ status ] [] []) (Θ SigMap.[ S ↦ status' ] [] []))
  = cong (θ ←_)
      (←-single-overwrite-sig S status (Θ SigMap.[ S ↦ status' ] [] [])
        (sig-∈-single S status'))

sig-set-clobber-single-as-← : ∀ S status status' θ S∈ → (set-sig{S} (θ ← (Θ SigMap.[ S ↦ status' ] [] [])) S∈ status) ≡ (θ ← (Θ SigMap.[ S ↦ status ] [] []))
sig-set-clobber-single-as-← S status status' θ S∈
  =(begin
     (set-sig{S} (θ ← θs1) ((sig-∈-single-right-← S status' θ)) status)
     ≡⟨  sym (sig-switch-right S status θ θs1 ((sig-∈-single S status')) ((sig-∈-single-right-← S status' θ)))  ⟩
     (θ ← (set-sig{S} θs1 ((sig-∈-single S status')) status))
     ≡⟨  cong (_←_ θ) (sig-put-1map-overwrite' S status' status ((sig-∈-single S status')))  ⟩
     (θ ← θs2) ∎)
   where
     θs1 = (Θ SigMap.[ S ↦ status' ] [] [])
     θs2 = (Θ SigMap.[ S ↦ status ] [] [])

sig-re-set-is-eq : ∀ θ S status → (S∈ : isSig∈ S θ)
                   → sig-stats {S} θ S∈ ≡ status
                   → set-sig {S} θ S∈ status ≡ θ
sig-re-set-is-eq θ S status S∈ eq
  rewrite SigMap.re-update-is-eq (sig θ) S S∈ status eq
  = refl

←-self-identity : ∀ θ → θ ← θ ≡ θ
←-self-identity θ
  rewrite SigMap.union-self-idenity (sig θ)
        | VarMap.union-self-idenity (var θ)
        | ShrMap.union-self-idenity (shr θ)
   = refl
