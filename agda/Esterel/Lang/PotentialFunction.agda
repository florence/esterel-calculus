module Esterel.Lang.PotentialFunction where

open import utility
  hiding (module ListSet)

open import Esterel.Lang
open import Esterel.Environment as Env
  using (Env ; _←_ ; Θ ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ) renaming (_≟ₛₜ_ to _≟ₛₜₛ_)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ) renaming (_≟ₛₜ_ to _≟ₛₜₛₕ_)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)

open import Function
  using (_∘_)
open import Relation.Nullary
  using (yes ; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary
  using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl)
open import Data.Bool
  using (Bool ; not ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.List
  using (List ; [] ; _∷_ ; [_] ; _++_ ; map ; concatMap ; filter)
open import Data.List.Any
  using (Any ; any)
open import Data.Product
  using (_×_ ; _,_ ; _,′_ ; proj₁ ; proj₂)

import Data.Nat as Nat
open Nat using (ℕ ; zero ; suc)

module SigSet = utility.ListSet Nat._≟_
module ShrSet = utility.ListSet Nat._≟_
module CodeSet = utility.ListSet Code._≟_

-- hide this when importing PotentialFunction to avoid ambiguity from sn-calculus.agda
[S]-env : (S : Signal) → Env
[S]-env S = Θ SigMap.[ S ↦ Signal.unknown ] ShrMap.empty VarMap.empty

-- The speculative environment used in Canₛ rule and for existing signals in Canθ
[S]-env-absent : (S : Signal) → Env
[S]-env-absent S = Θ SigMap.[ S ↦ Signal.absent ] ShrMap.empty VarMap.empty

-- Helper environment for existing signals in Canθ
[S]-env-present : (S : Signal) → Env
[S]-env-present S = Θ SigMap.[ S ↦ Signal.present ] ShrMap.empty VarMap.empty

Can   : Term → Env → SigSet.ST × CodeSet.ST × ShrSet.ST
Canₛ  : Term → Env → SigSet.ST
Canₖ  : Term → Env → CodeSet.ST
Canₛₕ : Term → Env → ShrSet.ST

Canₛ p θ with Can p θ
... | Ss , _ , _ = Ss
Canₖ p θ with Can p θ
... | _ , ks , _ = ks
Canₛₕ p θ with Can p θ
... | _ , _ , ss = ss


Canθ   : SigMap.Map Signal.Status → ℕ → Term → Env → SigSet.ST × CodeSet.ST × ShrSet.ST
Canθₛ  : SigMap.Map Signal.Status → ℕ → Term → Env → SigSet.ST
Canθₖ  : SigMap.Map Signal.Status → ℕ → Term → Env → CodeSet.ST
Canθₛₕ : SigMap.Map Signal.Status → ℕ → Term → Env → ShrSet.ST

Canθₛ sigs S p θ = proj₁ (Canθ sigs S p θ)
Canθₖ sigs S p θ = proj₁ (proj₂ (Canθ sigs S p θ))
Canθₛₕ sigs S p θ = proj₂ (proj₂ (Canθ sigs S p θ))

Canθ [] S p θ = Can p θ
Canθ (nothing             ∷ sig') S p θ = Canθ sig' (suc S) p θ
Canθ (just Signal.present ∷ sig') S p θ = Canθ sig' (suc S) p (θ ← [S]-env-present (S ₛ))
Canθ (just Signal.absent  ∷ sig') S p θ = Canθ sig' (suc S) p (θ ← [S]-env-absent (S ₛ))
Canθ (just Signal.unknown ∷ sig') S p θ with
  any (Nat._≟_ S) (Canθₛ sig' (suc S) p (θ ← [S]-env (S ₛ)))
... | yes S∈can-p-θ←[S] = Canθ sig' (suc S) p (θ ← [S]-env (S ₛ))
... | no  S∉can-p-θ←[S] = Canθ sig' (suc S) p (θ ← [S]-env-absent (S ₛ))


Can nothin θ =
  [] ,′ [ Code.nothin ] ,′ []
Can pause θ =
  [] ,′ [ Code.pause ] ,′ []
Can (signl S p) θ =
  SigSet.set-remove (Canθₛ (Env.sig ([S]-env S)) 0 p θ) (Signal.unwrap S) ,′
                     Canθₖ (Env.sig ([S]-env S)) 0 p θ ,′
                     Canθₛₕ (Env.sig ([S]-env S)) 0 p θ
Can (present S ∣⇒ p ∣⇒ q) θ with (Env.Sig∈ S θ)
... | yes S∈ =
  if ⌊ Signal.present Signal.≟ₛₜ (Env.sig-stats{S} θ S∈) ⌋
  then Can p θ
  else
    if ⌊ Signal.absent Signal.≟ₛₜ Env.sig-stats{S} θ S∈ ⌋
    then Can q θ
    else Canₛ p θ ++ Canₛ q θ ,′ Canₖ p θ ++ Canₖ q θ ,′ Canₛₕ p θ ++ Canₛₕ q θ
... | no S∉ =
  Canₛ p θ ++ Canₛ q θ ,′ Canₖ p θ ++ Canₖ q θ ,′ Canₛₕ p θ ++ Canₛₕ q θ
Can (emit S) θ = [ (Signal.unwrap S) ] ,′ [ Code.nothin ] ,′ []
Can (p ∥ q) θ =
  Canₛ p θ ++ Canₛ q θ ,′
  concatMap (λ k → map (Code._⊔_ k) (Canₖ q θ)) (Canₖ p θ) ,′
  Canₛₕ p θ ++ Canₛₕ q θ
Can (loop p) θ = Can p θ
Can (loopˢ p q) θ = Can p θ
Can (p >> q) θ with any (Code._≟_ Code.nothin) (Canₖ p θ)
... | no  nothin∉ =
  Can p θ
... | yes nothin∈ =
  Canₛ p θ ++ Canₛ q θ ,′
  (CodeSet.set-remove (Canₖ p θ) Code.nothin) ++ Canₖ q θ ,′
  Canₛₕ p θ ++ Canₛₕ q θ
Can (suspend p S) θ = Can p θ
Can (trap p) θ =
  Canₛ p θ ,′ map Code.↓* (Canₖ p θ) ,′ Canₛₕ p θ
Can (exit n) θ =
  [] ,′ [ Code.exit n ] ,′ []
Can (shared s ≔ e in: p) θ =
  Canₛ p θ ,′
  Canₖ p θ ,′
  ShrSet.set-remove (Canₛₕ p θ) (SharedVar.unwrap s)
Can (s ⇐ e) θ =
  [] ,′ [ Code.nothin ] ,′ [ (SharedVar.unwrap s) ]
Can (var x ≔ e in: p) θ =
  Can p θ
Can (x ≔ e) θ =
  [] ,′ [ Code.nothin ] ,′ []
Can (if x ∣⇒ p ∣⇒ q) θ =
  Canₛ p θ ++ Canₛ q θ ,′ Canₖ p θ ++ Canₖ q θ ,′ Canₛₕ p θ ++ Canₛₕ q θ
Can (ρ (Θ sig' shr' var') · p) θ =
  SigSet.set-subtract (Canθₛ sig' 0 p θ)  (SigMap.keys sig') ,′
                       Canθₖ sig' 0 p θ ,′
  ShrSet.set-subtract (Canθₛₕ sig' 0 p θ) (ShrMap.keys shr')
