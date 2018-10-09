module Esterel.CompletionCode where

open import Data.Nat
  using (ℕ ; zero ; suc) renaming (_≟_ to _≟ℕ_ ; _⊔_ to _⊔ℕ_ ; _≤_ to _≤N_ ; _≤?_ to _≤?N_)
open import Data.Nat.Properties
  using (⊔-⊓-0-isCommutativeSemiringWithoutOne)
open import Function
  using (_∘_)
open import Relation.Nullary
  using (Dec ; yes ; no)
open import Relation.Binary
  using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong)
import Level
import Relation.Binary
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.List.Any.Properties using (++ˡ ; ++ʳ)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Empty using (⊥-elim)
import Data.Bool
open import Algebra.Structures
  using (IsCommutativeSemiringWithoutOne ; IsCommutativeMonoid)

open import utility

data CompletionCode : Set where
  nothin : CompletionCode
  pause  : CompletionCode
  exit   : ℕ → CompletionCode

↓* : CompletionCode → CompletionCode
↓* nothin         = nothin
↓* pause          = pause
↓* (exit zero)    = nothin
↓* (exit (suc n)) = exit n

exit-injective : ∀{n m} → exit n ≡ exit m → n ≡ m
exit-injective refl = refl

_≟_ : Decidable {A = CompletionCode} _≡_
nothin ≟ nothin = yes refl
nothin ≟ pause  = no λ()
nothin ≟ exit _ = no λ()
pause  ≟ nothin = no λ()
pause  ≟ pause  = yes refl
pause  ≟ exit _ = no λ()
exit _ ≟ nothin = no λ()
exit _ ≟ pause  = no λ()
exit n ≟ exit m with n ≟ℕ m
... | yes n≡m = yes (cong exit n≡m)
... | no ¬n≡m = no (¬n≡m ∘ exit-injective)

open ListSet _≟_

_⊔_ : CompletionCode → CompletionCode → CompletionCode
nothin ⊔ r      = r
pause  ⊔ nothin = pause
pause  ⊔ r      = r
exit n ⊔ nothin = exit n
exit n ⊔ pause  = exit n
exit n ⊔ exit m = exit (n ⊔ℕ m)

⊔-comm : ∀ c₁ c₂ → c₁ ⊔ c₂ ≡ c₂ ⊔ c₁
⊔-comm nothin   nothin   = refl
⊔-comm nothin   pause    = refl
⊔-comm nothin   (exit m) = refl
⊔-comm pause    nothin   = refl
⊔-comm pause    pause    = refl
⊔-comm pause    (exit m) = refl
⊔-comm (exit n) nothin   = refl
⊔-comm (exit n) pause    = refl
⊔-comm (exit n) (exit m)
  rewrite IsCommutativeMonoid.comm
            (IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid
              ⊔-⊓-0-isCommutativeSemiringWithoutOne) n m
  = refl

data _≤_ : Relation.Binary.Rel CompletionCode Level.zero where
  nothin≤c     : ∀ {c}                 -> nothin ≤ c
  pause≤pause  :                          pause  ≤ pause
  pause≤exit   : ∀ {n}                 -> pause  ≤ exit n
  exit≤exit    : ∀ {n} {m} -> (n ≤N m) -> exit n ≤ exit m

_≤?_ : Decidable _≤_
nothin ≤? c2 = yes nothin≤c
pause ≤? nothin = no (λ ())
pause ≤? pause = yes pause≤pause
pause ≤? exit x = yes pause≤exit
exit n ≤? nothin = no (λ ())
exit n ≤? pause = no (λ ())
exit n ≤? exit m with n ≤?N m
exit n ≤? exit m | yes n≤m = yes (exit≤exit n≤m)
exit n ≤? exit m | no ¬n≤m = no ¬≤ where
  ¬≤ : Relation.Nullary.¬ (exit n ≤ exit m)
  ¬≤ (exit≤exit n) = ¬n≤m n

codessub : (List CompletionCode) → (List CompletionCode) → Set
codessub codes' codes = (∀ a → a ∈ codes' → a ∈ codes)
codesub++ll : ∀{a b c} →  codessub a b → codessub a (b ++ c)
codesub++ll sub a a∈ = ++ˡ (sub a a∈)

codesub++both : ∀{a b c d} →  codessub a c → codessub b d → codessub (a ++ b) (c ++ d)
codesub++both{a}{b}{c}{d} a⊂c b⊂d z z∈ with ++⁻ a z∈
... | inj₁ z∈1 = ++ˡ (a⊂c z z∈1) 
... | inj₂ z∈2 = ++ʳ c (b⊂d z z∈2)  

codesub- : ∀{a b} z → codessub a b → codessub (set-remove a z) (set-remove b z)
codesub-{a}{b} z a⊂b x x∈ with z ≟ x
... | yes refl = ⊥-elim (set-remove-removed{x}{a} x∈)
... | no ¬refl = set-remove-not-removed ¬refl (a⊂b x (set-remove-mono-∈ z x∈)) 
