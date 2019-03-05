module std-reduction.Properties where

open import std-reduction
open import sn-calculus

open import Relation.Binary.PropositionalEquality using (_≡_)
open _≡_

std-redution-deterministic : ∀{p q r} →
                             p ⇁ q →
                             p ⇁ r →
                             q ≡ r
std-redution-deterministic = ?

std=>calc : ∀{p q} → p ⇁ q → p sn⟶₁ q
std=>calc = ?
