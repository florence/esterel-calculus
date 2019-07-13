module Esterel.Variable.Signal.Ordering where

open import Esterel.Variable.Signal

open import Level
open import Relation.Binary
  using (Rel)

infix 6 _⊑_

data _⊑_ : Rel Status 0ℓ where
  refl : {S : Status} → S ⊑ S
  uknw : {S : Status} → unknown ⊑ S

⊑-trans : ∀{S1 S2 S3} → S1 ⊑ S2 → S2 ⊑ S3 → S1 ⊑ S3
⊑-trans refl b = b
⊑-trans uknw b = uknw

