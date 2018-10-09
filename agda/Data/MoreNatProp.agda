module Data.MoreNatProp where

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong)
open import Data.Nat as Nat
  using (ℕ ; suc ; zero ; _≤′_ ; _≤_ ; _+_ ; s≤s ; z≤n ; ≤′-refl ;
         ≤′-step ; _⊔_)
open import Data.Nat.Properties as NatP
  using (≤⇒≤′ ; ≤′⇒≤ ;  m≤m+n ; s≤′s ; ≤-steps ; ≤⇒pred≤)
open import Data.Nat.Properties.Simple as NatPS
  using (+-comm ; +-suc)

≤-trans : ∀ {x y z} -> x ≤ y -> y ≤ z -> x ≤ z
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

≤′-trans : ∀ {x y z} -> x ≤′ y -> y ≤′ z -> x ≤′ z
≤′-trans xy yz = ≤⇒≤′ (≤-trans (≤′⇒≤ xy) (≤′⇒≤ yz))

≤′+r : ∀ {x y z} -> x ≤′ y -> z + x  ≤′ z + y 
≤′+r {x} {y} {zero} x≤′y = x≤′y
≤′+r {x} {y} {suc z} x≤′y = s≤′s (≤′+r {x} {y} {z} x≤′y)

≤′+l : ∀ {x y z} -> x ≤′ y -> x + z ≤′ y + z
≤′+l {x} {y} {z} x≤′y rewrite +-comm x z | +-comm y z = ≤′+r{x}{y}{z} x≤′y

≡is≤′ : ∀ {p q} -> p ≡ q -> p ≤′ q
≡is≤′ p≡q rewrite p≡q = ≤′-refl

≤+b : ∀ x y z w -> x ≤ z -> y ≤ w -> x + y ≤ z + w
≤+b .0 y z w Nat.z≤n y≤w = ≤-steps z y≤w
≤+b .(suc x) y .(suc z) w (Nat.s≤s{x}{z} x≤z) y≤w = s≤s (≤+b x y z w x≤z y≤w)

≤′+b : ∀ x y z w -> x ≤′ z -> y ≤′ w -> x + y ≤′ z + w
≤′+b x y z w x≤′z y≤′w = ≤⇒≤′ (≤+b x y z w (≤′⇒≤ x≤′z) (≤′⇒≤ y≤′w))

suc≤′⇒≤′ : ∀ x y -> suc x ≤′ y -> x ≤′ y
suc≤′⇒≤′ x y sucx≤′y = ≤⇒≤′ (≤⇒pred≤ (suc x) y (≤′⇒≤ sucx≤′y))

⊔-sym : ∀ n m -> n ⊔ m ≡ m ⊔ n
⊔-sym zero zero = refl
⊔-sym zero (suc m) = refl
⊔-sym (suc n) zero = refl
⊔-sym (suc n) (suc m) = cong suc (⊔-sym n m)
