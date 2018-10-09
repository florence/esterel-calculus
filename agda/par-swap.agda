module par-swap where

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Context
open import sn-calculus

data _∥R_ : Term -> Term -> Set where
  ∥Rstep : ∀ {C p q d} ->
          (d≐C⟦p∥q⟧c : d ≐ C ⟦ (p ∥ q) ⟧c) ->
          d ∥R (C ⟦ (q ∥ p) ⟧c)

data _∥R*_ : Term -> Term -> Set where
  ∥R0 : ∀ {p} -> p ∥R* p
  ∥Rn : ∀ {p q r} ->
        (p∥Rq : p ∥R q) ->
        (q∥R*r : q ∥R* r) ->
        p ∥R* r

∥R*-concat : ∀ {p q r} -> p ∥R* q -> q ∥R* r -> p ∥R* r
∥R*-concat ∥R0 q∥R*r = q∥R*r
∥R*-concat (∥Rn p∥Rq p∥R*q) q∥R*r = ∥Rn p∥Rq (∥R*-concat p∥R*q q∥R*r)

data _∥R*∪sn⟶*_ : Term -> Term -> Set where
  ∪∥R* : ∀ {p q r} ->
         (p∥R*q : p ∥R* q) ->
         (q∥R∪sn⟶*r : q ∥R*∪sn⟶* r) ->
         p ∥R*∪sn⟶* r
  ∪sn⟶* : ∀ {p q r} ->
         (psn⟶*q : p sn⟶* q) ->
         (q∥R∪sn⟶*r : q ∥R*∪sn⟶* r) ->
         p ∥R*∪sn⟶* r
  ∪refl : ∀ {p} -> p ∥R*∪sn⟶* p

∥R*∪sn⟶*-concat : ∀ {p q r} -> p ∥R*∪sn⟶* q -> q ∥R*∪sn⟶* r -> p ∥R*∪sn⟶* r
∥R*∪sn⟶*-concat (∪∥R* p∥R*q a) b = ∪∥R* p∥R*q (∥R*∪sn⟶*-concat a b)
∥R*∪sn⟶*-concat (∪sn⟶* psn⟶*q a) b = ∪sn⟶* psn⟶*q (∥R*∪sn⟶*-concat a b)
∥R*∪sn⟶*-concat ∪refl b = b

data _∥R∪sn≡ₑ_ : Term → Term → Set where
  ∪stpsn : ∀{p q} → (psn⟶q : p sn⟶ q) → p ∥R∪sn≡ₑ q
  ∪stp∥ : ∀{p q} → (p∥Rq : p ∥R q) → p ∥R∪sn≡ₑ q
  ∪sym : ∀{p q BV FV} → (psn∪∥R≡ₑq : p ∥R∪sn≡ₑ q) → (CBp : CorrectBinding p BV FV) → q ∥R∪sn≡ₑ p
  ∪ref : ∀{p} → p ∥R∪sn≡ₑ p
  ∪trn : ∀{p r q} → (p∥R∪sn≡ₑr : p ∥R∪sn≡ₑ r) → (r∥R∪sn≡ₑq : r ∥R∪sn≡ₑ q) → p ∥R∪sn≡ₑ q
