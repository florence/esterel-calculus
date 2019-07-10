module utility.HeterogeneousEquality where

open import Relation.Binary.HeterogeneousEquality


cong₃ : ∀{a b c d}
       {A : Set a}
       {B : A → Set b}
       {C : ∀ x → B x → Set c}
       {D : ∀ x → (y : B x) → C x y → Set d}
       {x y u v q w}
       (f : (x : A) (y : B x) (z : C x y) → D x y z)
       → x ≅ y → u ≅ v → q ≅ w
       → f x u q ≅ f y v w
cong₃ f refl refl refl = refl
cong₄ : ∀{a b c d e}
         {A : Set a}
         {B : A → Set b}
         {C : ∀ x → B x → Set c}
         {D : ∀ x → (y : B x) → C x y → Set d}
         {E : ∀ x → (y : B x) → (z : C x y) → D x y z → Set e}
         {x y u v q w m n}
         (f : (x : A) (y : B x) (z : C x y) → (w : D x y z) → E x y z w)
         → x ≅ y → u ≅ v → q ≅ w → m ≅ n
         → f x u q m ≅ f y v w n
cong₄ f refl refl refl refl = refl
