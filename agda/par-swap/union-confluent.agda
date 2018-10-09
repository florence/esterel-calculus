module par-swap.union-confluent where

open import par-swap
open import par-swap.properties
open import par-swap.confluent
open import par-swap.dpg

open import Data.Nat using (_+_ ;  _≤′_ ; _<′_ ; suc ; zero ; ≤′-refl ; ℕ)
open import Data.Nat.Properties.Simple using ( +-comm ; +-assoc)
open import Data.Nat.Properties using (s≤′s ; z≤′n)
open import Data.MoreNatProp using (≤′-trans ; suc≤′⇒≤′)
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Data.Empty

open import Induction.Nat using (<-rec)
open import Induction.Lexicographic using ()
open import Induction using ()
open import Induction.WellFounded using ()
open import Level using ()
open import Relation.Binary using (Rel)

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Environment as Env
open import Esterel.Context
open import Esterel.Lang.Binding

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; subst ; cong ; trans ;
         module ≡-Reasoning ; cong₂ ; subst₂ ; inspect)
open import sn-calculus
open import context-properties -- get view, E-views

open import binding-preserve using (sn⟶-maintains-binding ; sn⟶*-maintains-binding)
open import noetherian using (noetherian ; ∥_∥s)
open import sn-calculus-props

∥R-preserves-∥∥s : ∀ {p q} -> p ∥R q -> ∥ q ∥s ≡ ∥ p ∥s
∥R-preserves-∥∥s (∥Rstep{C}{p}{q} d≐C⟦p∥q⟧c)
  rewrite sym (unplugc d≐C⟦p∥q⟧c) = ∥∥par-sym p q C where

  ∥∥par-sym : ∀ p q C ->  ∥ C ⟦ q ∥ p ⟧c ∥s ≡ ∥ C ⟦ p ∥ q ⟧c ∥s
  ∥∥par-sym p q [] rewrite +-comm ∥ p ∥s ∥ q ∥s = refl
  ∥∥par-sym p q (_ ∷ C) with ∥∥par-sym p q C
  ∥∥par-sym p q (ceval (epar₁ _) ∷ C)    | R rewrite R = refl
  ∥∥par-sym p q (ceval (epar₂ _) ∷ C)    | R rewrite R = refl
  ∥∥par-sym p q (ceval (eseq _) ∷ C)     | R rewrite R = refl
  ∥∥par-sym p q (ceval (eloopˢ _) ∷ C)   | R rewrite R = refl
  ∥∥par-sym p q (ceval (esuspend _) ∷ C) | R rewrite R = refl
  ∥∥par-sym p q (ceval etrap ∷ C)        | R rewrite R = refl
  ∥∥par-sym p q (csignl _ ∷ C)           | R rewrite R = refl
  ∥∥par-sym p q (cpresent₁ _ _ ∷ C)      | R rewrite R = refl
  ∥∥par-sym p q (cpresent₂ _ _ ∷ C)      | R rewrite R = refl
  ∥∥par-sym p q (cloop ∷ C)              | R rewrite R = refl
  ∥∥par-sym p q (cloopˢ₂ _ ∷ C)          | R rewrite R = refl
  ∥∥par-sym p q (cseq₂ _ ∷ C)            | R rewrite R = refl
  ∥∥par-sym p q (cshared _ _ ∷ C)        | R rewrite R = refl
  ∥∥par-sym p q (cvar _ _ ∷ C)           | R rewrite R = refl
  ∥∥par-sym p q (cif₁ _ _ ∷ C)           | R rewrite R = refl
  ∥∥par-sym p q (cif₂ _ _ ∷ C)           | R rewrite R = refl
  ∥∥par-sym p q (cenv _ ∷ C)             | R rewrite R = refl

∥R*-preserves-∥∥s : ∀ {p q} -> p ∥R* q -> ∥ q ∥s ≡ ∥ p ∥s
∥R*-preserves-∥∥s ∥R0 = refl
∥R*-preserves-∥∥s (∥Rn p∥Rq p∥R*q) with ∥R*-preserves-∥∥s p∥R*q
... | x rewrite ∥R-preserves-∥∥s p∥Rq = x


module LexicographicLE {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
                       (RelA : Rel A ℓ₁)
                       (RelB : Rel B ℓ₂) where

  open import Level
  open import Relation.Binary
  open import Induction.WellFounded
  open import Data.Product
  open import Function
  open import Induction
  open import Relation.Unary

  data _<_ : Rel (Σ A \ _ → B) (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : RelA x₁ x₂) → (x₁ , y₁) < (x₂ , y₂)
    right : ∀ {x₁ y₁ x₂ y₂} (y₁<y₂ : RelB y₁ y₂) → (x₁ ≡ x₂ ⊎ RelA x₁ x₂) →
            (x₁  , y₁) < (x₂  , y₂)

  mutual

    accessibleLE : ∀ {x y} →
                    Acc RelA x → Well-founded RelB →
                    Acc _<_ (x , y)
    accessibleLE accA wfB = acc (accessibleLE′ accA (wfB _) wfB)

    accessibleLE′ :
      ∀ {x y} →
      Acc RelA x → Acc RelB y →  Well-founded RelB →
      WfRec _<_ (Acc _<_) (x , y)
    accessibleLE′ (acc rsA) _    wfB ._ (left  x′<x) = accessibleLE (rsA _ x′<x) wfB
    accessibleLE′ accA (acc rsB) wfB .(_ , _) (right y′<y (inj₁ refl)) =
      acc (accessibleLE′ accA (rsB _ y′<y) wfB)
    accessibleLE′ (acc rsA) (acc rsB) wfB .(_ , _) (right y′<y (inj₂ x′<x)) =
      acc (accessibleLE′ (rsA _ x′<x) (rsB _ y′<y) wfB)

  well-founded : Well-founded RelA → Well-founded RelB →
                 Well-founded _<_
  well-founded wfA wfB p = accessibleLE (wfA (proj₁ p)) wfB

module _ where
  open LexicographicLE _<′_ _<′_ public
    renaming (_<_ to _<<′_;
              well-founded to <<′-well-founded;
              left to <<′-left;
              right to <<′-right)

module _ {ℓ} where
  open Induction.WellFounded.All
       (<<′-well-founded Induction.Nat.<-well-founded Induction.Nat.<-well-founded) ℓ public
    renaming (wfRec-builder to <<′-rec-builder;
              wfRec to <<′-rec)



{-
  proof from _On the Power of Simple Diagrams_
  by Roberto Di Cosmo, RTA 1996 (lemma 7)
-}
∥R*-sn⟶*-commute : CB-COMMUTE _∥R*_ _sn⟶*_
∥R*-sn⟶*-commute = thm where
  redlen : ∀ {p q} -> p ∥R* q -> ℕ
  redlen ∥R0 = zero
  redlen (∥Rn p∥Rq p∥R*q) = suc (redlen p∥R*q)

  sharedtype : (ℕ × ℕ) -> Set
  sharedtype (sizeb , distab) =
     ∀ {a b c BV FV} ->
      CorrectBinding a BV FV ->
      (a∥R*b : a ∥R* b) ->
      a sn⟶* c ->
      redlen a∥R*b ≡ distab ->
      ∥ b ∥s ≡ sizeb ->
      ∃ \ {d -> b sn⟶* d × c ∥R* d}

  {- this proof is not working the way that
     Di Cosmo intended; it uses properties
     about ∥R* reduction directly -}
  composing-the-diagram-in-the-hypothesis-down :
    ∀ {p1 p2 p3 q1 q3} ->
    p1 sn⟶ p2 ->
    p2 sn⟶* p3 ->
    p1 ∥R* q1 ->
    p3 ∥R* q3 ->
    (∥ q3 ∥s) <′ (∥ q1 ∥s)
  composing-the-diagram-in-the-hypothesis-down = thm where

    thm-no-∥R* : ∀ {p1 p2 p3} ->
     p1 sn⟶ p2 ->
     p2 sn⟶* p3 ->
     ∥ p3 ∥s <′ ∥ p1 ∥s
    thm-no-∥R* p1sn⟶p2 rrefl = noetherian p1sn⟶p2
    thm-no-∥R* {p1}{p2}{p3} p1sn⟶p2 (rstep{q = r} p2sn⟶r rsn⟶*p3)
      with thm-no-∥R* p2sn⟶r rsn⟶*p3
    ... | ∥p3∥s<′∥p2∥s =
        ≤′-trans {y = ∥ p2 ∥s}
                 ∥p3∥s<′∥p2∥s
                 (suc≤′⇒≤′ ∥ p2 ∥s ∥ p1 ∥s (noetherian p1sn⟶p2))

    thm : ∀ {p1 p2 p3 q1 q3} ->
     p1 sn⟶ p2 ->
     p2 sn⟶* p3 ->
     p1 ∥R* q1 ->
     p3 ∥R* q3 ->
     (∥ q3 ∥s) <′ (∥ q1 ∥s)
    thm p1sn⟶p2 p2sn⟶*p3 p1∥R*q1 p3∥R*q3
      rewrite ∥R*-preserves-∥∥s p1∥R*q1
            | ∥R*-preserves-∥∥s p3∥R*q3 =
            thm-no-∥R* p1sn⟶p2 p2sn⟶*p3

  step : ∀ nm ->
          (∀ (nm′ : ℕ × ℕ) -> nm′ <<′ nm -> sharedtype nm′) ->
          sharedtype nm
  step (sizeb , distab) rec  CBa ∥R0 asn⟶*c redlena∥R*b≡distab ∥b∥s≡sizeb = _ , asn⟶*c , ∥R0
  step (sizeb , distab) rec CBa a∥R*b rrefl redlena∥R*b≡distab ∥b∥s≡sizeb = _ , rrefl , a∥R*b
  step (sizeb , distab) rec {a} {b} {c} CBa
       (∥Rn{q = a″} a∥Ra″ a″∥R*b)
       (rstep{q = a′} asn⟶a′ a′sn⟶*c)
       redlena∥R*b≡distab
       ∥b∥s≡sizeb rewrite sym redlena∥R*b≡distab
    with sn⟶-maintains-binding CBa asn⟶a′
  ... | (_ , CBa′ , _)
    with DPG a∥Ra″ asn⟶a′
  ... | (a‴ , gap) , a″sn⟶gap ,  gapsn⟶*a‴ , a′∥R*a‴
    with rec (sizeb , redlen a″∥R*b) (<<′-right (s≤′s ≤′-refl) (inj₁ refl))
             (∥R-maintains-binding CBa a∥Ra″)
             a″∥R*b  (rstep a″sn⟶gap gapsn⟶*a‴) refl ∥b∥s≡sizeb
  ... | (b′ , bsn⟶*b′ , a‴∥R*b′) rewrite sym ∥b∥s≡sizeb
    with composing-the-diagram-in-the-hypothesis-down a″sn⟶gap gapsn⟶*a‴ a″∥R*b a‴∥R*b′
  ... | ∥b′∥s<′∥b∥s
    with rec (∥ b′ ∥s , redlen (∥R*-concat a′∥R*a‴ a‴∥R*b′))
             (<<′-left ∥b′∥s<′∥b∥s)
             CBa′ (∥R*-concat a′∥R*a‴ a‴∥R*b′) a′sn⟶*c refl refl
  ... | ( d , b′sn⟶*d , c∥R*d) =  d , sn⟶*+ bsn⟶*b′ b′sn⟶*d , c∥R*d

  lemma7-commutation : ∀ (nm : ℕ × ℕ) -> sharedtype nm
  lemma7-commutation = <<′-rec _ step

  thm : CB-COMMUTE _∥R*_ _sn⟶*_
  thm {p}{q}{r} CBp p∥R*q psn⟶*r =
   lemma7-commutation (∥ q ∥s , redlen p∥R*q) CBp p∥R*q psn⟶*r refl refl

∥R*∪sn⟶*-confluent : CB-CONFLUENT _∥R*∪sn⟶*_
∥R*∪sn⟶*-confluent =
  \ { CBp p∥R*∪sn⟶*q p∥R*∪sn⟶*r ->
      hindley-rosen
       (redlen p∥R*∪sn⟶*q , redlen p∥R*∪sn⟶*r)
       CBp p∥R*∪sn⟶*q p∥R*∪sn⟶*r refl refl} where

  redlen : ∀ {p q} -> p ∥R*∪sn⟶* q -> ℕ
  redlen (∪∥R* _ r) = suc (redlen r)
  redlen (∪sn⟶* _ r) = suc (redlen r)
  redlen ∪refl = zero

  sharedtype : ℕ × ℕ -> Set
  sharedtype (n , m) = ∀ {p q r BV FV} ->
    CorrectBinding p BV FV ->
    (p∥R*∪sn⟶*q : p ∥R*∪sn⟶* q) ->
    (p∥R*∪sn⟶*r : p ∥R*∪sn⟶* r) ->
    n ≡ redlen p∥R*∪sn⟶*q ->
    m ≡ redlen p∥R*∪sn⟶*r ->
    ∃ λ {z → (q ∥R*∪sn⟶* z × r ∥R*∪sn⟶* z)}

  length-lemma : ∀ {a b}  (l : a ∥R*∪sn⟶* b) ->
      suc zero ≡ suc (redlen l) ⊎
      suc zero <′ suc (redlen l)
  length-lemma (∪∥R* p∥R*q l) = inj₂ (s≤′s (s≤′s z≤′n))
  length-lemma (∪sn⟶* psn⟶*q l) = inj₂ (s≤′s (s≤′s z≤′n))
  length-lemma ∪refl = inj₁ refl

  step : ∀ nm ->
          (∀ (nm′ : ℕ × ℕ) -> nm′ <<′ nm -> sharedtype nm′) ->
          sharedtype nm
  step (n , m) rec CBp (∪∥R* p∥R*q a) ∪refl n≡ m≡ = _ , ∪refl , ∪∥R* p∥R*q a
  step (n , m) rec CBp (∪sn⟶* psn⟶*q a) ∪refl n≡ m≡ =   _ , ∪refl , ∪sn⟶* psn⟶*q a
  step (n , m) rec CBp ∪refl (∪∥R* p∥R*q b) n≡ m≡ = _ , ∪∥R* p∥R*q b , ∪refl
  step (n , m) rec CBp ∪refl (∪sn⟶* psn⟶*q b) n≡ m≡ = _ , ∪sn⟶* psn⟶*q b , ∪refl
  step (n , m) rec CBp ∪refl ∪refl n≡ m≡ = _ , ∪refl , ∪refl

  step(n , m) rec {p}{q}{r} CBp
      (∪∥R* {_}{q₁} p∥R*q₁ q₁∥R*∪sn⟶*q)
      (∪∥R* {_}{r₁} p∥R*r₁ r₁∥R*∪sn⟶*r)
     n≡ m≡  rewrite n≡ | m≡
    with BVFVcorrect _ _ _ CBp
  ... | refl , refl
    with ∥R*-maintains-binding CBp p∥R*q₁
  ... | CBq₁
    with  BVFVcorrect _ _ _ CBq₁
  ... | refl , refl
    with ∥R*-maintains-binding CBp p∥R*r₁
  ... | CBr₁
    with  BVFVcorrect _ _ _ CBr₁
  ... | refl , refl
    with ∥R*-confluent CBp p∥R*q₁ p∥R*r₁
  ... | q₁r₁ , q₁∥R*q₁r₁ , r₁∥R*q₁r₁
    with rec (suc zero , redlen r₁∥R*∪sn⟶*r)
             (<<′-right ≤′-refl (length-lemma q₁∥R*∪sn⟶*q))
             CBr₁ (∪∥R* r₁∥R*q₁r₁ ∪refl) r₁∥R*∪sn⟶*r
             refl refl
  ... | q₁r₁r , q₁r₁∥R*∪sn⟶*q₁r₁r , r∥R*∪sn⟶*q₁r₁r
    with rec (redlen q₁∥R*∪sn⟶*q , suc (redlen q₁r₁∥R*∪sn⟶*q₁r₁r))
             (<<′-left ≤′-refl)
             CBq₁ q₁∥R*∪sn⟶*q (∪∥R* q₁∥R*q₁r₁ q₁r₁∥R*∪sn⟶*q₁r₁r)
             refl refl
  ... | qq₁r₁r , q∥R*∪sn⟶*qq₁r₁r , q₁r₁r∥R*∪sn⟶*qq₁r₁r
    = qq₁r₁r , q∥R*∪sn⟶*qq₁r₁r , ∥R*∪sn⟶*-concat r∥R*∪sn⟶*q₁r₁r q₁r₁r∥R*∪sn⟶*qq₁r₁r

  step (n , m) rec {p}{q}{r} CBp
    (∪∥R*{_}{q₁} p∥R*q₁ q₁∥R*∪sn⟶*q)
    (∪sn⟶*{_}{r₁} psn⟶*r₁  r₁∥R*∪sn⟶*r)
    n≡ m≡ rewrite n≡ | m≡
    with BVFVcorrect _ _ _ CBp
  ... | refl , refl
    with ∥R*-maintains-binding CBp p∥R*q₁
  ... | CBq₁
    with  BVFVcorrect _ _ _ CBq₁
  ... | refl , refl
    with sn⟶*-maintains-binding CBp psn⟶*r₁
  ... | (BVr₁ , FVr₁) , CBr₁
    with ∥R*-sn⟶*-commute CBp p∥R*q₁ psn⟶*r₁
  ... | q₁r₁ , q₁sn⟶*q₁r₁ , r₁∥R*q₁r₁
    with rec (suc zero , redlen r₁∥R*∪sn⟶*r)
             (<<′-right ≤′-refl (length-lemma q₁∥R*∪sn⟶*q))
             CBr₁ (∪∥R* r₁∥R*q₁r₁ ∪refl) r₁∥R*∪sn⟶*r
             refl refl
  ... | q₁r₁r , q₁r₁∥R*∪sn⟶*q₁r₁r , r∥R*∪sn⟶*q₁r₁r
     with rec (redlen q₁∥R*∪sn⟶*q , suc (redlen q₁r₁∥R*∪sn⟶*q₁r₁r))
             (<<′-left ≤′-refl)
             CBq₁ q₁∥R*∪sn⟶*q (∪sn⟶*  q₁sn⟶*q₁r₁  q₁r₁∥R*∪sn⟶*q₁r₁r)
             refl refl
  ... | qq₁r₁r , q∥R*∪sn⟶*qq₁r₁r , q₁r₁r∥R*∪sn⟶*qq₁r₁r
    =  qq₁r₁r , q∥R*∪sn⟶*qq₁r₁r , ∥R*∪sn⟶*-concat r∥R*∪sn⟶*q₁r₁r q₁r₁r∥R*∪sn⟶*qq₁r₁r

  step (n , m) rec {p}{q}{r} CBp
    (∪sn⟶*{_}{q₁} psn⟶*q₁ q₁∥R*∪sn⟶*q)
    (∪∥R*{_}{r₁} p∥R*r₁  r₁∥R*∪sn⟶*r)
    n≡ m≡ rewrite n≡ | m≡
    with BVFVcorrect _ _ _ CBp
  ... | refl , refl
    with sn⟶*-maintains-binding CBp psn⟶*q₁
  ... | (BVq₁ , FVq₁) , CBq₁
    with ∥R*-maintains-binding CBp p∥R*r₁
  ... | CBr₁
    with  BVFVcorrect _ _ _ CBr₁
  ... | refl , refl
    with ∥R*-sn⟶*-commute CBp p∥R*r₁ psn⟶*q₁
  ... | r₁q₁ , r₁sn⟶*r₁q₁ , q₁∥R*r₁q₁
    with rec (suc zero , redlen r₁∥R*∪sn⟶*r)
             (<<′-right ≤′-refl (length-lemma q₁∥R*∪sn⟶*q))
             CBr₁ (∪sn⟶* r₁sn⟶*r₁q₁ ∪refl) r₁∥R*∪sn⟶*r
             refl refl
  ... | r₁q₁r , r₁q₁∥R*∪sn⟶*r₁q₁r , r∥R*∪sn⟶*r₁q₁r
     with rec (redlen q₁∥R*∪sn⟶*q , suc (redlen r₁q₁∥R*∪sn⟶*r₁q₁r))
             (<<′-left ≤′-refl)
             CBq₁ q₁∥R*∪sn⟶*q (∪∥R*  q₁∥R*r₁q₁  r₁q₁∥R*∪sn⟶*r₁q₁r)
             refl refl
  ... | qq₁r₁r , q∥R*∪sn⟶*qq₁r₁r , q₁r₁r∥R*∪sn⟶*qq₁r₁r
    =  qq₁r₁r , q∥R*∪sn⟶*qq₁r₁r , ∥R*∪sn⟶*-concat r∥R*∪sn⟶*r₁q₁r q₁r₁r∥R*∪sn⟶*qq₁r₁r

  step (n , m) rec {p}{q}{r} CBp
    (∪sn⟶*{_}{q₁} psn⟶*q₁  q₁∥R*∪sn⟶*q)
    (∪sn⟶*{_}{r₁} psn⟶*r₁ r₁∥R*∪sn⟶*r)
    n≡ m≡ rewrite n≡ | m≡
    with BVFVcorrect _ _ _ CBp
  ... | refl , refl
    with sn⟶*-maintains-binding CBp psn⟶*q₁
  ... | (BVq₁ , FVq₁) , CBq₁
    with sn⟶*-maintains-binding CBp psn⟶*r₁
  ... | (BVr₁ , FVr₁) , CBr₁
    with sn⟶*-confluent CBp psn⟶*q₁ psn⟶*r₁
  ... | q₁r₁ , q₁sn⟶*q₁r₁ , r₁sn⟶*q₁r₁
    with rec (suc zero , redlen r₁∥R*∪sn⟶*r)
             (<<′-right ≤′-refl (length-lemma q₁∥R*∪sn⟶*q))
             CBr₁ (∪sn⟶* r₁sn⟶*q₁r₁ ∪refl) r₁∥R*∪sn⟶*r
             refl refl
  ... | q₁r₁r , q₁r₁∥R*∪sn⟶*q₁r₁r , r∥R*∪sn⟶*q₁r₁r
    with rec (redlen q₁∥R*∪sn⟶*q , suc (redlen q₁r₁∥R*∪sn⟶*q₁r₁r))
             (<<′-left ≤′-refl)
             CBq₁ q₁∥R*∪sn⟶*q (∪sn⟶* q₁sn⟶*q₁r₁ q₁r₁∥R*∪sn⟶*q₁r₁r)
             refl refl
  ... | qq₁r₁r , q∥R*∪sn⟶*qq₁r₁r , q₁r₁r∥R*∪sn⟶*qq₁r₁r
    = qq₁r₁r , q∥R*∪sn⟶*qq₁r₁r , ∥R*∪sn⟶*-concat r∥R*∪sn⟶*q₁r₁r q₁r₁r∥R*∪sn⟶*qq₁r₁r

  hindley-rosen : ∀ (nm : ℕ × ℕ) -> sharedtype nm
  hindley-rosen = <<′-rec _ step
