module Esterel.Lang.Binding where

open import utility
open import Data.List
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.Bool
  using (Bool ; true ; false ; if_then_else_)
open import Esterel.Lang
open import Esterel.Environment as Env
  using (Env ; VarList ; Dom ; Θ ; _←_)
open import Esterel.Context
  using (Context1 ; EvaluationContext1 ; _≐_⟦_⟧e ; _⟦_⟧e ; _≐_⟦_⟧c ; _⟦_⟧c)
open import Esterel.Context.Properties
  using (plug)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ) renaming (_≟ₛₜ_ to _≟ₛₜₛ_ ; unwrap to Sunwrap)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ) renaming (_≟ₛₜ_ to _≟ₛₜₛₕ_ ; unwrap to sunwrap)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ) renaming (unwrap to vunwrap)
open import Data.Product
  using (_×_ ; _,_ ; _,′_ ; proj₁ ; proj₂ ; ∃)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; _≟_ ; zero ; suc)
open import Relation.Nullary
  using (Dec ; yes ; no ; ¬_)

open import Function
  using (_∘_ ; id ; _∋_)
open import Relation.Binary
  using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; setoid)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Data.Bool
  using (not)
open import Data.List.Any as ListAny
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties using (++ˡ ; ++ʳ ; ∷↔)

open ListSet Data.Nat._≟_
open _≐_⟦_⟧e
open _≐_⟦_⟧c
open Context1
open EvaluationContext1

base : VarList
base = [] ,′ [] ,′ []

+S : Signal -> VarList -> VarList
+S S' (S , s , v) =  ((Sunwrap S') ∷ S , s , v)

+s : SharedVar -> VarList ->  VarList
+s s' (S , s , v) =  (S , sunwrap s' ∷ s , v)

+x : SeqVar -> VarList -> VarList
+x x' (S , s , v) =  (S , s , vunwrap x' ∷ v)

Xs : VarList -> List ℕ
Xs (_ , _ , v) = v
Ss : VarList -> List ℕ
Ss (S , _ , _) = S
FVₑ : Expr -> VarList
FVₑ (plus []) = base
FVₑ (plus (num x ∷ x₁)) = FVₑ (plus x₁)
FVₑ (plus (seq-ref x ∷ x₁)) = +x x (FVₑ (plus x₁))
FVₑ (plus (shr-ref s ∷ x₁)) = +s s (FVₑ (plus x₁))

dist++ˡ : ∀{VL1 VL2 VL3} → (distinct VL1 (VL2 U̬ VL3)) → (distinct VL1 VL2)
dist++ˡ (a , b , c) =  (dist'++ˡ a) ,(dist'++ˡ b) ,(dist'++ˡ c)

dist++ʳ : ∀{VL1 VL2 VL3} → (distinct VL1 (VL2 U̬ VL3)) → (distinct VL1 VL3)
dist++ʳ{VL1}{VL2 = (v1 , v2 , v3)}{VL3 = (V1 , V2 , V3)} (a , b , c)
   =  (dist'++ʳ{V2 = v1}{V3 = V1} a)  , (dist'++ʳ{V2 = v2}{V3 = V2} b) , (dist'++ʳ{V2 = v3}{V3 = V3} c)



dist++b : ∀{VL1 VL2 VL3 VL4} → (distinct (VL1 U̬ VL2) (VL3 U̬ VL4)) → (distinct VL1 VL3)
dist++b (a , b , c) =  (dist'++b a) , (dist'++b b) , (dist'++b c)

dist:: : ∀{VL1 VL2 S} → (distinct VL1 (+S S VL2)) → (distinct VL1 VL2)
dist::{VL1}{(Ss , s , v)}{S} (a , b , c) = dist':: a  , b , c

data CorrectBinding : Term → VarList → VarList → Set where
  CBnothing : CorrectBinding nothin base base
  CBpause   : CorrectBinding pause base base
  CBsig     : ∀{p S BV FV} → CorrectBinding p BV FV
                         → CorrectBinding (signl S p) (+S S BV) (FV |̌ (+S S base))
  CBpresent : ∀{S p q BVp FVp BVq FVq}
               → (cbp : CorrectBinding p BVp FVp)
               → (cbq : CorrectBinding q BVq FVq)
               → CorrectBinding (present S ∣⇒ p ∣⇒ q) (BVp U̬ BVq) (+S S (FVp U̬ FVq))
  CBemit    : ∀{S} → CorrectBinding (emit S) base (+S S base)
  CBpar     : ∀{p q BVp FVp BVq FVq}
                → (cbp : CorrectBinding p BVp FVp)
                → (cbq : CorrectBinding q BVq FVq)
                → (BVp≠BVq : distinct BVp BVq)
                → (FVp≠BVq : distinct FVp BVq)
                → (BVp≠FVq : distinct BVp FVq)
                → (Xp≠Xq : distinct' (Xs FVp) (Xs FVq))
                → CorrectBinding (p ∥ q) (BVp U̬ BVq) (FVp U̬ FVq)
  CBloop    : ∀{p BV FV}
               → CorrectBinding p BV FV
               → (BV≠FV : distinct BV FV)
               → CorrectBinding (loop p) BV FV
  CBloopˢ   : ∀{p q BVp FVp BVq FVq}
               → CorrectBinding p BVp FVp
               → CorrectBinding q BVq FVq
               → (BVp≠FVq : distinct BVp FVq)
               → (BVq≠FVq : distinct BVq FVq)
               → CorrectBinding (loopˢ p q) (BVp U̬ BVq) (FVp U̬ FVq)
  CBseq     : ∀{p q BVp BVq FVp FVq}
                → (cbp : CorrectBinding p BVp FVp)
                → (cbq : CorrectBinding q BVq FVq)
                → (BVp≠FVq : distinct BVp FVq)
                → CorrectBinding (p >> q) (BVp U̬ BVq) (FVp U̬ FVq)
  CBsusp    : ∀{S p BV FV}
                → (cbp : CorrectBinding p BV FV)
                → ([S]≠BVp : distinct' [ (Sunwrap S) ] (Ss BV))
                → CorrectBinding (suspend p S) BV (+S S FV)
  CBexit    : ∀{n} → CorrectBinding (exit n) base base
  CBtrap    : ∀{p BV FV} → CorrectBinding p BV FV → CorrectBinding (trap p) BV FV
  CBshared  : ∀{s e p BV FV} → CorrectBinding p BV FV
                             → CorrectBinding (shared s ≔ e in: p)
                                              (+s s BV) ((FVₑ e) U̬ (FV |̌ (+s s base)))
  CBsset    : ∀{s e} → CorrectBinding (s ⇐ e) base (+s s (FVₑ e))
  CBvar     : ∀{x e p BV FV} → CorrectBinding p BV FV
                             → CorrectBinding (var x ≔ e in: p)
                                              (+x x BV) ((FVₑ e) U̬ (FV |̌ (+x x base)))
  CBvset    : ∀{x e} → CorrectBinding (x ≔ e) base (+x x (FVₑ e))
  CBif      : ∀{x p q BVp BVq FVp FVq}
              → (cbp : CorrectBinding p BVp FVp)
              → (cbq : CorrectBinding q BVq FVq)
              → CorrectBinding (if x ∣⇒ p ∣⇒ q) (BVp U̬ BVq) (+x x (FVp U̬ FVq))
  CBρ       : ∀{θ p BV FV} → CorrectBinding p BV FV
                           → CorrectBinding (ρ θ · p) (((Dom θ) U̬ BV)) (FV |̌ (Dom θ))


binding-is-function : ∀{p BV₁ FV₁ BV₂ FV₂} →
  CorrectBinding p BV₁ FV₁ →
  CorrectBinding p BV₂ FV₂ →
  BV₁ ≡ BV₂ × FV₁ ≡ FV₂
binding-is-function CBnothing CBnothing = refl , refl
binding-is-function CBpause CBpause = refl , refl
binding-is-function (CBsig cb₁) (CBsig cb₂)
  with binding-is-function cb₁ cb₂
... | (refl , refl) = refl , refl
binding-is-function (CBpresent cbp₁ cbq₁) (CBpresent cbp₂ cbq₂)
  with binding-is-function cbp₁ cbp₂ | binding-is-function cbq₁ cbq₂
... | (refl , refl) | (refl , refl) = refl , refl
binding-is-function CBemit CBemit = refl , refl
binding-is-function (CBpar cbp₁ cbq₁ BVp≠BVq₁ FVp≠BVq₁ BVp≠FVq₁ Xp≠Xq₁)
                    (CBpar cbp₂ cbq₂ BVp≠BVq₂ FVp≠BVq₂ BVp≠FVq₂ Xp≠Xq₂)
  with binding-is-function cbp₁ cbp₂ | binding-is-function cbq₁ cbq₂
... | (refl , refl) | (refl , refl) = refl , refl
binding-is-function (CBloop cb₁ BV≠FV₁)
                    (CBloop cb₂ BV≠FVV₂)
  with binding-is-function cb₁ cb₂
... | (refl , refl) = refl , refl
binding-is-function (CBloopˢ cbp₁ cbq₁ BVp≠FVq₁ BVq≠FVq₁)
                    (CBloopˢ cbp₂ cbq₂ BVp≠FVq₂ BVq≠FVq₂)
  with binding-is-function cbp₁ cbp₂ | binding-is-function cbq₁ cbq₂
... | (refl , refl) | (refl , refl) = refl , refl
binding-is-function (CBseq cbp₁ cbq₁ BV≠FV₁) (CBseq cbp₂ cbq₂ BV≠FV₂)
  with binding-is-function cbp₁ cbp₂ | binding-is-function cbq₁ cbq₂
... | (refl , refl) | (refl , refl) = refl , refl
binding-is-function (CBsusp cb₁ S∉BV₁) (CBsusp cb₂ S∉BV₂)
  with binding-is-function cb₁ cb₂
... | (refl , refl) = refl , refl
binding-is-function CBexit CBexit = refl , refl
binding-is-function (CBtrap cb₁) (CBtrap cb₂)
  with binding-is-function cb₁ cb₂
... | (refl , refl) = refl , refl
binding-is-function (CBshared cb₁) (CBshared cb₂)
  with binding-is-function cb₁ cb₂
... | (refl , refl) = refl , refl
binding-is-function CBsset CBsset = refl , refl
binding-is-function (CBvar cb₁) (CBvar cb₂)
  with binding-is-function cb₁ cb₂
... | (refl , refl) = refl , refl
binding-is-function CBvset CBvset = refl , refl
binding-is-function (CBif cbp₁ cbq₁) (CBif cbp₂ cbq₂)
  with binding-is-function cbp₁ cbp₂ | binding-is-function cbq₁ cbq₂
... | (refl , refl) | (refl , refl) = refl , refl
binding-is-function (CBρ cb₁) (CBρ cb₂)
  with binding-is-function cb₁ cb₂
... | (refl , refl) = refl , refl

binding-dec : ∀ p → Dec (∃ \ BV -> ∃ \ FV -> CorrectBinding p BV FV)

binding-dec nothin = yes (base , base , CBnothing)

binding-dec pause = yes (base , base , CBpause)

binding-dec (signl S p) with binding-dec p
binding-dec (signl S p) | yes (BV , FV , CBp) =
  yes (+S S BV , (FV |̌ (+S S base)) , CBsig CBp)
binding-dec (signl S p) | no ¬p = no (\ { (BV , FV , CBsig proj₃) → ¬p (_ , _ , proj₃) })

binding-dec (present S ∣⇒ p ∣⇒ q) with binding-dec p
binding-dec (present S ∣⇒ p ∣⇒ q) | yes p₂ with binding-dec q
binding-dec (present S ∣⇒ p ∣⇒ q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) =
  yes (BVp U̬ BVq , +S S (FVp U̬ FVq) , CBpresent CBp CBq)
binding-dec (present S ∣⇒ p ∣⇒ p₁) | yes p₂ | (no ¬p) =
  no (\ { (BV , FV , CBpresent BD BD₁) → ¬p (_ , _ , BD₁) } )
binding-dec (present S ∣⇒ p ∣⇒ p₁) | no ¬p =
  no (\ { (BV , FV , CBpresent BD BD₁) → ¬p (_ , _ , BD) } )

binding-dec (emit S) = yes (base , (Sunwrap S ∷ [] , [] , []) , CBemit)

binding-dec (p ∥ q) with binding-dec p
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) with binding-dec q
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) with distinct-dec BVp BVq
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) | yes BVp≠BVq  = no ¬CB
 where
   ¬CB : ¬ (∃ \ BV -> ∃ \ FV -> CorrectBinding (p ∥ q) BV FV)
   ¬CB (BV₂ , FV₂ , CBpar CBp₂ CBq₂ BVp≠BVq' FVp≠BVq' BVp≠FVq' Xp≠Xq') with (binding-is-function CBp CBp₂ , binding-is-function CBq CBq₂)
   ... | ((refl , refl) , (refl , refl)) = distinct-not-distinct-dec BVp≠BVq' BVp≠BVq
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) | no ¬BVp≠BVq with distinct-dec FVp BVq
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | (yes (BVq , FVq , CBq)) | (no ¬BVp≠BVq) | (yes FVp≠BVq) = no ¬CB
 where
   ¬CB : ¬ (∃ \ BV -> ∃ \ FV -> CorrectBinding (p ∥ q) BV FV)
   ¬CB (BV₂ , FV₂ , CBpar CBp₂ CBq₂ BVp≠BVq' FVp≠BVq' BVp≠FVq' Xp≠Xq') with (binding-is-function CBp CBp₂ , binding-is-function CBq CBq₂)
   ... | ((refl , refl) , (refl , refl)) = distinct-not-distinct-dec FVp≠BVq' FVp≠BVq
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | (yes (BVq , FVq , CBq)) | (no ¬BVp≠BVq) | (no ¬FVp≠BVq) with distinct-dec BVp FVq
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | (yes (BVq , FVq , CBq)) | (no ¬BVp≠BVq) | (no ¬FVp≠BVq) | (yes BVp≠FVq) = no ¬CB
 where
   ¬CB : ¬ (∃ \ BV -> ∃ \ FV -> CorrectBinding (p ∥ q) BV FV)
   ¬CB (BV₂ , FV₂ , CBpar CBp₂ CBq₂ BVp≠BVq' FVp≠BVq' BVp≠FVq' Xp≠Xq') with (binding-is-function CBp CBp₂ , binding-is-function CBq CBq₂)
   ... | ((refl , refl) , (refl , refl)) = distinct-not-distinct-dec BVp≠FVq' BVp≠FVq
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | (yes (BVq , FVq , CBq)) | (no ¬BVp≠BVq) | (no ¬FVp≠BVq) | (no ¬BVp≠FVq) with distinct'-dec (Xs FVp) (Xs FVq)
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | (yes (BVq , FVq , CBq)) | (no ¬BVp≠BVq) | (no ¬FVp≠BVq) | (no ¬BVp≠FVq) | (yes Xp≠Xq) = no ¬CB
 where
   ¬CB : ¬ (∃ \ BV -> ∃ \ FV -> CorrectBinding (p ∥ q) BV FV)
   ¬CB (BV₂ , FV₂ , CBpar CBp₂ CBq₂ BVp≠BVq' FVp≠BVq' BVp≠FVq' Xp≠Xq') with (binding-is-function CBp CBp₂ , binding-is-function CBq CBq₂)
   ... | ((refl , refl) , (refl , refl)) = Xp≠Xq' (proj₁ Xp≠Xq) (proj₁ (proj₂ Xp≠Xq)) (proj₂ (proj₂ Xp≠Xq))
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | (yes (BVq , FVq , CBq)) | (no ¬BVp≠BVq) | (no ¬FVp≠BVq) | (no ¬BVp≠FVq) | (no ¬Xp≠Xq) =
  yes (BVp U̬ BVq , FVp U̬ FVq , CBpar CBp CBq (distinct-dec-is-distinct  ¬BVp≠BVq)
                                           (distinct-dec-is-distinct  ¬FVp≠BVq)
                                           (distinct-dec-is-distinct  ¬BVp≠FVq)
                                           (λ z z∈xs z∈ys → ¬Xp≠Xq (z , z∈xs , z∈ys)))
binding-dec (p ∥ q) | yes (BVp , FVp , CBp) | no ¬p =
  no (\ { (BV , FV , CBpar X X₁ BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) → ¬p (_ , _ , X₁ ) } )
binding-dec (p ∥ q) | no ¬p =
  no (\ { (BV , FV , CBpar X X₁ BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) → ¬p (_ , _ , X) } )

binding-dec (loop p) with binding-dec p
binding-dec (loop p) | yes (BV , FV , CB) with distinct-dec BV FV
binding-dec (loop p) | yes (BV , FV , CB) | yes dec = no ¬CB
  where
   ¬CB : ¬ (∃ \ BV -> ∃ \ FV -> CorrectBinding (loop p) BV FV)
   ¬CB (BV₂ , FV₂ , CBloop CB₂  BV≠FV') with binding-is-function CB CB₂
   ... | (refl , refl) = distinct-not-distinct-dec BV≠FV' dec
binding-dec (loop p) | yes (BV , FV , CB) | no dec = yes (BV , (FV , (CBloop CB (distinct-dec-is-distinct dec))))
binding-dec (loop p) | no ¬p =
  no (\ { (BV , FV , CBloop CB BV≠FV) -> ¬p (_ , _ , CB) } )

binding-dec (loopˢ p q) with binding-dec p
binding-dec (loopˢ p q) | yes (BVp , FVq , CBp ) with binding-dec q
binding-dec (loopˢ p q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) with distinct-dec BVp FVq
binding-dec (loopˢ p q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) | yes BVp≠FVq = no ¬CB
 where
  ¬CB :  ¬ (∃ \ BV -> ∃ \ FV -> CorrectBinding (loopˢ p q) BV FV)
  ¬CB (BV₂ , FV₂ , CBloopˢ CBp₂ CBq₂ BVp≠FVq₂ BVq≠FVq₂) with (binding-is-function CBp CBp₂ , binding-is-function CBq CBq₂)
  ... | ((refl , refl) , (refl , refl)) = distinct-not-distinct-dec BVp≠FVq₂ BVp≠FVq
binding-dec (loopˢ p q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) | no ¬BVp≠FVq with distinct-dec BVq FVq
binding-dec (loopˢ p q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) | no ¬BVp≠FVq | yes ¬BVq≠FVq = no ¬CB where
  ¬CB : ¬ (∃ \ BV -> ∃ \ FV -> CorrectBinding (loopˢ p q) BV FV)
  ¬CB (BV₂ , FV₂ , CBloopˢ CBp₂ CBq₂ BVp≠FVq₂ BVq≠FVq₂)  with (binding-is-function CBp CBp₂ , binding-is-function CBq CBq₂)
  ... | ((refl , refl) , (refl , refl)) = distinct-not-distinct-dec BVq≠FVq₂ ¬BVq≠FVq
binding-dec (loopˢ p q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) | no BVp≠FVq | no BVq≠FVq =
   yes (BVp U̬ BVq , FVp U̬ FVq , CBloopˢ CBp CBq (distinct-dec-is-distinct BVp≠FVq) (distinct-dec-is-distinct BVq≠FVq))
binding-dec (loopˢ p q) | yes (BVp , FVq , CBp) | (no ¬CBq) =
  no (\ { (BV , FV , CBloopˢ CBp CBq BVp≠FVq BVq≠FVq) -> ¬CBq (_ , _ , CBq) } )
binding-dec (loopˢ p q) | no ¬CBp =
  no (\ { (BV , FV , CBloopˢ CBp CBq BVp≠FVq BVq≠FVq) -> ¬CBp (_ , _ , CBp) })


binding-dec (p >> q) with binding-dec p
binding-dec (p >> q) | yes (BVp , FVq , CBp ) with binding-dec q
binding-dec (p >> q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) with distinct-dec BVp FVq
binding-dec (p >> q) | yes (BVp , FVp , CBp) | (yes (BVq , FVq , CBq)) | (yes BVp≠FVq) = no ¬CB
 where
  ¬CB :  ¬ (∃ \ BV -> ∃ \ FV -> CorrectBinding (p >> q) BV FV)
  ¬CB (BV₂ , FV₂ , CBseq CBp₂ CBq₂ BVp≠FVq') with (binding-is-function CBp CBp₂ , binding-is-function CBq CBq₂)
  ... | ((refl , refl) , (refl , refl)) = distinct-not-distinct-dec BVp≠FVq' BVp≠FVq
binding-dec (p >> q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) | no ¬BVp≠FVq =
  yes  (BVp U̬ BVq , FVp U̬ FVq , CBseq CBp CBq (distinct-dec-is-distinct ¬BVp≠FVq))
binding-dec (p >> q) | yes (BVp , FVq , CBp) | (no ¬CBq) =
  no (\ { (BV , FV , CBseq CBp CBq BVp≠FVq) -> ¬CBq (_ , _ , CBq) } )
binding-dec (p >> q) | no ¬CBp =
  no (\ { (BV , FV , CBseq CBp CBq BVp≠FVq) -> ¬CBp (_ , _ , CBp) })

binding-dec (suspend p S) with binding-dec p
binding-dec (suspend p S) | yes (BV , FV , CB) with distinct'-dec [ (Sunwrap S) ] (Ss BV)
binding-dec (suspend p S) | yes (BV₁ , FV₁ , CB₁) | yes ([S]≠BVp₁ , [S]≠BVp₂ , [S]≠BVp₃) = no ¬CB
 where
   ¬CB : ¬ (∃ \ BV -> ∃ \ FV -> CorrectBinding (suspend p S) BV FV)
   ¬CB (BV₂ , FV₂ , CBsusp CB₃ [S]≠BVp') with (binding-is-function CB₁ CB₃)
   ... | refl , refl = [S]≠BVp' [S]≠BVp₁ [S]≠BVp₂ [S]≠BVp₃
binding-dec (suspend p S) | yes (BV , FV , CB) | (no ¬[S]≠BVp) =
  yes (BV , +S S FV , CBsusp CB (λ z z∈xs z∈ys → ¬[S]≠BVp (z , z∈xs , z∈ys)))
binding-dec (suspend p S) | no ¬p =
  no (\ { (BV , FV , CBsusp CB [S]≠BVp) -> ¬p (_ , _ , CB)})

binding-dec (trap p) with binding-dec p
binding-dec (trap p) | yes (BV , FV , CB) = yes (BV , FV , CBtrap CB)
binding-dec (trap p) | no ¬p =
  no (\ { (BV , FV , CBtrap CB ) -> ¬p (BV , FV , CB) })

binding-dec (exit x) = yes (base , base , CBexit)

binding-dec (shared s ≔ e in: p) with binding-dec p
binding-dec (shared s ≔ e in: p) | yes (BV , FV , CB) =
  yes (+s s BV , (FVₑ e) U̬ (FV |̌ (+s s base)) , CBshared CB)
binding-dec (shared s ≔ e in: p) | no ¬p =
  no (\ { (BV , FV , CBshared CB) -> ¬p (_ , _ , CB) })

binding-dec (s ⇐ e) = yes (base , +s s (FVₑ e) , CBsset)

binding-dec (var x ≔ e in: p) with binding-dec p
binding-dec (var x ≔ e in: p) | yes (BV , FV , CB) =
  yes (+x x BV , (FVₑ e) U̬ (FV |̌ (+x x base)) , CBvar CB)
binding-dec (var x ≔ e in: p) | no ¬p =
  no (\ { (BV , FV , CBvar CB) -> ¬p (_ , _ , CB) } )

binding-dec (x ≔ e) = yes (base , (+x x (FVₑ e)) , CBvset)

binding-dec (if x ∣⇒ p ∣⇒ q) with binding-dec p
binding-dec (if x ∣⇒ p ∣⇒ q) | yes p₁ with binding-dec q
binding-dec (if x ∣⇒ p₁ ∣⇒ q) | yes (BVp , FVp , CBp) | yes (BVq , FVq , CBq) =
  yes (BVp U̬ BVq , +x x (FVp U̬ FVq) , CBif CBp CBq)
binding-dec (if x ∣⇒ p ∣⇒ q) | yes p₁ | (no ¬p) =
  no (\ { (BV , FV , CBif CBp CBq) -> ¬p (_ , _ , CBq) })
binding-dec (if x ∣⇒ p ∣⇒ q) | no ¬p =
  no (\ { (BV , FV , CBif CBp CBq) -> ¬p (_ , _ , CBp) })

binding-dec (ρ θ · p) with binding-dec p
binding-dec (ρ θ · p) | yes (BV , FV , BP) =
  yes (((Dom θ) U̬ BV)  , FV |̌ (Dom θ) , CBρ BP)
binding-dec (ρ θ · p) | no ¬p = no (\ { (BV , FV , CBρ p ) -> ¬p (_ , _ , p) } )

binding-extract : ∀{p BV FV p' E} →
  CorrectBinding p BV FV →
  p ≐ E ⟦ p' ⟧e →
  ∃ λ { (BV' , FV') → (BV' ⊆ BV × FV' ⊆ FV) × CorrectBinding p' BV' FV' }
binding-extract cb                      dehole =
  _ , (⊆-refl , ⊆-refl) , cb
binding-extract (CBpar cbp cbq _ _ _ _) (depar₁ p≐E⟦p'⟧)
  with binding-extract cbp p≐E⟦p'⟧
... | (BV' , FV') , (BV'⊆BV , FV'⊆FV) , cb* = _ , (∪ˡ BV'⊆BV , ∪ˡ FV'⊆FV) , cb*
binding-extract {_} (CBpar {BVp = BVp} {FVp = FVp} cbp cbq _ _ _ _) (depar₂ q≐E⟦q'⟧)
  with binding-extract cbq q≐E⟦q'⟧
... | (BV' , FV') , (BV'⊆BV , FV'⊆FV) , cb* = _ , (∪ʳ BVp BV'⊆BV , ∪ʳ FVp FV'⊆FV) , cb*
binding-extract (CBseq cbp cbq _)       (deseq p≐E⟦p'⟧)
  with binding-extract cbp p≐E⟦p'⟧
... | (BV' , FV') , (BV'⊆BV , FV'⊆FV) , cb* = _ , (∪ˡ BV'⊆BV , ∪ˡ FV'⊆FV) , cb*
binding-extract (CBloopˢ cbp cbq _ _)   (deloopˢ p≐E⟦p'⟧)
  with binding-extract cbp p≐E⟦p'⟧
... | (BV' , FV') , (BV'⊆BV , FV'⊆FV) , cb* = _ , (∪ˡ BV'⊆BV , ∪ˡ FV'⊆FV) , cb*
binding-extract (CBsusp {S = S} cb _)   (desuspend p≐E⟦p'⟧)
  with binding-extract cb  p≐E⟦p'⟧
... | (BV' , FV') , (BV'⊆BV , FV'⊆FV) , cb* = _ , (BV'⊆BV , ∪ʳ (+S S base) FV'⊆FV) , cb*
binding-extract (CBtrap cb)             (detrap p≐E⟦p'⟧)
  with binding-extract cb  p≐E⟦p'⟧
... | (BV' , FV') , (BV'⊆BV , FV'⊆FV) , cb* = _ , (BV'⊆BV , FV'⊆FV) , cb*

binding-subst : ∀{p BVp FVp q BVq FVq r BVr FVr E} →
  CorrectBinding p BVp FVp →
  p ≐ E ⟦ q ⟧e →
  CorrectBinding q BVq FVq →
  BVr ⊆ BVq →
  FVr ⊆ FVq →
  CorrectBinding r BVr FVr →
  ∃ λ { (BV' , FV') → (BV' ⊆ BVp × FV' ⊆ FVp) × CorrectBinding (E ⟦ r ⟧e) BV' FV' }
binding-subst (CBpar {BVq = BVq'} {FVq = FVq'} cbp' cbq' BVp'≠BVq' FVp'≠BVq' BVp'≠FVq' Xp'≠Xq')
              (depar₁ p'≐E⟦q⟧) cbq BVr⊆BVq FVr⊆FVq cbr
  with binding-subst cbp' p'≐E⟦q⟧ cbq BVr⊆BVq FVr⊆FVq cbr
... | (BVp'' , FVp'') , (BVp''⊆BVp' , FVp''⊆FVp') , cbp'' =
  _ , (∪-respect-⊆-left BVp''⊆BVp' , ∪-respect-⊆-left FVp''⊆FVp') ,
  CBpar cbp'' cbq'
        (⊆-respect-distinct-left BVp''⊆BVp' BVp'≠BVq')
        (⊆-respect-distinct-left FVp''⊆FVp' FVp'≠BVq')
        (⊆-respect-distinct-left BVp''⊆BVp' BVp'≠FVq')
        (⊆¹-respect-distinct'-left (proj₂ (proj₂ FVp''⊆FVp')) Xp'≠Xq')
binding-subst (CBpar {BVp = BVp'} {FVp = FVp'} cbp' cbq' BVp'≠BVq' FVp'≠BVq' BVp'≠FVq' Xp'≠Xq')
              (depar₂ q'≐E⟦q⟧) cbq BVr⊆BVq FVr⊆FVq cbr
  with binding-subst cbq' q'≐E⟦q⟧ cbq BVr⊆BVq FVr⊆FVq cbr
... | (BVq'' , FVq'') , (BVq''⊆BVq' , FVq''⊆FVq') , cbq'' =
  _ , (∪-respect-⊆-right BVp' BVq''⊆BVq' , ∪-respect-⊆-right FVp' FVq''⊆FVq') ,
  CBpar cbp' cbq''
        (⊆-respect-distinct-right BVq''⊆BVq' BVp'≠BVq')
        (⊆-respect-distinct-right BVq''⊆BVq' FVp'≠BVq')
        (⊆-respect-distinct-right FVq''⊆FVq' BVp'≠FVq')
        (⊆¹-respect-distinct'-right (proj₂ (proj₂ FVq''⊆FVq')) Xp'≠Xq')
binding-subst (CBseq {BVq = BVq'} {FVq = FVq'} cbp' cbq' BV≠FV)
              (deseq p'≐E⟦q⟧) cbq BVr⊆BVq FVr⊆FVq cbr
  with binding-subst cbp' p'≐E⟦q⟧ cbq BVr⊆BVq FVr⊆FVq cbr
... | (BVp'' , FVp'') , (BVp''⊆BVp' , FVp''⊆FVp') , cbp'' =
  _ , (∪-respect-⊆-left BVp''⊆BVp' , ∪-respect-⊆-left FVp''⊆FVp') ,
  CBseq cbp'' cbq' (⊆-respect-distinct-left BVp''⊆BVp' BV≠FV)
binding-subst (CBloopˢ {BVq = BVq'} {FVq = FVq'} cbp' cbq' BVp≠FVq BVq≠FVq)
              (deloopˢ p'≐E⟦q⟧) cbq BVr⊆BVq FVr⊆FVq cbr
  with binding-subst cbp' p'≐E⟦q⟧ cbq BVr⊆BVq FVr⊆FVq cbr
... | (BVp'' , FVp'') , (BVp''⊆BVp' , FVp''⊆FVp') , cbp'' =
  _ , (∪-respect-⊆-left BVp''⊆BVp' , ∪-respect-⊆-left FVp''⊆FVp') ,
  CBloopˢ cbp'' cbq' (⊆-respect-distinct-left BVp''⊆BVp' BVp≠FVq) BVq≠FVq
binding-subst (CBsusp {S} {FV = FVp'} cbp' S∉BVp') (desuspend p'≐E⟦q⟧) cbq BVr⊆BVq FVr⊆FVq cbr
  with binding-subst cbp' p'≐E⟦q⟧ cbq BVr⊆BVq FVr⊆FVq cbr
... | (BVp'' , FVP'') , (BVp''⊆BVp' , FVp''⊆FVp') , cbp'' =
  _ , (BVp''⊆BVp' , (∪¹-respect-⊆¹-right [ Signal.unwrap S ] ,′ id ,′ id # FVp''⊆FVp')) ,
  CBsusp cbp'' (⊆¹-respect-distinct'-right (proj₁ BVp''⊆BVp') S∉BVp')
binding-subst (CBtrap cbp') (detrap p'≐E⟦q⟧) cbq BVr⊆BVq FVr⊆FVq cbr
  with binding-subst cbp' p'≐E⟦q⟧ cbq BVr⊆BVq FVr⊆FVq cbr
... | (BVp'' , FVp'') , ⟨BVp''⊆BVp'⟩×⟨FVp''⊆FVp'⟩ , cbp'' =
  _ , ⟨BVp''⊆BVp'⟩×⟨FVp''⊆FVp'⟩ , CBtrap cbp''
binding-subst cbp dehole cbq BVr⊆BVq FVr⊆FVq cbr
  with binding-is-function cbp cbq
... | (refl , refl) = _ , (BVr⊆BVq , FVr⊆FVq) , cbr

binding-extractc' : ∀{p BV FV p' C} →
  CorrectBinding p BV FV →
  p ≐ C ⟦ p' ⟧c →
  ∃ λ { (BV' , FV') → CorrectBinding p' BV' FV' }
binding-extractc' cbp dchole =
  _ , cbp
binding-extractc' (CBsig cbp) (dcsignl p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBpresent cbp cbp₁) (dcpresent₁ p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBpresent cbp cbp₁) (dcpresent₂ p≐C⟦p'⟧) =
  binding-extractc' cbp₁ p≐C⟦p'⟧
binding-extractc' (CBpar cbp cbp₁ BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (dcpar₁ p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBpar cbp cbp₁ BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (dcpar₂ p≐C⟦p'⟧) =
  binding-extractc' cbp₁ p≐C⟦p'⟧
binding-extractc' (CBloop cbp BV≠FV) (dcloop p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBloopˢ CBp CBq BVp≠FVq BVq≠FVq) (dcloopˢ₁ p≐C⟦p'⟧) =
  binding-extractc' CBp p≐C⟦p'⟧
binding-extractc' (CBloopˢ CBp CBq BVp≠FVq BVq≠FVq) (dcloopˢ₂ q≐C⟦q'⟧) =
  binding-extractc' CBq q≐C⟦q'⟧
binding-extractc' (CBseq cbp cbp₁ BVp≠FVq) (dcseq₁ p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBseq cbp cbp₁ BVp≠FVq) (dcseq₂ p≐C⟦p'⟧) =
  binding-extractc' cbp₁ p≐C⟦p'⟧
binding-extractc' (CBsusp cbp [S]≠BVp) (dcsuspend p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBtrap cbp) (dctrap p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBshared cbp) (dcshared p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBvar cbp) (dcvar p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBif cbp cbp₁) (dcif₁ p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧
binding-extractc' (CBif cbp cbp₁) (dcif₂ p≐C⟦p'⟧) =
  binding-extractc' cbp₁ p≐C⟦p'⟧
binding-extractc' (CBρ cbp) (dcenv p≐C⟦p'⟧) =
  binding-extractc' cbp p≐C⟦p'⟧

binding-substc' : ∀{p BVp FVp q BVq FVq r BVr FVr C} →
  CorrectBinding p BVp FVp →
  p ≐ C ⟦ q ⟧c →
  CorrectBinding q BVq FVq →
  BVr ⊆ BVq →
  FVr ⊆ FVq →
  CorrectBinding r BVr FVr →
  ∃ λ { (BV' , FV') → (BV' ⊆ BVp × FV' ⊆ FVp) × CorrectBinding (C ⟦ r ⟧c) BV' FV' }

binding-substc' CBp dchole CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-is-function CBp CBq
... | refl , refl = _ , (BVr⊆BVq , FVr⊆FVq) , CBr

binding-substc' (CBpar  cbp cbp₁ BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq)
                (dcpar₁ dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (∪-respect-⊆-left bvsub , ∪-respect-⊆-left fvsub) ,
  CBpar  cb1 cbp₁ (⊆-respect-distinct-left bvsub BVp≠BVq)
                  (⊆-respect-distinct-left fvsub FVp≠BVq)
                  (⊆-respect-distinct-left bvsub BVp≠FVq)
                  (⊆¹-respect-distinct'-left (thd fvsub) Xp≠Xq)

binding-substc' (CBpar{BVp = BVp}{FVp = FVp} cbp cbp₁ BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq)
                (dcpar₂ dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp₁ dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub ,  fvsub) , cb1 =
  _ , (∪-respect-⊆-right BVp bvsub , ∪-respect-⊆-right FVp fvsub) ,
  CBpar cbp cb1 (⊆-respect-distinct-right bvsub BVp≠BVq)
                (⊆-respect-distinct-right bvsub FVp≠BVq)
                (⊆-respect-distinct-right fvsub BVp≠FVq)
                (⊆¹-respect-distinct'-right (thd fvsub) Xp≠Xq)

binding-substc' (CBseq cbp cbp₁ BVp≠FVq)
                (dcseq₁ dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (∪-respect-⊆-left bvsub , ∪-respect-⊆-left fvsub) ,
  CBseq cb1 cbp₁ (⊆-respect-distinct-left bvsub BVp≠FVq)

binding-substc' (CBseq{BVp = BVp}{FVp = FVp} cbp cbp₁ BVp≠FVq)
                (dcseq₂ dc) CBq BVr⊆BVq FVr⊆FVq CBr
   with  binding-substc' cbp₁ dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
   _ , (∪-respect-⊆-right BVp bvsub , ∪-respect-⊆-right FVp fvsub) ,
   CBseq cbp cb1 (⊆-respect-distinct-right fvsub  BVp≠FVq)

binding-substc' (CBsusp{S = S} cbp [S]≠BVp)
                (dcsuspend dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
   _ ,  (bvsub , ((∷-respect-⊆¹ (Signal.unwrap S)) , id , id # fvsub)) ,
   CBsusp cb1 (⊆¹-respect-distinct'-right (fst bvsub) [S]≠BVp)

binding-substc' (CBtrap CBp) (dctrap dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' CBp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (bvsub , fvsub) , CBtrap cb1

binding-substc' (CBsig{S = S ₛ} cbp) (dcsignl dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (((∷-respect-⊆¹ S) , id , id # bvsub) ,
       ⊆-respect-|̌ (+S (S ₛ) base) fvsub),
  CBsig cb1

binding-substc' (CBpresent{S = S ₛ} cbp cbp₁)
                (dcpresent₁ dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (∪-respect-⊆-left bvsub ,
       ((∷-respect-⊆¹ S) , id , id # (∪-respect-⊆-left fvsub))) ,
  CBpresent cb1 cbp₁

binding-substc' (CBpresent{S = S ₛ}{BVp = BVp}{FVp = FVp} cbp cbp₁)
                (dcpresent₂ dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp₁ dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (∪-respect-⊆-right BVp bvsub ,
       ((∷-respect-⊆¹ S) , id , id # (∪-respect-⊆-right FVp fvsub))) ,
  CBpresent cbp cb1

binding-substc' (CBloop cbp BV≠FV)
                (dcloop dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (∪-respect-⊆-right base bvsub , fvsub) ,
  CBloop cb1 (⊆-respect-distinct-left bvsub
              (⊆-respect-distinct-right fvsub BV≠FV))

binding-substc' (CBloopˢ cbp cbp₁ BVp≠FVq BVq≠FVq)
                (dcloopˢ₁ dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (∪-respect-⊆-left bvsub , ∪-respect-⊆-left fvsub) ,
  CBloopˢ cb1 cbp₁ (⊆-respect-distinct-left bvsub BVp≠FVq) BVq≠FVq

binding-substc' (CBloopˢ{BVp = BVp}{FVp = FVp} cbp cbp₁ BVp≠FVq BVq≠FVq)
                (dcloopˢ₂ dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp₁ dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (∪-respect-⊆-right BVp bvsub , ∪-respect-⊆-right FVp fvsub) ,
  CBloopˢ cbp cb1 (⊆-respect-distinct-right fvsub  BVp≠FVq)
                  (⊆-respect-distinct-left bvsub
                   (⊆-respect-distinct-right fvsub BVq≠FVq))

binding-substc' (CBshared{s = s}{e = e} cbp)
                (dcshared dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
 _ , (((id , (∷-respect-⊆¹ (SharedVar.unwrap s)) , id # bvsub)) ,
      ∪-respect-⊆-right (FVₑ e) (⊆-respect-|̌ (+s s base) fvsub)) ,
 CBshared cb1

binding-substc' (CBvar{x = x}{e = e} cbp) (dcvar dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (((id , id , (∷-respect-⊆¹ (SeqVar.unwrap x)) # bvsub)) ,
        ∪-respect-⊆-right (FVₑ e) (⊆-respect-|̌ (+x x base) fvsub)) ,
  CBvar cb1

binding-substc' (CBif{x = x ᵥ} cbp cbp₁) (dcif₁ dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (∪-respect-⊆-left bvsub , (id , id , (∷-respect-⊆¹ x) # (∪-respect-⊆-left fvsub))) ,
  CBif cb1 cbp₁

binding-substc' (CBif{x = x ᵥ}{BVp = BVp}{FVp = FVp} cbp cbp₁)
                (dcif₂ dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp₁ dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
  _ , (∪-respect-⊆-right BVp bvsub ,
       (id , id , (∷-respect-⊆¹ x) # (∪-respect-⊆-right FVp fvsub))) ,
  CBif cbp cb1

binding-substc' (CBρ{θ = θ} cbp) (dcenv dc) CBq BVr⊆BVq FVr⊆FVq CBr
  with binding-substc' cbp dc CBq BVr⊆BVq FVr⊆FVq CBr
... | _ , (bvsub , fvsub) , cb1 =
 _ , (∪-respect-⊆-right (Dom θ) bvsub , ⊆-respect-|̌ (Dom θ) fvsub) ,
 CBρ cb1


-- In the decomposition E ⟦ p ⟧e, the bound variables in p and the free
-- variables in E must be disjoint.
distinct-term-context-help : ∀ {BV FV BVp FVp BVnothin FVnothin} p E →
  CorrectBinding (E ⟦ p ⟧e) BV FV →
  CorrectBinding p BVp FVp →
  (BVp ⊆ BV) →
  CorrectBinding (E ⟦ nothin ⟧e) BVnothin FVnothin →
  distinct BVp FVnothin
distinct-term-context-help p [] cb cbp BVp⊆BV CBnothing =
  (λ _ _ ()) ,′ (λ _ _ ()) ,′ (λ _ _ ())
distinct-term-context-help p (epar₁ q ∷ E)
  (CBpar cbp' cbq' BVp'≠BVq' FVp'≠BVq' BVp'≠FVq' Xp'≠Xq') cbp BVp⊆BV
  (CBpar cbnothinp cbnothinq BVp≠BVq₁ FVp≠BVq₁ BVp≠FVq₁ Xp≠Xq₁)
  with binding-extract cbp' (((E ⟦ p ⟧e) ≐ E ⟦ p ⟧e) ∋ plug refl)
... | (BV' , FV') , (BV'⊆BVE⟦p⟧ , FV'⊆FVE⟦p⟧) , cbp*
  with binding-is-function cbp cbp* | binding-is-function cbq' cbnothinq
... | refl , refl | refl , refl =
  distinct-union-right
    (distinct-term-context-help p E cbp' cbp BV'⊆BVE⟦p⟧ cbnothinp)
    (⊆-respect-distinct-left BV'⊆BVE⟦p⟧ BVp'≠FVq')
distinct-term-context-help p (epar₂ p₁ ∷ E)
  (CBpar cbp' cbq' BVp'≠BVq' FVp'≠BVq' BVp'≠FVq' Xp'≠Xq') cbp BVp⊆BV
  (CBpar {FVq = FVnothinq} cbnothinp cbnothinq BVp≠BVq₁ FVp≠BVq₁ BVp≠FVq₁ Xp≠Xq₁)
  with binding-extract cbq' (((E ⟦ p ⟧e) ≐ E ⟦ p ⟧e) ∋ plug refl)
... | (BV' , FV') , (BV'⊆BVE⟦p⟧ , FV'⊆FVE⟦p⟧) , cbp*
  with binding-is-function cbp cbp* | binding-is-function cbp' cbnothinp
... | refl , refl | refl , refl =
  ⊆-respect-distinct-right
    (∪-comm-⊆-right FVnothinq ⊆-refl)
    (distinct-union-right
      (distinct-term-context-help p E cbq' cbp BV'⊆BVE⟦p⟧ cbnothinq)
      (⊆-respect-distinct-left BV'⊆BVE⟦p⟧ (distinct-sym FVp'≠BVq')))

distinct-term-context-help p (eseq q ∷ E)
  (CBseq {BVp = BVE⟦p⟧p} {FVp = FVE⟦p⟧p} cbp' cbq' BVp'≠FVq') cbp BVp⊆BV
  (CBseq {BVp = BVnothinp} {BVq = BVnothinq} {FVp = FVnothinp} {FVq = FVnothinq}
         cbnothinp cbnothinq BVp≠FVq)
  with binding-extract cbp' (((E ⟦ p ⟧e) ≐ E ⟦ p ⟧e) ∋ plug refl)
... | (BV' , FV') , (BV'⊆BVE⟦p⟧ , FV'⊆FVE⟦p⟧) , cbp*
  with binding-is-function cbp cbp* | binding-is-function cbq' cbnothinq
... | refl , refl | refl , refl =
  distinct-union-right
    (distinct-term-context-help p E cbp' cbp BV'⊆BVE⟦p⟧ cbnothinp)
    (⊆-respect-distinct-left
     BV'⊆BVE⟦p⟧
     (distinct-sym (dist++ˡ (distinct-sym (distinct-union-left BVp'≠FVq' BVp≠FVq)))))

distinct-term-context-help p (eloopˢ q ∷ E)
  (CBloopˢ {BVp = BVE⟦p⟧p} {FVp = FVE⟦p⟧p} cbp' cbq' BVp'≠FVq' BVq'≠FVq') cbp BVp⊆BV
  (CBloopˢ {BVp = BVnothinp} {FVp = FVnothinp} {BVq = BVnothinq} {FVq = FVnothinq}
           cbnothinp cbnothinq BVp≠FVq BVq≠FVq)
  with binding-extract cbp' (((E ⟦ p ⟧e) ≐ E ⟦ p ⟧e) ∋ plug refl)
... | (BV' , FV') , (BV'⊆BVE⟦p⟧ , FV'⊆FVE⟦p⟧) , cbp*
  with binding-is-function cbp cbp* | binding-is-function cbq' cbnothinq
... | refl , refl | refl , refl =
   distinct-union-right
    (distinct-term-context-help p E cbp' cbp BV'⊆BVE⟦p⟧ cbnothinp)
    (⊆-respect-distinct-left
     BV'⊆BVE⟦p⟧
     (distinct-sym (dist++ˡ (distinct-sym (distinct-union-left BVp'≠FVq' BVp≠FVq)))))

distinct-term-context-help {BVp = BVp} p (esuspend S ∷ E)
  (CBsusp cb [S]≠BVp) cbp BVp⊆BV
  (CBsusp {FV = FV} cbnothin [S]≠BVp₁) = BVp≠S∷FV ,′ id ,′ id # dist
  where dist = distinct-term-context-help p E cb cbp BVp⊆BV cbnothin
        BVp≠S∷FV : (typeof (proj₁ dist)) → ∀ S' → S' ∈ (proj₁ BVp) → S' ∈ (Signal.unwrap S ∷ proj₁ FV) → ⊥
        BVp≠S∷FV BVp≠FV S' S'∈BVp (here refl) = [S]≠BVp S' (here refl) (proj₁ BVp⊆BV S' S'∈BVp)
        BVp≠S∷FV BVp≠FV S' S'∈BVp (there S'∈FV) = BVp≠FV S' S'∈BVp S'∈FV
distinct-term-context-help p (etrap ∷ E)
  (CBtrap cb) cbp BVp⊆BV
  (CBtrap cbnothin) =
  distinct-term-context-help p E cb cbp BVp⊆BV cbnothin

BVars : ∀ (p : Term) -> VarList
BVars nothin = base
BVars pause = base
BVars (signl S p) = +S S (BVars p)
BVars (present S ∣⇒ p ∣⇒ q) = BVp U̬ BVq where
  BVp = BVars p
  BVq = BVars q
BVars (emit S) = base
BVars (p ∥ q) = BVp U̬ BVq where
  BVp = BVars p
  BVq = BVars q
BVars (loop p) = BV where
  BV = BVars p
BVars (loopˢ p q) = BVp U̬ BVq where
  BVp = BVars p
  BVq = BVars q
BVars (p >> q) = BVp U̬ BVq where
  BVp = BVars p
  BVq = BVars q
BVars (suspend p S) = BVars p
BVars (trap p) = BVars p
BVars (exit x) = base
BVars (shared s ≔ e in: p) = +s s (BVars p)
BVars (s ⇐ e) = base
BVars (var x ≔ e in: p) =  +x x (BVars p)
BVars (x ≔ e) = base
BVars (if x ∣⇒ p ∣⇒ q) =  BVp U̬ BVq where
  BVp = BVars p
  BVq = BVars q
BVars (ρ θ · p) = (Dom θ) U̬ BV where
  BV = BVars p

FVars : ∀ (p : Term) -> VarList
FVars nothin = base
FVars pause = base
FVars (signl S p) =  FV |̌ (+S S base) where
  FV = FVars p
FVars (present S ∣⇒ p ∣⇒ q) =  +S S (FVp U̬ FVq) where
  FVp = FVars p
  FVq = FVars q
FVars (emit S) =  +S S base
FVars (p ∥ q) = FVp U̬ FVq where
  FVp = FVars p
  FVq = FVars q
FVars (loop p) = FVars p
FVars (loopˢ p q) = FVp U̬ FVq where
  FVp = FVars p
  FVq = FVars q
FVars (p >> q) =  FVp U̬ FVq where
  FVp = FVars p
  FVq = FVars q
FVars (suspend p S) = +S S (FVars p)
FVars (trap p) = FVars p
FVars (exit x) = base
FVars (shared s ≔ e in: p) = (FVₑ e) U̬ (FV |̌ (+s s base)) where
  FV = FVars p
FVars (s ⇐ e) = +s s (FVₑ e) where
FVars (var x ≔ e in: p) = (FVₑ e) U̬ (FV |̌ (+x x base)) where
  FV = FVars p
FVars (x ≔ e) = +x x (FVₑ e)
FVars (if x ∣⇒ p ∣⇒ q) = +x x (FVp U̬ FVq) where
  FVp = FVars p
  FVq = FVars q
FVars (ρ θ · p) = FV |̌ (Dom θ) where
  FV = FVars p

CB : Term -> Set
CB p = CorrectBinding p (BVars p) (FVars p)


BVFVcorrect : ∀ p BV FV -> CorrectBinding p BV FV -> BVars p ≡ BV × FVars p ≡ FV
BVFVcorrect .nothin .([] , [] , []) .([] , [] , []) CBnothing = refl , refl
BVFVcorrect .pause .([] , [] , []) .([] , [] , []) CBpause = refl , refl
BVFVcorrect .(signl _ _) .(+S S BV) .(FV |̌ (+S S base))
            (CBsig{p}{S}{BV}{FV} CB) with BVFVcorrect p BV FV CB
... | refl , refl = refl , refl
BVFVcorrect .(present _ ∣⇒ _ ∣⇒ _) .(BVp U̬ BVq) .(+S S (FVp U̬ FVq))
            (CBpresent{S}{p}{q}{BVp}{FVp}{BVq}{FVq} CBp CBq) with
            BVFVcorrect p BVp FVp CBp | BVFVcorrect q BVq FVq CBq
... | refl , refl | refl , refl = refl , refl
BVFVcorrect .(emit _) _ _ CBemit = refl , refl
BVFVcorrect .(_ ∥ _) .(BVp U̬ BVq) .(FVp U̬ FVq)
            (CBpar{p}{q}{BVp}{FVp}{BVq}{FVq} CBp CBq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) with
            BVFVcorrect p BVp FVp CBp | BVFVcorrect q BVq FVq CBq
... | refl , refl | refl , refl = refl , refl
BVFVcorrect .(loop _) .BV .FV
            (CBloop{p}{BV}{FV} CB BV≠FV) with
            BVFVcorrect p BV FV CB
... | refl , refl = refl , refl
BVFVcorrect .(loopˢ _ _) .(BVp U̬ BVq) .(FVp U̬ FVq)
            (CBloopˢ{p}{q}{BVp}{FVp}{BVq}{FVq} CBp CBq BVp≠FVq BVq≠FVq) with
            BVFVcorrect p BVp FVp CBp | BVFVcorrect q BVq FVq CBq
... | refl , refl | refl , refl = refl , refl
BVFVcorrect .(_ >> _) .(BVp U̬ BVq) .(FVp U̬ FVq)
            (CBseq{p}{q}{BVp}{BVq}{FVp}{FVq} CBp CBq BVp≠FVq) with
            BVFVcorrect p BVp FVp CBp | BVFVcorrect q BVq FVq CBq
... | refl , refl | refl , refl = refl , refl
BVFVcorrect .(suspend _ _) .BV .(+S S FV)
            (CBsusp{S}{p}{BV}{FV} CB [S]≠BVp) with
            BVFVcorrect p BV FV CB
... | refl , refl = refl , refl
BVFVcorrect .(trap _) .BV .FV (CBtrap{p}{BV}{FV} CB) with
             BVFVcorrect p BV FV CB
... | refl , refl = refl , refl
BVFVcorrect .(exit _) .([] , [] , []) .([] , [] , []) CBexit = refl , refl
BVFVcorrect .(shared _ ≔ _ in: _) .(+s s BV) .((FVₑ e) U̬ (FV |̌ (+s s base)))
            (CBshared{s}{e}{p}{BV}{FV} CB) with
            BVFVcorrect p BV FV CB
... | refl , refl = refl , refl
BVFVcorrect .(_ ⇐ _) .([] , [] , []) .(+s s (FVₑ e)) (CBsset{s}{e}) = refl , refl
BVFVcorrect .(var _ ≔ _ in: _) .(+x x BV) .((FVₑ e) U̬ (FV |̌ (+x x base)))
            (CBvar{x}{e}{p}{BV}{FV} CB) with
            BVFVcorrect p BV FV CB
... | refl , refl = refl , refl
BVFVcorrect .(_ ≔ _) .([] , [] , []) .(+x x (FVₑ e)) (CBvset{x}{e}) = refl , refl
BVFVcorrect .(if _ ∣⇒ _ ∣⇒ _) .(BVp U̬ BVq) .(+x x (FVp U̬ FVq))
            (CBif{x}{p}{q}{BVp}{BVq}{FVp}{FVq} CBp CBq) with
            BVFVcorrect p BVp FVp CBp | BVFVcorrect q BVq FVq CBq
... | refl , refl | refl , refl = refl , refl
BVFVcorrect .(ρ _ · _) .(((Dom θ) U̬ BV)) .(FV |̌ (Dom θ))
            (CBρ{θ}{p}{BV}{FV} CB) with BVFVcorrect p BV FV CB
... | refl , refl = refl , refl

