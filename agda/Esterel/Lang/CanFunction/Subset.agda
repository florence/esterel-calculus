module Esterel.Lang.CanFunction.Subset where

open import utility
  renaming (_U̬_ to _∪_ ; _|̌_ to _-_)

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.CanFunction
open import Esterel.Lang.CanFunction.Base
open import Esterel.Lang.Properties
  using (halted ; paused ; done)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)
open import Data.OrderedListMap(Signal)(Signal.unwrap)(Signal.Status) as OLST
open import Data.Sublist as SL
  using (Sublist ; visit ; get)
open import Data.Sublist.Properties as SLProp
  using ()
open import Data.FiniteMap.Properties(Signal) as FMPropSig
  using ()

open import Data.Bool
  using (Bool ; not ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List as List
  using (List ; [] ; _∷_ ; _++_ ; map )
open import Data.List.Properties
  using (map-id ; length-map)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using (++⁻)
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ)
open import Data.Maybe
  using (Maybe ; maybe ; just ; nothing)
open import Data.Nat as Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_)
open import Data.Nat.Properties
  using (+-suc ; +-identityʳ)
open import Data.Product as Prod
  using (Σ ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_ ; ∃-syntax ; Σ-syntax)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; id ; _∋_ ; _$_ ; _|>_ ; const)
open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality as Prop
  using (_≡_ ; refl ; trans ; sym ; cong ; subst ; subst₂ ; inspect ; [_] ; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality as Het
  using (_≅_ ; ≅-to-≡ ; ≡-to-≅ ; ≅-to-subst-≡ ; ≅-to-type-≡)
  renaming (refl to hrefl ; cong to hcong ; sym to hsym)

open ≡-Reasoning


CanResult = SigSet.ST × CodeSet.ST × ShrSet.ST

Canθ-lookup : ∀ sigs → (S : Signal) →  (S∈ : SigMap.∈Dom{Signal.Status} S sigs) → Env → (Env → CanResult) → CanResult
Canθ-lookup sigs S S∈ θ visit with SigMap.lookup{k = S} sigs S∈
... | Signal.present = visit $ θ ← [S]-env-present S
... | Signal.absent = visit $ θ ← [S]-env-absent S
... | Signal.unknown
  with any (Nat._≟_ (Signal.unwrap S)) $ proj₁ (visit (θ ← [S]-env S))
... | yes _ = visit $ θ ← [S]-env S
... | no _ = visit $ θ ← [S]-env-absent S

Canθ-visit : Term → SigMap.Map Signal.Status → Env →  CanResult
Canθ-visit p sigs θ
  = SigMap.key-visit sigs (Canθ-lookup sigs) (Can p) θ

add-n-nothings : ℕ → SigMap.Map Signal.Status → SigMap.Map Signal.Status
add-n-nothings 0 s = s
add-n-nothings (suc n) s = nothing ∷ (add-n-nothings n s)

add-nothing-on-empty : ∀ n → (SigMap.keys (add-n-nothings n [])) ≡ []
add-nothing-on-empty 0 = refl
add-nothing-on-empty (suc n) rewrite (add-nothing-on-empty n) = refl

add-nothing-on-empty∈ : ∀ n → (SigMap.keys+∈ (add-n-nothings n [])) ≡ []
add-nothing-on-empty∈ 0 = refl
add-nothing-on-empty∈ (suc n) rewrite (add-nothing-on-empty n) = refl

add-nothing-swap : ∀ n l → (add-n-nothings n (nothing ∷ l)) ≡  (nothing ∷ (add-n-nothings n l))
add-nothing-swap 0 l = refl
add-nothing-swap (suc n) l rewrite add-nothing-swap n l = refl

add-nothing-add : ∀ n l → (add-n-nothings n (nothing ∷ l)) ≡ (add-n-nothings (suc n) l)
add-nothing-add zero l = refl
add-nothing-add (suc n) l rewrite add-nothing-add n l = refl

canθ-n-empty-irr : ∀ n k p θ → Canθ (add-n-nothings n []) k p θ ≡ Can p θ
canθ-n-empty-irr zero k p θ = refl
canθ-n-empty-irr (suc n) k p θ = canθ-n-empty-irr n (suc k) p θ

canθ-first-swap : ∀ n k sigs p θ x
                      → ∃[ stat ]
                        ((Canθ (add-n-nothings n (just x ∷ sigs)) k p θ
                         ≡
                         Canθ (add-n-nothings (suc n) sigs) k p (θ ← [ (n + k) ₛ ↦ stat ]))
                         × 
                         (Canθ (just x ∷ sigs) (n + k) p θ
                          ≡
                          Canθ sigs (n + suc k) p (θ ← [ (n + k) ₛ ↦ stat ])))
canθ-first-swap zero k sigs p θ Signal.present = Signal.present , refl , refl
canθ-first-swap zero k sigs p θ Signal.absent = Signal.absent , refl , refl
canθ-first-swap zero k sigs p θ Signal.unknown
  with any (Nat._≟_ k) (Canθₛ sigs (suc k) p (θ ← [S]-env (k ₛ)))
... | yes _ = Signal.unknown , refl , refl
... | no _ = Signal.absent , refl , refl
canθ-first-swap (suc n) k sigs p θ x
  with canθ-first-swap n (suc k) sigs p θ x
     | +-suc n k
     | +-suc n (suc k)
... | (m , a , c) | b | d =  m , subst (λ n2 → (Canθ (add-n-nothings n (just x ∷ sigs)) (suc k) p θ
                                         ≡
                                         Canθ (add-n-nothings (suc n) sigs) (suc k) p (θ ← [ n2 ₛ ↦ m ])))
                                b a
                           , subst₂ (λ n2 n3 → (Canθ (just x ∷ sigs) n2 p θ
                                                 ≡
                                                Canθ sigs n3 p (θ ← [ n2 ₛ ↦ m ])))

                                    b d c

canθ-lift-n : ∀ sigs n k p θ → Canθ sigs (n + k) p θ ≡ Canθ (add-n-nothings n sigs) k p θ
canθ-lift-n [] n k p θ rewrite canθ-n-empty-irr n k p θ = refl
canθ-lift-n (nothing ∷ sigs) n k p θ rewrite add-nothing-add n sigs = canθ-lift-n sigs (suc n) k p θ
canθ-lift-n (just x ∷ sigs) n k p θ
  with canθ-first-swap n k sigs p θ x
     | +-suc n k
... | (m , a , c) | b with (canθ-lift-n sigs n (suc k) p (θ ← [ ((n + k) ₛ) ↦ m ])) | (canθ-lift-n sigs n (suc k) p θ)
... | rec | rec2
 =  begin
      Canθ (just x ∷ sigs) (n + k) p θ ≡⟨ c ⟩
      Canθ sigs (n + (suc k)) p θ2 ≡⟨ rec ⟩
      Canθ (add-n-nothings n sigs) (suc k) p θ2 ≡⟨ (sym a) ⟩
       Canθ (add-n-nothings n (just x ∷ sigs)) k p θ ∎
  where θ2 = (θ ← [ ((n + k) ₛ) ↦ m ])

{-
     rewrite sym (+-identityʳ n)
           | canθ-lift-n sigs n 0 p θ

-}


visit-lift-sig : ∀{a}{A : Set a}{sigs : SigMap.Map Signal.Status}
               → ((n : Signal) → (SigMap.∈Dom n sigs) → A)
               → (∃[ n ] (n ∈ SigMap.keys sigs) → A)
visit-lift-sig {sigs = sigs} f
  = (Prod.uncurry f) ∘ (Prod.map Signal.wrap (SigMap.in-inject sigs))

add-nothings-remove-is-set : ∀ n x sigs → 
  (add-n-nothings n (just x ∷ sigs)) ≡ (SigMap.union (add-n-nothings (suc n) sigs) SigMap.[ n ₛ ↦ x ])
add-nothings-remove-is-set zero x sigs
  rewrite SigMap.union-comm (nothing ∷ sigs) SigMap.[ 0 ₛ ↦ x ] $ (λ { .0 x∈1 (here refl) → 0∈S x∈1 ; z x∈1 (there ())})
   = refl
add-nothings-remove-is-set (suc n) x sigs
   = cong (nothing ∷_) $ add-nothings-remove-is-set n x sigs

keys+∈-get-length : ∀ n sigs → (x : Signal.Status)
  → (suc (List.length (SigMap.keys+∈ (add-n-nothings (suc n) sigs))))
     ≡
    (List.length (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs))))
keys+∈-get-length zero sigs x
  rewrite sym $ length-map (Prod.map id there) $ OLST.Dom'+∈-help $ map suc (Dom' sigs) = refl
keys+∈-get-length (suc n) sigs x
  rewrite sym $ OLST.Dom'+∈-help-len suc $ map suc $ OLST.Dom' (add-n-nothings n sigs)
        | sym $ OLST.Dom'+∈-help-len suc $ map suc $ OLST.Dom' (add-n-nothings n (just x ∷ sigs))
        | sym $ OLST.Dom'+∈-help-len suc $ OLST.Dom' (add-n-nothings n (just x ∷ sigs))
  = keys+∈-get-length n sigs x

keys-nothings-off-by-one : ∀ n sigs x →
  (SigMap.keys (add-n-nothings n (just x ∷ sigs)))
    ≡
  (n ∷ (SigMap.keys (add-n-nothings (suc n) sigs)))
keys-nothings-off-by-one zero sigs x = refl
keys-nothings-off-by-one (suc n) sigs x
  rewrite keys-nothings-off-by-one n sigs x
  = refl 


add-n-nothings-++ : ∀ n sig → (add-n-nothings n sig) ≡ (List.applyUpTo (const nothing) n)  ++ sig
add-n-nothings-++ zero sig = refl
add-n-nothings-++ (suc n) sig = cong (nothing ∷_) $ add-n-nothings-++ n sig

keys-tail-equal : ∀ n sigs → (x : Signal.Status)
                    → SigMap.keys (add-n-nothings n (just x ∷ sigs))
                      ≡ 
                      (n ∷ SigMap.keys (add-n-nothings (suc n) sigs))
keys-tail-equal zero sigs x = refl
keys-tail-equal (suc n) sigs x = cong (map suc) $ keys-tail-equal n sigs x


keys+∈-tail-equal : ∀ n sigs → (x : Signal.Status)
                    → (map proj₁ $ SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs)))
                      ≡ 
                      (n ∷ (map proj₁ $ SigMap.keys+∈ (add-n-nothings (suc n) sigs)))
keys+∈-tail-equal n sigs x
   rewrite sym $ FMPropSig.proj₁∈-unchanged (add-n-nothings (suc n) sigs)
         | sym $ FMPropSig.proj₁∈-unchanged (add-n-nothings n (just x ∷ sigs))
   = keys-tail-equal n sigs x

keys+∈-tail-equal-++ : ∀ n sigs → (x : Signal.Status)
                    → (map proj₁ $ SigMap.keys+∈ (List.applyUpTo (const nothing) n ++ just x ∷ sigs))
                      ≡ 
                      (n ∷ (map proj₁ $ SigMap.keys+∈ (List.applyUpTo (const nothing) n ++ (nothing ∷ sigs))))
keys+∈-tail-equal-++ n sigs x
  rewrite sym $ add-n-nothings-++ n (nothing ∷ sigs)
        | sym $ add-n-nothings-++ n (just x ∷ sigs)
        | add-nothing-add n sigs
  = keys+∈-tail-equal n sigs x


subst-id : ∀{a}{A : Set a}{x : A} → ∀ eq → (subst id eq x) ≡ x
subst-id refl = refl



keys+∈-keys-≡ : ∀ n sigs → (x : Signal.Status) → ∀ off
 → (sl1 : Sublist (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs))) (suc off))
 → (sl2 : Sublist (SigMap.keys+∈ (add-n-nothings (suc n) sigs)) (suc off))
 → proj₁ (get sl1) ≡ proj₁ (get sl2)
keys+∈-keys-≡ n sigs x off sl1 sl2
  rewrite sym $ add-nothing-add n sigs
        | add-n-nothings-++ n (nothing ∷ sigs)
        | add-n-nothings-++ n (just x ∷ sigs)
        | SLProp.map-get proj₁ sl1
        | SLProp.map-get proj₁ sl2
        = begin get (SL.map proj₁ sl1) ≡⟨ proj₂ sl1′ ⟩
                get (proj₁ sl1′) ≡⟨ SLProp.++-get-≡ List.[ n ] off (proj₁ sl1′) (proj₁ sl2′) ⟩
                get (proj₁ sl2′) ≡⟨ sym $ proj₂ sl2′ ⟩
                get (SL.map proj₁ sl2) ∎
       where
          l′ = (map proj₁ $ SigMap.keys+∈ (List.applyUpTo (const nothing) n ++ nothing ∷ sigs))
          sl1′ : Σ[ sl1′ ∈  (Sublist (n ∷ l′) (suc off)) ] get (SL.map proj₁ sl1) ≡ get sl1′
          sl1′ rewrite sym $ keys+∈-tail-equal-++ n sigs x
                     | sym $ add-n-nothings-++ n (just x ∷ sigs)
              = (SL.map proj₁ sl1) , refl
          sl2′ : Σ[ sl2′ ∈ (Sublist l′ (suc off)) ] (get (SL.map proj₁ sl2) ≡ get sl2′) 
          sl2′ rewrite sym $ keys+∈-tail-equal-++ n (nothing ∷ sigs) x
                     | sym $ add-n-nothings-++ n (nothing ∷ sigs)
                     | add-nothing-add n sigs
               = (SL.map proj₁ sl2) , refl

∈Dom-nothing-contradition : ∀ n sigs → (x : Signal.Status) → ∀ off
                            → (sl : Sublist (SigMap.keys+∈ (add-n-nothings (suc n) sigs)) (suc off))
                            → (proj₁ (get sl)) ∈ (SigMap.keys SigMap.[ n ₛ ↦ x ])
                            → ⊥
∈Dom-nothing-contradition n sigs x off sl = {!!}


keys+∈-get-≡ : ∀ n sigs → (x : Signal.Status) → ∀ off
 → (sl1 : Sublist (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs))) (suc off))
 → (sl2 : Sublist (SigMap.keys+∈ (add-n-nothings (suc n) sigs)) (suc off))
 →  SigMap.lookup{k = Signal.wrap $ proj₁ $ get sl1} (add-n-nothings n (just x ∷ sigs)) (proj₂ $ get sl1)
      ≡
    SigMap.lookup{k = Signal.wrap $ proj₁ $ get sl2} (add-n-nothings (suc n) sigs) (proj₂ $ get sl2)
keys+∈-get-≡ n sigs x off sl1 sl2
  with (keys+∈-keys-≡ n sigs x off sl1 sl2)
... | key-eq  rewrite add-nothings-remove-is-set n x sigs
   =  begin
        SigMap.lookup{k = Signal.wrap $ proj₁ $ get sl1} (SigMap.union e1 e2) (proj₂ $ get sl1)
        ≡⟨ step1 ⟩
        SigMap.lookup{k = Signal.wrap $ proj₁ $ get sl1} e1 (subst (_∈ _) (sym key-eq) (proj₂ $ get sl2))
        ≅⟨ heq ⟩
        SigMap.lookup{k = Signal.wrap $ proj₁ $ get sl2} e1 (proj₂ $ get sl2) ∎
   where
     e1 = (add-n-nothings (suc n) sigs)
     e2 = SigMap.[ n ₛ ↦ x ]
     heq : SigMap.lookup{k = Signal.wrap $ proj₁ $ get sl1} e1 (subst (_∈ _) (sym key-eq) (proj₂ $ get sl2))
            ≅
           SigMap.lookup{k = Signal.wrap $ proj₁ $ get sl2} e1 (proj₂ $ get sl2)
     f : (x : ℕ) → x ∈ (SigMap.keys e1) → Set
     f a b =
             SigMap.lookup{k = Signal.wrap $ a} e1 b
              ≅
             SigMap.lookup{k = Signal.wrap $ proj₁ $ get sl2} e1 (proj₂ $ get sl2)
     heq = Het.cong₂
           (λ a b → (SigMap.lookup{k = Signal.wrap $ a} e1 b))
           (≡-to-≅ key-eq)
           (Het.≡-subst-removable (_∈ _) (sym key-eq) (proj₂ $ get sl2))
            
     step1 = (sym
      $ SigMap.U-∉-irr-get-help-m{Signal.Status}{(add-n-nothings (suc n) sigs)}{SigMap.[ n ₛ ↦ x ]}{Signal.wrap $ proj₁ $ get sl1}
        (subst (_∈ _) (sym key-eq) (proj₂ $ get sl2))
        (subst (λ y → y ∈ _ → ⊥) (sym key-eq) (∈Dom-nothing-contradition n sigs x off sl2))
        (proj₂ $ get sl1))

-- SigMap.U-∉-irr-get-help-m{m = (add-n-nothings (suc n) sigs)}{m' = SigMap.[ n ₛ ↦ x ]}  (proj₂ $ get sl2) ? ?
-- SigMap.[ n ₛ ↦ x ]

-- add-nothings-remove-is-set n x sigs

--

--add-nothings-remove-is-set n x sigs

-- keys+∈-keys-≡ n sigs x off sl1 sl2

canθ-visit-first-swap-inner : ∀ n sigs p θ → (x : Signal.Status) → ∀ off
 → (sl1 : Sublist (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs))) off)
 → (sl2 : Sublist (SigMap.keys+∈ (add-n-nothings (suc n) sigs)) off)
 →  (SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) θ sl1
      ≡
     SL.visit (visit-lift-sig{sigs = (add-n-nothings (suc n) sigs)} (Canθ-lookup (add-n-nothings (suc n) sigs))) (Can p) θ sl2)
canθ-visit-first-swap-inner n sigs p θ x off sl1 sl2 = {!!}


canθ-visit-first-swap : ∀ n sigs p θ x →
 ∃[ stat ]
 (SigMap.key-visit (add-n-nothings n (just x ∷ sigs)) (Canθ-lookup (add-n-nothings n (just x ∷ sigs))) (Can p) θ
  ≡
  SigMap.key-visit (add-n-nothings (suc n) sigs) (Canθ-lookup (add-n-nothings (suc n) sigs)) (Can p) (θ ← [ n ₛ ↦ stat ]))
canθ-visit-first-swap n sigs p θ x
   with SL.sublist (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs))) | (SigMap.keys+∈ (add-n-nothings (suc n) sigs))
... | a | b = {!!}


      
canθ-visit-correct-start-higher :
    ∀ sigs θ p n → Canθ sigs n p θ ≡ SigMap.key-visit (add-n-nothings n sigs) (Canθ-lookup (add-n-nothings n sigs)) (Can p) θ
canθ-visit-correct-start-higher [] θ p n
  rewrite add-nothing-on-empty∈ n = refl
canθ-visit-correct-start-higher (nothing ∷ sigs) θ p n
  rewrite add-nothing-add n sigs = canθ-visit-correct-start-higher sigs θ p (suc n)
canθ-visit-correct-start-higher (just x ∷ sigs) θ p n
     rewrite sym (+-identityʳ n)
     with canθ-first-swap n 0 sigs p θ x
... | (stat , eqa , eqb) = {!eqb!}

Canθₛ⊆Canₛ : ∀ θ θu p S S′′ →
  (Signal.unwrap S) ∈ Canθₛ (Env.sig θ) S′′ p θu →
  (Signal.unwrap S) ∈ Canₛ p (θ ← θu)
Canθₛ⊆Canₛ (Θ [] a b) θu p S S′′ ∈ rewrite can-shr-var-irr p  θu ((Θ [] a b) ← θu)  refl = ∈
Canθₛ⊆Canₛ (Θ (nothing ∷ sg) a b) θu p S S′′ ∈
   = {!(Canθₛ⊆Canₛ (Θ sg a b) θu p S (suc S′′) ∈)!}
Canθₛ⊆Canₛ (Θ (just x ∷ sg) _ _) θu p S S′′ ∈ = {!!}

Canθₛ⊆Canₛ-[]env-negative : ∀ θ p S →
  (Signal.unwrap S) ∉ Canₛ p θ →
  (Signal.unwrap S) ∉ Canθₛ (Env.sig θ) 0 p Env.[]env
Canθₛ⊆Canₛ-[]env-negative θ p S ∉f ∈f
   =   ∉f $ subst (λ x → ((Signal.unwrap S) ∈ Canₛ p x)) (Env.←-comm θ Env.[]env ((λ x x₁ ()) , (λ x x₁ ()) , (λ x x₁ ()))) (Canθₛ⊆Canₛ θ Env.[]env p S 0 ∈f) 
