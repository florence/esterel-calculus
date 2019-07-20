module Esterel.Lang.CanFunction.CanThetaVisit where

{- 

This moduel defines Canθ-visit, a variant of Canθ which
works by induction on the Domain of θ. (with the usual _ₛ, _ₖ, and _ₛₕ variantes)

It also defines Canθ-visit≡Canθ, which proves that Canθ-visit is the same as CanΘ

-}

open import utility
  renaming (_U̬_ to _∪_ ; _|̌_ to _-_)
  hiding (_⊆_)
open import utility.HeterogeneousEquality

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
open import Esterel.Variable.Signal.Ordering as SO
 using (_⊑_)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)
open import Data.OrderedListMap(Signal)(Signal.unwrap)(Signal.Status) as OLST
open import Data.OrderedListMap.Properties(Signal)(Signal.unwrap)(Signal.Status) as OLSTP
open import Data.Sublist as SL
  using (Sublist ; visit ; get ; elem ; empty)
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
open import Data.Maybe as Maybe
  using (Maybe ; maybe ; just ; nothing)
open import Data.Nat as Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_)
open import Data.Nat.Properties as NatP
  using (+-suc ; +-identityʳ)
open import Data.Product as Prod
  using (Σ ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_ ; ∃-syntax ; Σ-syntax)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; id ; _∋_ ; _$_ ; _|>_ ; const ; flip; _⟨_⟩_)
open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality as Prop
  using (_≡_ ; refl ; trans ; sym ; cong ; subst ; subst₂ ; inspect ; [_] ; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality as Het
  using (_≅_ ; ≅-to-≡ ; ≡-to-≅ ; ≅-to-subst-≡ ; ≅-to-type-≡)
  renaming (refl to hrefl ; cong to hcong ; sym to hsym)
open import Relation.Nullary.Negation
  using (contradiction)
open import Data.Fin as Fin
  using ()
open import Relation.Unary
  using (_⊆′_)

open ≡-Reasoning

SubDomain : (sig : SigMap.Map Signal.Status) → ∀ off → Set
SubDomain sig off = Sublist (SigMap.keys+∈ sig) off

subdomain : (sig : SigMap.Map Signal.Status)
  → SubDomain sig (List.length (SigMap.keys+∈ sig))
subdomain = SL.sublist ∘ SigMap.keys+∈

subdomain-sig : ∀{off} sigs
   → SubDomain sigs (suc off)
   → Signal
subdomain-sig _ sl = (proj₁ (get sl)) ₛ

subdomain-∈ : ∀{off} sigs
   → (sl : SubDomain sigs (suc off))
   → (SigMap.∈Dom (subdomain-sig sigs sl) sigs)
subdomain-∈ _ = proj₂ ∘ get

subdomain-lookup : ∀{off} sigs
   → SubDomain sigs (suc off)
   → Signal.Status
subdomain-lookup sigs sl = SigMap.lookup{k = subdomain-sig sigs sl} sigs $ proj₂ (get sl)

CanResult = SigSet.ST × CodeSet.ST × ShrSet.ST

Canθ-lookup : ∀ sigs → (S : Signal) →  (S∈ : SigMap.∈Dom{Signal.Status} S sigs) → Env → (Env → CanResult) → CanResult
Canθ-lookup sigs S S∈ θ visit with SigMap.lookup{k = S} sigs S∈
... | Signal.present = visit $ θ ← [S]-env-present S
... | Signal.absent = visit $ θ ← [S]-env-absent S
... | Signal.unknown
  with any (Nat._≟_ (Signal.unwrap S)) $ proj₁ (visit (θ ← [S]-env S))
... | yes _ = visit $ θ ← [S]-env S
... | no _ = visit $ θ ← [S]-env-absent S

Canθ-visit : Term → SigMap.Map Signal.Status → Env → CanResult
Canθ-visit p sigs θ
  = SigMap.key-visit sigs (Canθ-lookup sigs) (Can p) θ

Canθₛ-visit : Term → SigMap.Map Signal.Status → Env → SigSet.ST
Canθₛ-visit p sigs θ = proj₁ $ Canθ-visit p sigs θ

Canθₖ-visit : Term → SigMap.Map Signal.Status → Env → CodeSet.ST
Canθₖ-visit p sigs θ = proj₁ $ proj₂ $ Canθ-visit p sigs θ

Canθₛₕ-visit : Term → SigMap.Map Signal.Status → Env → ShrSet.ST
Canθₛₕ-visit p sigs θ = proj₂ $ proj₂ $ Canθ-visit p sigs θ


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
                          Canθ sigs (n + suc k) p (θ ← [ (n + k) ₛ ↦ stat ]))
                         ×
                         (x ≡ Signal.present → stat ≡ Signal.present)
                         ×
                         (x ≡ Signal.absent → stat ≡ Signal.absent)
                         ×
                         (x ≡ Signal.unknown
                          → Any ((n + k) ≡_) (Canθₛ sigs (n + suc k) p (θ ← [S]-env ((n + k) ₛ)))
                          → stat ≡ Signal.unknown)
                         ×
                         (x ≡ Signal.unknown
                          → ¬ Any ((n + k) ≡_) (Canθₛ sigs (n + suc k) p (θ ← [S]-env ((n + k) ₛ)))
                          → stat ≡ Signal.absent))
                         
canθ-first-swap zero k sigs p θ Signal.present = Signal.present , refl , refl , (const refl) , (λ ()) , (λ ()) , (λ ())
canθ-first-swap zero k sigs p θ Signal.absent = Signal.absent , refl , refl , (λ ()) , (const refl) , (λ ()) , (λ ())
canθ-first-swap zero k sigs p θ Signal.unknown
  with any (Nat._≟_ k) (Canθₛ sigs (suc k) p (θ ← [S]-env (k ₛ)))
... | yes y = Signal.unknown , refl , refl , (λ ()) , (λ ()) , (const (const refl)) ,  λ _ → contradiction y
... | no ¬y = Signal.absent , refl , refl , (λ ()) , (λ ()) , (λ _ → flip contradiction ¬y) , (const (const refl))
canθ-first-swap (suc n) k sigs p θ x
  with canθ-first-swap n (suc k) sigs p θ x
     | +-suc n k
     | +-suc n (suc k)
... | (m , a , c , q1 , q2 , q3 , q4) | b | d
  rewrite subst (λ n2 → (Canθ (add-n-nothings n (just x ∷ sigs)) (suc k) p θ
                          ≡
                          Canθ (add-n-nothings (suc n) sigs) (suc k) p (θ ← [ n2 ₛ ↦ m ])))
           b a
         | subst₂ (λ n2 n3 → (Canθ (just x ∷ sigs) n2 p θ
                                ≡
                              Canθ sigs n3 p (θ ← [ n2 ₛ ↦ m ])))
           b d c
   =  m , refl , refl , q1 , q2
      , subst₂ (λ r1 r2 → x ≡ Signal.unknown → Any (r1 ≡_) (Canθₛ sigs r2 p (θ ← [S]-env (r1 ₛ))) → m ≡ Signal.unknown)
                b d q3
      , subst₂ (λ r1 r2 → x ≡ Signal.unknown → ¬ Any (r1 ≡_) (Canθₛ sigs r2 p (θ ← [S]-env (r1 ₛ))) → m ≡ Signal.absent)
                b d q4
     

canθ-lift-n : ∀ sigs n k p θ → Canθ sigs (n + k) p θ ≡ Canθ (add-n-nothings n sigs) k p θ
canθ-lift-n [] n k p θ rewrite canθ-n-empty-irr n k p θ = refl
canθ-lift-n (nothing ∷ sigs) n k p θ rewrite add-nothing-add n sigs = canθ-lift-n sigs (suc n) k p θ
canθ-lift-n (just x ∷ sigs) n k p θ
  with canθ-first-swap n k sigs p θ x
     | +-suc n k
... | (m , a , c , _) | b with (canθ-lift-n sigs n (suc k) p (θ ← [ ((n + k) ₛ) ↦ m ])) | (canθ-lift-n sigs n (suc k) p θ)
... | rec | rec2
 =  begin
      Canθ (just x ∷ sigs) (n + k) p θ ≡⟨ c ⟩
      Canθ sigs (n + (suc k)) p θ2 ≡⟨ rec ⟩
      Canθ (add-n-nothings n sigs) (suc k) p θ2 ≡⟨ (sym a) ⟩
       Canθ (add-n-nothings n (just x ∷ sigs)) k p θ ∎
  where θ2 = (θ ← [ ((n + k) ₛ) ↦ m ])

visit-lift-sig : ∀{a}{A : Set a}{sigs : SigMap.Map Signal.Status}
               → ((n : Signal) → (SigMap.∈Dom n sigs) → A)
               → (∃[ n ] (n ∈ SigMap.keys sigs) → A)
visit-lift-sig {sigs = sigs} f
  = (Prod.uncurry f) ∘ (Prod.map Signal.wrap (SigMap.in-inject sigs))

Canθ-visit-rec : ∀{off} → (sigs : SigMap.Map Signal.Status) → Term → Sublist (SigMap.keys+∈ sigs) off → Env → CanResult
Canθ-visit-rec sigs p sl θ = SL.visit (visit-lift-sig{sigs = sigs} (Canθ-lookup sigs)) (Can p) θ sl
   where dom = (SigMap.keys+∈ sigs)

Canθₛ-visit-rec : ∀{off} → (sigs : SigMap.Map Signal.Status) → Term → Sublist (SigMap.keys+∈ sigs) off → Env → SigSet.ST 
Canθₛ-visit-rec sigs p sl θ = proj₁ $ Canθ-visit-rec sigs p sl θ
Canθₖ-visit-rec : ∀{off} → (sigs : SigMap.Map Signal.Status) → Term → Sublist (SigMap.keys+∈ sigs) off → Env → CodeSet.ST 
Canθₖ-visit-rec sigs p sl θ = proj₁ $ proj₂ $ Canθ-visit-rec sigs p sl θ
Canθₛₕ-visit-rec : ∀{off} → (sigs : SigMap.Map Signal.Status) → Term → Sublist (SigMap.keys+∈ sigs) off → Env → ShrSet.ST 
Canθₛₕ-visit-rec sigs p sl θ = proj₂ $ proj₂ $ Canθ-visit-rec sigs p sl θ

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

keys+∈-tail-equalΣ : ∀ n sigs → (x : Signal.Status)
                     → (∃[ inn ] (∃[ tail ] 
                       (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs)) ≡
                         (n , inn) ∷ tail)))
keys+∈-tail-equalΣ zero sigs x = _ , _ , refl
keys+∈-tail-equalΣ (suc n) sigs x with keys+∈-tail-equalΣ n sigs x 
... | inn , rst , eq
    = (OLST.sucin inn)
      , map (Prod.map suc OLST.sucin) rst 
      , ( begin
            Dom'+∈-help (map suc (Dom' (add-n-nothings n (just x ∷ sigs))))
            ≡⟨ suc-isprodsucin (Dom' (add-n-nothings n (just x ∷ sigs))) ⟩
            map (Prod.map suc sucin) (Dom'+∈-help (Dom' (add-n-nothings n (just x ∷ sigs))))
            ≡⟨ cong (map (Prod.map suc sucin)) eq ⟩
            (suc n , sucin inn) ∷ map (Prod.map suc sucin) rst ∎) 

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


single-add-nothings-distinct : (x : Signal.Status)
                               → ∀ n sigs
                               → distinct' (SigMap.keys (add-n-nothings (suc n) sigs)) (SigMap.keys SigMap.[ n ₛ ↦ x ])
single-add-nothings-distinct x n sigs k ∈1 ∈2
  with SigMap.keys-1map (n ₛ) x
... | eq with subst (_ ∈_) eq ∈2
single-add-nothings-distinct x n sigs k ∈1 ∈2 | eq | there ()
single-add-nothings-distinct x zero sigs .0 ∈1 ∈2 | eq | here refl = OLST.0∈S ∈1 
single-add-nothings-distinct x (suc n) sigs .(suc n) ∈1 ∈2 | eq | here refl
   = single-add-nothings-distinct x n sigs n (OLST.sucout ∈1) (OLST.sucout ∈2)

∈Dom-nothing-contradition : ∀ n sigs → (x : Signal.Status) → ∀ off
                            → (sl : Sublist (SigMap.keys+∈ (add-n-nothings (suc n) sigs)) (suc off))
                            → (proj₁ (get sl)) ∈ (SigMap.keys SigMap.[ n ₛ ↦ x ])
                            → ⊥
∈Dom-nothing-contradition n sigs x off sl = single-add-nothings-distinct x n sigs (proj₁ (get sl)) (proj₂ (get sl))


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
     heq = Het.cong₂
           (λ a b → (SigMap.lookup{k = Signal.wrap $ a} e1 b))
           (≡-to-≅ key-eq)
           (Het.≡-subst-removable (_∈ _) (sym key-eq) (proj₂ $ get sl2))
     step1 = (sym
      $ SigMap.U-∉-irr-get-help-m{Signal.Status}{(add-n-nothings (suc n) sigs)}{SigMap.[ n ₛ ↦ x ]}{Signal.wrap $ proj₁ $ get sl1}
        (subst (_∈ _) (sym key-eq) (proj₂ $ get sl2))
        (subst (λ y → y ∈ _ → ⊥) (sym key-eq) (∈Dom-nothing-contradition n sigs x off sl2))
        (proj₂ $ get sl1))

canθ-visit-first-swap-inner : ∀ n sigs p θ → (x : Signal.Status) → ∀ off
 → (sl1 : Sublist (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs))) off)
 → (sl2 : Sublist (SigMap.keys+∈ (add-n-nothings (suc n) sigs)) off)
 →  (SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) θ sl1
      ≡
     SL.visit (visit-lift-sig{sigs = (add-n-nothings (suc n) sigs)} (Canθ-lookup (add-n-nothings (suc n) sigs))) (Can p) θ sl2)
canθ-visit-first-swap-inner n sigs p θ x .0 Sublist.empty Sublist.empty = refl
canθ-visit-first-swap-inner n sigs p θ x .(suc n₁) l1@(Sublist.elem n₁ n<l sl1) l2@(Sublist.elem .n₁ n<l₁ sl2)
  with get l1 | get l2 | inspect get l1 | inspect get l2
... | S1 , S∈1 | S2 , S∈2 | [ refl ] | [ refl ]
  with SigMap.lookup{k = Signal.wrap S1} (add-n-nothings n (just x ∷ sigs)) S∈1
     | SigMap.lookup{k = Signal.wrap S2} (add-n-nothings (suc n) sigs) S∈2 
     | inspect (SigMap.lookup{k = Signal.wrap S1} (add-n-nothings n (just x ∷ sigs))) S∈1
     | inspect (SigMap.lookup{k = Signal.wrap S2} (add-n-nothings (suc n) sigs)) S∈2 
... | a | b | [ eqa ] | [ eqb ]
  with ((a ≡ b) ∋  eq eqa eqb ) 
    where 
     -- typeof shenanigans because we cannot match on eqa and eqb here
     -- matching on them above breaks case dispatching below
     -- and matching on them in the local runs afould of something something module telescopes
     eq : (typeof eqa) → (typeof eqb) → (a ≡ b)
     eq refl refl = (keys+∈-get-≡ n sigs x n₁ l1 l2)
canθ-visit-first-swap-inner n sigs p θ x .(suc n₁) l1@(Sublist.elem n₁ n<l sl1) l2@(Sublist.elem .n₁ n<l₁ sl2)
                           | S1 , S∈1 | S2 , S∈2 | [ eq1 ] | [ eq2 ]
                           | Signal.present | .Signal.present | [ eqa ] | [ eqb ]
                           | refl
  
  =  subst
      (λ r →
       SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) (θ ← [S]-env-present (S1 ₛ)) sl1
        ≡
       SL.visit (visit-lift-sig{sigs = (add-n-nothings (suc n) sigs)} (Canθ-lookup (add-n-nothings (suc n) sigs))) (Can p) (θ ← [S]-env-present (r ₛ)) sl2)
      (keys+∈-keys-≡ n sigs x n₁ l1 l2)
      (canθ-visit-first-swap-inner n sigs p (θ ← [S]-env-present (S1 ₛ)) x n₁ sl1 sl2)
   

canθ-visit-first-swap-inner n sigs p θ x .(suc n₁) l1@(Sublist.elem n₁ n<l sl1) l2@(Sublist.elem .n₁ n<l₁ sl2)
                          | S1 , S∈1 | S2 , S∈2 | [ eq1 ] | [ eq2 ]
                          | Signal.absent | .Signal.absent | [ eqa ] | [ eqb ]
                          | refl
  =  subst
      (λ r →
       SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) (θ ← [S]-env-absent (S1 ₛ)) sl1
        ≡
       SL.visit (visit-lift-sig{sigs = (add-n-nothings (suc n) sigs)} (Canθ-lookup (add-n-nothings (suc n) sigs))) (Can p) (θ ← [S]-env-absent (r ₛ)) sl2)
      (keys+∈-keys-≡ n sigs x n₁ l1 l2)
      (canθ-visit-first-swap-inner n sigs p (θ ← [S]-env-absent (S1 ₛ)) x n₁ sl1 sl2)
canθ-visit-first-swap-inner n sigs p θ x .(suc n₁) (Sublist.elem n₁ n<l sl1) (Sublist.elem .n₁ n<l₁ sl2)
                          | S1 , S∈1 | S2 , S∈2 | [ eq1 ] | [ eq2 ]
                          | Signal.unknown | .Signal.unknown | [ eqa ] | [ eqb ]
                          | refl
  with any (Nat._≟_ S1) $ proj₁ (visit1 (θ ← [S]-env (Signal.wrap S1)))
     | any (Nat._≟_ S2) $ proj₁ (visit2 (θ ← [S]-env (Signal.wrap S2)))
     | inspect (any (Nat._≟_ S1)) $ proj₁ (visit1 (θ ← [S]-env (Signal.wrap S1)))
     | inspect (any (Nat._≟_ S2)) $ proj₁ (visit2 (θ ← [S]-env (Signal.wrap S2)))
   where
     visit1 = (λ a → SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) a sl1)
     visit2 = (λ a → SL.visit (visit-lift-sig{sigs = (add-n-nothings (suc n) sigs)} (Canθ-lookup (add-n-nothings (suc n) sigs))) (Can p) a sl2)


... | a | b | [ c ] | [ d ] with ((⌊ a ⌋ ≡ ⌊ b ⌋) ∋ eq c d)
  where
    visit1 = (λ a → SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) a sl1)
    visit2 = (λ a → SL.visit (visit-lift-sig{sigs = (add-n-nothings (suc n) sigs)} (Canθ-lookup (add-n-nothings (suc n) sigs))) (Can p) a sl2)
    l1 = (Sublist.elem n₁ n<l sl1)
    l2 = (Sublist.elem n₁ n<l₁ sl2)
    keyeq = (keys+∈-keys-≡ n sigs x n₁ l1 l2)
    eq : (typeof c) → (typeof d) → (⌊ a ⌋ ≡ ⌊ b ⌋)
    eq refl refl =  begin
                     ⌊ a ⌋ ≡⟨⟩
                     ⌊ (any (_≟_ S1) (proj₁ (visit1 (θ ← [S]-env (Signal.wrap S1))))) ⌋
                     ≡⟨  cong (λ key → ⌊ any (_≟_ key) (proj₁ (visit1 (θ ← [S]-env (Signal.wrap S1)))) ⌋) keyeq  ⟩ 
                     ⌊ (any (_≟_ S2) (proj₁ (visit1 (θ ← [S]-env (Signal.wrap S1))))) ⌋
                     ≡⟨ cong (λ visit → ⌊ (any (_≟_ S2) (proj₁ visit)) ⌋)
                            ((canθ-visit-first-swap-inner n sigs p (θ ← [S]-env (S1 ₛ)) x n₁ sl1 sl2))  ⟩
                     ⌊ (any (_≟_ S2) (proj₁ (visit2 (θ ← [S]-env (Signal.wrap S1))))) ⌋
                     ≡⟨ cong (λ key → ⌊ (any (_≟_ S2) (proj₁ (visit2 (θ ← [S]-env (Signal.wrap key))))) ⌋) keyeq ⟩
                     ⌊ (any (_≟_ S2) (proj₁ (visit2 (θ ← [S]-env (Signal.wrap S2))))) ⌋
                     ≡⟨⟩ ⌊ b ⌋ ∎
canθ-visit-first-swap-inner n sigs p θ x .(suc n₁) (Sublist.elem n₁ n<l sl1) (Sublist.elem .n₁ n<l₁ sl2)
                          | S1 , _ | S2 , _ | [ refl ] |  [ refl ]
                          | Signal.unknown | .Signal.unknown | [ eqa ] | [ eqb ] | refl
                          | yes p₁ | yes p₂ | [ c ] | [ d ] | refl
    = subst
      (λ r →
       SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) (θ ← [S]-env (S1 ₛ)) sl1
        ≡
       SL.visit (visit-lift-sig{sigs = (add-n-nothings (suc n) sigs)} (Canθ-lookup (add-n-nothings (suc n) sigs))) (Can p) (θ ← [S]-env (r ₛ)) sl2)
      (keys+∈-keys-≡ n sigs x n₁ (Sublist.elem n₁ n<l sl1) (Sublist.elem n₁ n<l₁ sl2))
      (canθ-visit-first-swap-inner n sigs p (θ ← [S]-env (S1 ₛ)) x n₁ sl1 sl2)
canθ-visit-first-swap-inner n sigs p θ x .(suc n₁) (Sublist.elem n₁ n<l sl1) (Sublist.elem .n₁ n<l₁ sl2)
                          | S1 , _ | S2 , _ | [ refl ] |  [ refl ]
                          | Signal.unknown | .Signal.unknown | [ eqa ] | [ eqb ] | refl
                          | no ¬p | no ¬p₁ | [ c ] | [ d ] | refl
  = subst
      (λ r →
       SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) (θ ← [S]-env-absent (S1 ₛ)) sl1
        ≡
       SL.visit (visit-lift-sig{sigs = (add-n-nothings (suc n) sigs)} (Canθ-lookup (add-n-nothings (suc n) sigs))) (Can p) (θ ← [S]-env-absent (r ₛ)) sl2)
      (keys+∈-keys-≡ n sigs x n₁ (Sublist.elem n₁ n<l sl1) (Sublist.elem n₁ n<l₁ sl2))
      (canθ-visit-first-swap-inner n sigs p (θ ← [S]-env-absent (S1 ₛ)) x n₁ sl1 sl2)
canθ-visit-first-swap-inner n sigs p θ x .(suc n₁) (Sublist.elem n₁ n<l sl1) (Sublist.elem .n₁ n<l₁ sl2)
                          | _ | _ | _ | _
                          | Signal.unknown | .Signal.unknown | [ eqa ] | [ eqb ] | refl
                          | yes p₁ | no ¬p | [ c ] | [ d ] | ()
canθ-visit-first-swap-inner n sigs p θ x .(suc n₁) (Sublist.elem n₁ n<l sl1) (Sublist.elem .n₁ n<l₁ sl2)
                          | _ | _ | _ | _
                          | Signal.unknown | .Signal.unknown | [ eqa ] | [ eqb ] | refl
                          | no ¬p | yes p₁ | [ c ] | [ d ] | ()


lookup-n-is-x : ∀ n sigs x
  → (n∈ : n ∈ SigMap.keys (add-n-nothings n (just x ∷ sigs)))
  → x ≡ (SigMap.lookup{k = Signal.wrap $ n} (add-n-nothings n (just x ∷ sigs)) n∈)
lookup-n-is-x zero sigs x n∈ = refl
lookup-n-is-x (suc n) sigs x n∈ = lookup-n-is-x n sigs x (n∈S{l = (add-n-nothings n (just x ∷ sigs))} n∈)

mutual
  canθ-visit-first-swap : ∀ n sigs p θ x →
   ∃[ stat ]
   ((SigMap.key-visit (add-n-nothings n (just x ∷ sigs)) (Canθ-lookup (add-n-nothings n (just x ∷ sigs))) (Can p) θ
     ≡
     SigMap.key-visit (add-n-nothings (suc n) sigs) (Canθ-lookup (add-n-nothings (suc n) sigs)) (Can p) (θ ← [ n ₛ ↦ stat ]))
    ×
    stat ≡ (proj₁ $ canθ-first-swap n 0 sigs p θ x))
  canθ-visit-first-swap n sigs p θ x
     with (canθ-first-swap n 0 sigs p θ x)
        | List.length (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs)))
        | SL.sublist (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs)))
        | SL.sublist (SigMap.keys+∈ (add-n-nothings (suc n) sigs))
        | (sym $ keys+∈-get-length n sigs x)
  ... | (_ , _ , _  , x≡p , x≡a , x≡u^in , x≡u^¬in)  | suc _ | l1@(Sublist.elem _ n<l sl1) | sl2 | refl
    
       -- we must show that (proj₁ (get l1)) ≡ n
    with keys+∈-tail-equalΣ n sigs x
  ... | y
     with (let 
              l1' = SL.sublist (SigMap.keys+∈ (add-n-nothings n (just x ∷ sigs)))
              l2  = (SL.sublist ((n , proj₁ y) ∷ (proj₁ (proj₂ y))))
              leneq = (keys+∈-get-length n sigs x)
              eq1 = proj₂ $ proj₂ y
              in (begin (proj₁ (get l1))
                  ≅⟨ cong₃{A = ℕ}{B = (const (List (Σ ℕ (λ n → n ∈ _))))  }{C = λ n l → Sublist l (suc n)}
                      (λ _ _ sl → proj₁ $ get sl)
                      (≡-to-≅ $ NatP.suc-injective $ trans leneq $ cong List.length eq1)
                      (≡-to-≅ $ eq1)
                      (Het.trans
                       (SLProp.equal-list-equal-sublist-het l1 l1' hrefl hrefl leneq)
                       (Het.cong SL.sublist $ ≡-to-≅ $ eq1)) ⟩
                  (proj₁ (get l2))
                  ≡⟨ cong proj₁ $ SLProp.get-first-is-first-from-head (n , proj₁ y) (proj₁ (proj₂ y)) ⟩
                  n ∎))
  ... | eq
    with SigMap.lookup{k = Signal.wrap $ proj₁ $ get l1} (add-n-nothings n (just x ∷ sigs)) $ proj₂ $ get l1
       | (let
             n∈ : Σ (n ∈ SigMap.keys (add-n-nothings n (just x ∷ sigs))) (_≅ (proj₂ $ get l1))
             n∈ = subst (_∈ _) eq (proj₂ $ get l1)
                  , Het.≡-subst-removable (_∈ _) eq (proj₂ $ get l1)
           in
            begin
            x ≡⟨ lookup-n-is-x n sigs x (proj₁ n∈)  ⟩
            (SigMap.lookup{k = Signal.wrap $ n} (add-n-nothings n (just x ∷ sigs)) (proj₁ n∈))
            ≅⟨ Het.cong₂ (λ n1 n∈ → (SigMap.lookup{k = Signal.wrap $ n1} (add-n-nothings n (just x ∷ sigs)) n∈))
                          (≡-to-≅ (sym eq))
                          (proj₂ n∈)   ⟩
            (SigMap.lookup{k = Signal.wrap $ proj₁ $ get l1} (add-n-nothings n (just x ∷ sigs)) $ proj₂ $ get l1) ∎)
  ... | Signal.present | prf rewrite eq
    = Signal.present , (canθ-visit-first-swap-inner n sigs p (θ ← [S]-env-present (n ₛ))  x _ sl1 sl2) , (sym $ x≡p prf)
  ... | Signal.absent | prf rewrite eq
    = Signal.absent , (canθ-visit-first-swap-inner n sigs p (θ ← [S]-env-absent (n ₛ))  x _ sl1 sl2) , (sym $ x≡a prf)
  ... | Signal.unknown  | prf 
    with any (Nat._≟_ (proj₁ (get l1))) $ proj₁ (revisit (θ ← [S]-env (Signal.wrap (proj₁ (get l1)))))
      where revisit = (λ θ → SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) θ sl1)
  ... | yes ∈visit rewrite eq
     = Signal.unknown
       , inner-eq
       , (sym $ x≡u^in prf
              $  (subst
                 id
                 (begin
                  (as (SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) θ2 sl1))
                  ≡⟨ cong as inner-eq ⟩
                  (as (SL.visit (visit-lift-sig{sigs = sig-suc} (Canθ-lookup sig-suc)) (Can p) θ2 sl2 ))
                  ≡⟨ cong (as ∘ (visit (visit-lift-sig{sigs = sig-suc} (Canθ-lookup sig-suc)) (Can p) θ2))
                     $ SLProp.sublist-irrelevant sl2 sl2' ⟩
                  (as (SigMap.key-visit sig-suc (Canθ-lookup sig-suc) (Can p) θ2))
                  ≡⟨ cong as $ sym $ rec ⟩
                  Any (_≡_ n) (proj₁ (Canθ sigs (suc n) p θ2))
                  ≡⟨ Prop.cong₂ final-step (sym $ +-identityʳ n) (NatP.+-comm 1 n) ⟩
                  final-step (n + 0) (n + 1)
                  ∎)
                  ∈visit) )
       where
         final-step = (λ n0 n1 → (Any (n0 ≡_) (Canθₛ sigs n1 p (θ ← [S]-env (n0 ₛ)))))
         sig-suc = (add-n-nothings (suc n) sigs)
         sl2' = (SL.sublist (SigMap.keys+∈ sig-suc))
         as = Any (n ≡_) ∘ proj₁
         θ2 = (θ ← [S]-env (n ₛ))
         inner-eq = (canθ-visit-first-swap-inner n sigs p θ2  x _ sl1 sl2)
         rec = canθ-visit-correct-start-higher sigs θ2 p (suc n)
  ... | no ∉visit rewrite eq
    = Signal.absent
      , (canθ-visit-first-swap-inner n sigs p (θ ← [S]-env-absent (n ₛ))  x _ sl1 sl2)
      , (sym $ x≡u^¬in prf
              $  (subst
                 id
                 (begin
                  (as (SL.visit (visit-lift-sig{sigs = (add-n-nothings n (just x ∷ sigs))} (Canθ-lookup (add-n-nothings n (just x ∷ sigs)))) (Can p) θ2 sl1))
                  ≡⟨ cong as inner-eq ⟩
                  (as (SL.visit (visit-lift-sig{sigs = sig-suc} (Canθ-lookup sig-suc)) (Can p) θ2 sl2 ))
                  ≡⟨ cong (as ∘ (visit (visit-lift-sig{sigs = sig-suc} (Canθ-lookup sig-suc)) (Can p) θ2))
                     $ SLProp.sublist-irrelevant sl2 sl2' ⟩
                  (as (SigMap.key-visit sig-suc (Canθ-lookup sig-suc) (Can p) θ2))
                  ≡⟨ cong as $ sym $ rec ⟩
                  (¬ Any (_≡_ n) (proj₁ (Canθ sigs (suc n) p θ2)))
                  ≡⟨ Prop.cong₂ final-step (sym $ +-identityʳ n) (NatP.+-comm 1 n) ⟩
                  final-step (n + 0) (n + 1)
                  ∎)
                  ∉visit) )
       where
         final-step = (λ n0 n1 → ¬ (Any (n0 ≡_) (Canθₛ sigs n1 p (θ ← [S]-env (n0 ₛ)))))
         sig-suc = (add-n-nothings (suc n) sigs)
         sl2' = (SL.sublist (SigMap.keys+∈ sig-suc))
         as = ¬_ ∘ (Any (n ≡_)) ∘ proj₁
         θ2 = (θ ← [S]-env (n ₛ))
         inner-eq = (canθ-visit-first-swap-inner n sigs p θ2  x _ sl1 sl2)
         rec = canθ-visit-correct-start-higher sigs θ2 p (suc n) 
          
  canθ-visit-correct-start-higher :
      ∀ sigs θ p n → Canθ sigs n p θ ≡ SigMap.key-visit (add-n-nothings n sigs) (Canθ-lookup (add-n-nothings n sigs)) (Can p) θ
  canθ-visit-correct-start-higher [] θ p n
    rewrite add-nothing-on-empty∈ n = refl
  canθ-visit-correct-start-higher (nothing ∷ sigs) θ p n
    rewrite add-nothing-add n sigs = canθ-visit-correct-start-higher sigs θ p (suc n)
  canθ-visit-correct-start-higher (just x ∷ sigs) θ p n
       rewrite sym (+-identityʳ n)
       with canθ-first-swap n 0 sigs p θ x
          | canθ-visit-first-swap n sigs p θ x
  ... | (stat , eqa , eqb , _) | (stat1 , eqc , refl)
     = begin
        Canθ (just x ∷ sigs) (n + 0) p θ
        ≡⟨ eqb ⟩
        Canθ sigs (n + 1) p (θ ← [ (n + 0) ₛ ↦ stat ])
        ≡⟨ cong (λ n1 → Canθ sigs (n + 1) p (θ ← [ n1 ₛ ↦ stat ])) (+-identityʳ n) ⟩
        Canθ sigs (n + 1) p (θ ← [ n ₛ ↦ stat ])
        ≡⟨  cong (λ n1 → Canθ sigs n1 p (θ ← [ n ₛ ↦ stat ])) (NatP.+-comm n 1)  ⟩
        Canθ sigs (suc n) p (θ ← [ n ₛ ↦ stat ])
        ≡⟨  canθ-visit-correct-start-higher sigs (θ ← [ n ₛ ↦ stat ]) p (suc n)  ⟩ 
        SigMap.key-visit (add-n-nothings (suc n) sigs) (Canθ-lookup (add-n-nothings (suc n) sigs)) (Can p) (θ ← [ n ₛ ↦ stat ])
        ≡⟨ sym eqc ⟩
        SigMap.key-visit (add-n-nothings n (just x ∷ sigs)) (Canθ-lookup (add-n-nothings n (just x ∷ sigs))) (Can p) θ
        ≡⟨ cong (λ n → SigMap.key-visit (add-n-nothings n (just x ∷ sigs)) (Canθ-lookup (add-n-nothings n (just x ∷ sigs))) (Can p) θ)
                (sym (+-identityʳ n)) ⟩
        SigMap.key-visit (add-n-nothings (n + 0) (just x ∷ sigs)) (Canθ-lookup (add-n-nothings (n + 0) (just x ∷ sigs))) (Can p) θ ∎


Canθ-visit≡Canθ : ∀ sigs θ p → 
                  Canθ-visit p sigs θ ≡ Canθ sigs 0 p θ
Canθ-visit≡Canθ sigs θ p = sym $ canθ-visit-correct-start-higher sigs θ p 0

Canθ-visit-rec-step : ∀{off} sigs θ p
  →  (slo : Sublist (SigMap.keys+∈ sigs) (suc off))
  →  (sli : Sublist (SigMap.keys+∈ sigs) off)
  → ∃[ stat ]
      ((Canθ-visit-rec sigs p slo θ
        ≡
        Canθ-visit-rec sigs p sli (θ ← [S]-env-build ((proj₁ (get slo)) ₛ) stat))
       ×
        (SigMap.lookup{k = ((proj₁ (get slo)) ₛ)} sigs (proj₂ (get slo))  ⊑ stat))
Canθ-visit-rec-step sigs θ p l@(elem n n<l slo) sli
  with SLProp.sublist-irrelevant slo sli
     | SigMap.lookup{k = (proj₁ (get l)) ₛ} sigs (proj₂ (get l))
... | refl | Signal.present  = Signal.present , refl , SO.refl
... | refl | Signal.absent = Signal.absent , refl , SO.refl
... | refl | Signal.unknown
  with any (_≟_  (proj₁ (get l))) (proj₁ (revisit (θ ← ([S]-env-build ((proj₁ (get l)) ₛ) Signal.unknown))))
    where revisit = (λ θ → SL.visit (visit-lift-sig{sigs = sigs} (Canθ-lookup sigs)) (Can p) θ sli)
... | yes _ = Signal.unknown , refl , SO.refl
... | no _ = Signal.absent , refl , SO.uknw


                      

