module utility where

open import Algebra
  using (Monoid)
open import Algebra.Structures
  using (IsMonoid ; IsSemigroup)
open import Data.Empty
open import Function
  using (_∘_ ; _$_ ; _∋_)
open import Relation.Binary
  using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; setoid ; sym ; cong ; subst)
open import Relation.Nullary
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Data.Bool
  using (not)
open import Data.List hiding (map)
open import Data.List.Properties
  using (map-id ; map-compose ; map-cong)
open import Data.List.Any as ListAny
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties using ( ∷↔ ; ++⁻)
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ)
open import Data.Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_ ; _∸_)
open import Data.Nat.Properties.Simple
  using (+-comm)
open import Data.Nat.Properties
  using (n∸n≡0 ; m+n∸n≡m)
open import Data.Product as Prod
  using (_,_ ; _,′_ ; _×_ ; proj₁ ; proj₂ ; ∃)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; id)
import Data.List.Membership.Setoid

++-assoc : ∀{A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc {_} xs ys zs =
  IsSemigroup.assoc (IsMonoid.isSemigroup (Monoid.isMonoid (Data.List.Properties.++-monoid _))) xs _ _



_∈_ : {A : Set} → (x : A) → (xs : List A) → Set
_∈_ {A} x xs = Data.List.Membership.Setoid._∈_ (setoid A) x xs

_∉_ : {A : Set} → (x : A) → (xs : List A) → Set
_∉_ {A} x xs = Data.List.Membership.Setoid._∉_ (setoid A) x xs



map-second : {A B C D : Set} →
  (f : B → D) →
  A × B × C → A × D × C
map-second f = Prod.map id (Prod.map f id)

any-map⁺ : ∀ {A B} {xs : List A} {x} (f : A → B) →
  x ∈ xs → f x ∈ Data.List.map f xs
any-map⁺ f (here refl)  = here refl
any-map⁺ f (there x∈xs) = there (any-map⁺ f x∈xs)

-- the map-mono like the one in Data.List.Any.Membership
-- idk why I can't import that module so I just implement one here
map-mono : ∀ {A B} {ys zs : List A} (f : A → B) →
  (∀ x → x ∈ ys → x ∈ zs) → ∀ fx → fx ∈ Data.List.map f ys → fx ∈ Data.List.map f zs
map-mono {ys = []} f ys⊆zs fx ()
map-mono {ys = y ∷ ys} {zs} f ys⊆zs .(f y) (here refl) =
  any-map⁺ f (ys⊆zs y (here refl))
map-mono {ys = y ∷ ys} {zs} f ys⊆zs fx (there fx∈map-f-ys) =
  map-mono f (λ x z → ys⊆zs x (there z)) fx fx∈map-f-ys

any-map⁺² : ∀ {A B : Set} {xs x fxy} (f : A → List B) →
  x ∈ xs → fxy ∈ f x → fxy ∈ concatMap f xs
any-map⁺² f (here refl)  fxy∈fx = ++ˡ fxy∈fx
any-map⁺² f (there x∈xs) fxy∈fx = ++ʳ (f _) (any-map⁺² f x∈xs fxy∈fx)

map-mono² : ∀ {A B C} {xs xs' : List A} {ys ys' : List B} (f : A → B → C) →
  (∀ u → u ∈ xs → u ∈ xs') →
  (∀ v → v ∈ ys → v ∈ ys') →
  ∀ fuv →
    fuv ∈ concatMap (λ u → Data.List.map (f u) ys)  xs →
    fuv ∈ concatMap (λ u → Data.List.map (f u) ys') xs'
map-mono² {xs = []} {xs'} {ys} {ys'} f xs⊆xs' ys⊆ys' fuv ()
map-mono² {xs = x ∷ xs} {xs'} {ys} {ys'} f xs⊆xs' ys⊆ys' fuv fuv∈[[fuv|ys]|x∷xs]
  with ++⁻ (Data.List.map (f x) ys) fuv∈[[fuv|ys]|x∷xs]
... | inj₂ fuv∈[[fuv|ys]|xs] =
  map-mono² f (λ u → xs⊆xs' u ∘ there) ys⊆ys' fuv fuv∈[[fuv|ys]|xs]
... | inj₁ fuv∈[fxv|ys] =
  any-map⁺² (λ u → Data.List.map (f u) ys')
    (xs⊆xs' x (here refl))
    (map-mono (f x) ys⊆ys' fuv fuv∈[fxv|ys])



module ListSet {A : Set} (_≟_ : Decidable {A = A} _≡_) where
  open import Relation.Nullary.Negation using (¬?)
  ST : Set
  ST = List A


  set-subtract : List A → List A → List A
  set-subtract S T = filter (λ x → ¬? (ListAny.any (_≟_ x) T)) S

  set-remove : List A → A → List A
  set-remove S x = filter (¬? ∘ _≟_ x) S

  set-remove-removed : ∀{S L} → S ∉ set-remove L S
  set-remove-removed {S} {[]} ()
  set-remove-removed {S} {x ∷ L} Sin with S ≟ x | set-remove-removed{S}{L}
  set-remove-removed {S} {x ∷ L} Sin | yes refl | r = r Sin
  set-remove-removed {S} {x ∷ L} (here px) | no ¬p | r = ¬p px
  set-remove-removed {S} {x ∷ L} (there Sin) | no ¬p | r = r Sin

  set-remove-not-eq : ∀{a a' xs} → a ∈ set-remove xs a' → ¬ a' ≡ a
  set-remove-not-eq {a}{a'}{xs} a∈xs-a' with a' ≟ a
  ... | yes refl = ⊥-elim (set-remove-removed{a}{xs} a∈xs-a')
  ... | no ¬refl = ¬refl

  set-remove-mono-∈ : ∀ {xs a} a' → a ∈ set-remove xs a' → a ∈ xs
  set-remove-mono-∈ {[]}       {a} a' ()
  set-remove-mono-∈ {(x ∷ xs)} {a} a' a∈xs-[a'] with a' ≟ x
  set-remove-mono-∈ {(x ∷ xs)} {a} a' a∈xs-[a']
    | yes a'≡x = there (set-remove-mono-∈ a' a∈xs-[a'])
  set-remove-mono-∈ {(x ∷ xs)} {a} a' (here refl)
    | no ¬a'≡x = here refl
  set-remove-mono-∈ {(x ∷ xs)} {a} a' (there a∈xs-[a'])
    | no ¬a'≡x = there (set-remove-mono-∈ a' a∈xs-[a'])

  set-remove-not-removed : ∀ {a' a xs} → ¬ (a' ≡ a) → a ∈ xs → a ∈ set-remove xs a'
  set-remove-not-removed {a'} {a} {.a ∷ xs} a'≢a (here refl)  with a' ≟ a
  ... | yes a'≡a = ⊥-elim (a'≢a a'≡a)
  ... | no ¬a'≡a = here refl
  set-remove-not-removed {a'} {a} {x ∷ xs} a'≢a (there a∈xs) with a' ≟ x
  ... | yes a'≡x = set-remove-not-removed a'≢a a∈xs
  ... | no ¬a'≡x = there (set-remove-not-removed a'≢a a∈xs)

  set-subtract-[] : ∀ xs → set-subtract xs [] ≡ xs
  set-subtract-[] [] = refl
  set-subtract-[] (x ∷ xs) rewrite set-subtract-[] xs = refl

  set-subtract-[a]≡set-remove : ∀ xs a → set-subtract xs (a ∷ []) ≡ set-remove xs a
  set-subtract-[a]≡set-remove [] a = refl
  set-subtract-[a]≡set-remove (x ∷ xs) a
    with x ≟ a | a ≟ x
  ... | yes refl | no  a≢x  = ⊥-elim (a≢x refl)
  ... | no  x≢a  | yes refl = ⊥-elim (x≢a refl)
  ... | yes refl | yes a≡x =  set-subtract-[a]≡set-remove xs x 
  ... | no  x≢a  | no  a≢x  rewrite set-subtract-[a]≡set-remove xs a =  refl 

  set-subtract-merge : ∀ {xs ys z} → z ∈ set-subtract xs ys → (z ∈ xs) × (z ∉ ys)
  set-subtract-merge {[]} ()
  set-subtract-merge {x ∷ xs} {ys} z∈xs-ys with ListAny.any (_≟_ x) ys
  set-subtract-merge {x ∷ xs} {ys} (here refl)     | no x∉ys = here refl ,′ x∉ys
  set-subtract-merge {x ∷ xs} {ys} (there z∈xs-ys) | no x∉ys = there z∈xs , z∉ys
    where z∈xs,z∉ys = set-subtract-merge {xs} {ys} z∈xs-ys
          z∈xs      = proj₁ z∈xs,z∉ys
          z∉ys      = proj₂ z∈xs,z∉ys
  ... | yes x∈ys = there z∈xs , z∉ys
    where z∈xs,z∉ys = set-subtract-merge {xs} {ys} z∈xs-ys
          z∈xs      = proj₁ z∈xs,z∉ys
          z∉ys      = proj₂ z∈xs,z∉ys

  set-subtract-split : ∀ {xs ys z} → z ∈ xs → z ∈ set-subtract xs ys ⊎ z ∈ ys
  set-subtract-split {[]}     ()
  set-subtract-split {x ∷ xs} {ys} (here refl) with ListAny.any (_≟_ x) ys
  ... | yes x∈ys = inj₂ x∈ys
  ... | no  x∉ys = inj₁ ( (here refl) )
  set-subtract-split {x ∷ xs} {ys} (there x∈xs)
    with ListAny.any (_≟_ x) ys | set-subtract-split x∈xs
  ... | x∈ys⊎x∉ys | inj₂ z∈ys    = inj₂ z∈ys
  ... | yes x∈ys  | inj₁ z∈xs-ys = inj₁  z∈xs-ys 
  ... | no  x∉ys  | inj₁ z∈xs-ys = inj₁ ( (there z∈xs-ys) )

  set-subtract-notin : ∀ {xs ys z} → z ∈ xs → z ∉ ys → z ∈ set-subtract xs ys
  set-subtract-notin{xs}{ys}{z} z∈ z∉ with set-subtract-split{xs}{ys}{z} z∈
  ... | inj₁ a = a
  ... | inj₂ b = ⊥-elim (z∉ b)

-- note: the fixity of our triple-apply _#_ combinator
-- is different from the usual fixity of _$_.
infixl 1 _#_

-- applying three functions to three values in parallel
_#_ : {A B C : Set} → {D : A → Set} → {E : B → Set} → {F : C → Set} →
  ((a : A) → D a) × ((b : B) → E b) × ((c : C) → F c) →
  (abc : A × B × C) → D (proj₁ abc) × E (proj₁ (proj₂ abc)) × F (proj₂ (proj₂ abc))
(f , g , h) # (x , y , z) = f x ,′ g y ,′ h z

infix 6 _U̬_

_U̬_ : List ℕ × List ℕ × List ℕ → List ℕ × List ℕ × List ℕ → List ℕ × List ℕ × List ℕ
(S , s , v) U̬ (S1 , s1 , v1) = S ++ S1 ,′ s ++ s1 ,′ v ++ v1
infixr 6 _|̌_
infixr 6 _|¹_
_|¹_ = ListSet.set-subtract Data.Nat._≟_
_|̌_ : List ℕ × List ℕ × List ℕ → List ℕ × List ℕ × List ℕ → List ℕ × List ℕ × List ℕ
(S , s , x) |̌ (S1 , s1 , x1)
   = (S |¹ S1) , (s |¹ s1) , (x |¹ x1)

∪-assoc : ∀ xs³ ys³ zs³ → (xs³ U̬ ys³) U̬ zs³ ≡ xs³ U̬ (ys³ U̬ zs³)
∪-assoc xs³ ys³ zs³
  rewrite ++-assoc (proj₁ xs³)         (proj₁ ys³)         (proj₁ zs³)
        | ++-assoc (proj₁ (proj₂ xs³)) (proj₁ (proj₂ ys³)) (proj₁ (proj₂ zs³))
        | ++-assoc (proj₂ (proj₂ xs³)) (proj₂ (proj₂ ys³)) (proj₂ (proj₂ zs³)) = refl



xs++[]≡xs : ∀{A : Set} → (xs : List A) → xs ++ [] ≡ xs
xs++[]≡xs xs = proj₂ (Monoid.identity (Data.List.Properties.++-monoid _)) xs

x∈xs++[]→x∈xs : ∀{A} → {x : A} → {xs : List A} → x ∈ (xs ++ []) → x ∈ xs
x∈xs++[]→x∈xs {xs = xs} x∈xs rewrite xs++[]≡xs xs = x∈xs



_⊆¹_ : List ℕ → List ℕ → Set
xs ⊆¹ ys = ∀ x → x ∈ xs → x ∈ ys

_⊆_ : List ℕ × List ℕ × List ℕ → List ℕ × List ℕ × List ℕ → Set
(Ss₁ , ss₁ , xs₁) ⊆ (Ss₂ , ss₂ , xs₂) =
  (Ss₁ ⊆¹ Ss₂) × (ss₁ ⊆¹ ss₂) × (xs₁ ⊆¹ xs₂)



⊆¹-refl : ∀ {xs} → xs ⊆¹ xs
⊆¹-refl _ p = p

⊆-refl : ∀ {xs³} → xs³ ⊆ xs³
⊆-refl = ⊆¹-refl ,′ ⊆¹-refl ,′ ⊆¹-refl

⊆-empty-left : ∀ {xs³} → ([] ,′ [] ,′ []) ⊆ xs³
⊆-empty-left = (λ _ ()) ,′ (λ _ ()) ,′ (λ _ ())

⊆¹-trans : ∀{xs ys zs} → xs ⊆¹ ys → ys ⊆¹ zs → xs ⊆¹ zs
⊆¹-trans xs⊆ys ys⊆zs w w∈xs = ys⊆zs _ (xs⊆ys _ w∈xs)

⊆-trans : ∀{xs³ ys³ zs³} → xs³ ⊆ ys³ → ys³ ⊆ zs³ → xs³ ⊆ zs³
⊆-trans xs³⊆ys³ ys³⊆zs³ = ⊆¹-trans ,′ ⊆¹-trans ,′ ⊆¹-trans # xs³⊆ys³ # ys³⊆zs³

⊆¹-respect-|¹ : ∀{xs ys} zs → xs ⊆¹ ys → (xs |¹ zs) ⊆¹ (ys |¹ zs)
⊆¹-respect-|¹{xs}{ys} zs xs⊂ys a a∈ with ListSet.set-subtract-merge Data.Nat._≟_ {xs}{zs}{a} a∈
... | (a∈xs , a∉zs) = ListSet.set-subtract-notin Data.Nat._≟_ (xs⊂ys a a∈xs) a∉zs

⊆-respect-|̌ : ∀{xs ys} zs → xs ⊆ ys → (xs |̌ zs) ⊆ (ys |̌ zs)
⊆-respect-|̌ zs sub = ⊆¹-respect-|¹ , ⊆¹-respect-|¹  , ⊆¹-respect-|¹  # zs # sub

∷-respect-⊆¹ : ∀{xs ys} z → xs ⊆¹ ys → (z ∷ xs) ⊆¹ (z ∷ ys)
∷-respect-⊆¹ z sub .z (here refl) = here refl
∷-respect-⊆¹ z sub a (there a∈) = there (sub a a∈)

∪ˡ : ∀{xs³ ys³ zs³} → xs³ ⊆ ys³ → xs³ ⊆ (ys³ U̬ zs³)
∪ˡ (Ss₁⊆Ss₂ , ss₁⊆ss₂ , xs₁⊆xs₂) =
  (λ S → ++ˡ ∘ Ss₁⊆Ss₂ S) ,′
  (λ s → ++ˡ ∘ ss₁⊆ss₂ s) ,′
  (λ x → ++ˡ ∘ xs₁⊆xs₂ x)

∪ʳ : ∀{xs³ ys³} → (zs³ : List ℕ × List ℕ × List ℕ) → xs³ ⊆ ys³ → xs³ ⊆ (zs³ U̬ ys³)
∪ʳ xs (Ss₁⊆Ss₂ , ss₁⊆ss₂ , xs₁⊆xs₂) =
  (λ S → ++ʳ (proj₁ xs)         ∘ Ss₁⊆Ss₂ S) ,′
  (λ s → ++ʳ (proj₁ (proj₂ xs)) ∘ ss₁⊆ss₂ s) ,′
  (λ x → ++ʳ (proj₂ (proj₂ xs)) ∘ xs₁⊆xs₂ x)

∪¹-unjoin-⊆¹ : ∀ {ys zs} xs → (xs ++ ys) ⊆¹ zs → xs ⊆¹ zs × ys ⊆¹ zs
∪¹-unjoin-⊆¹ xs xs++ys⊆zs = (λ x x∈xs → xs++ys⊆zs x (++ˡ x∈xs)) ,′
                           (λ x x∈ys → xs++ys⊆zs x (++ʳ xs x∈ys))

∪-unjoin-⊆ : ∀ {ys³ zs³} xs³ → (xs³ U̬ ys³) ⊆ zs³ → xs³ ⊆ zs³ × ys³ ⊆ zs³
∪-unjoin-⊆ xs³ xs³∪ys³⊆zs³ = unzip³ (∪¹-unjoin-⊆¹ ,′ ∪¹-unjoin-⊆¹ ,′ ∪¹-unjoin-⊆¹ #
                                      xs³ # xs³∪ys³⊆zs³)
  where unzip³ : {A B C D E F : Set} → (A × D) × (B × E) × (C × F) → (A × B × C) × (D × E × F)
        unzip³ ((a , d) , (b , e) , (c , f)) = (a , b , c) , (d , e , f)

∪-unjoin-⊆ˡ : ∀{xs³ ys³ zs³} → (xs³ U̬ ys³) ⊆ zs³ → xs³ ⊆ zs³
∪-unjoin-⊆ˡ {xs³} = proj₁ ∘ ∪-unjoin-⊆ xs³

∪-unjoin-⊆ʳ : ∀ {ys³ zs³} xs³ → (xs³ U̬ ys³) ⊆ zs³ → ys³ ⊆ zs³
∪-unjoin-⊆ʳ xs³ = proj₂ ∘ ∪-unjoin-⊆ xs³

∪¹-join-⊆¹ : ∀{xs ys zs} → xs ⊆¹ zs → ys ⊆¹ zs → (xs ++ ys) ⊆¹ zs
∪¹-join-⊆¹ {xs} xs⊆zs ys⊆zs w w∈xs++ys with ++⁻ xs w∈xs++ys
... | inj₁ w∈xs = xs⊆zs _ w∈xs
... | inj₂ w∈ys = ys⊆zs _ w∈ys

∪-join-⊆ : ∀{xs³ ys³ zs³} → xs³ ⊆ zs³ → ys³ ⊆ zs³ → (xs³ U̬ ys³) ⊆ zs³
∪-join-⊆ xs³⊆zs³ ys³⊆zs³ = ∪¹-join-⊆¹ ,′ ∪¹-join-⊆¹ ,′ ∪¹-join-⊆¹ # xs³⊆zs³ # ys³⊆zs³

∪-respect-⊆-left : ∀{xs³ ys³ zs³} → xs³ ⊆ ys³ → (xs³ U̬ zs³) ⊆ (ys³ U̬ zs³)
∪-respect-⊆-left {xs³} {ys³} {zs³} xs³⊆ys³ = ∪-join-⊆ (∪ˡ xs³⊆ys³) (∪ʳ ys³ ⊆-refl)

∪-respect-⊆-right : ∀{xs³ ys³} zs³ → xs³ ⊆ ys³ → (zs³ U̬ xs³) ⊆ (zs³ U̬ ys³)
∪-respect-⊆-right {xs³} {ys³} zs³ xs³⊆ys³ = ∪-join-⊆ (∪ˡ (⊆-refl {zs³})) (∪ʳ zs³ xs³⊆ys³)

∪¹-respect-⊆¹-right : ∀ {xs ys} zs → xs ⊆¹ ys → (zs ++ xs) ⊆¹ (zs ++ ys)
∪¹-respect-⊆¹-right zs xs⊆ys = proj₁ (∪-respect-⊆-right (zs ,′ [] ,′ []) (xs⊆ys ,′ ⊆¹-refl {[]} ,′ ⊆¹-refl {[]}))

∪¹-respect-⊆¹-left : ∀ {xs ys zs} → xs ⊆¹ ys → (xs ++ zs) ⊆¹ (ys ++ zs)
∪¹-respect-⊆¹-left{zs = zs} xs⊆ys =  proj₁ (∪-respect-⊆-left{zs³ = (zs ,′ [] ,′ [])} (xs⊆ys ,′ ⊆¹-refl {[]} ,′ ⊆¹-refl {[]})) 

⊆-subst-left : ∀{xs³ ys³ zs³} → xs³ ≡ ys³ → xs³ ⊆ zs³ → ys³ ⊆ zs³
⊆-subst-left refl xs³⊆zs³ = xs³⊆zs³

∪-comm-⊆-left : ∀ {ys³ zs³} xs³ → (xs³ U̬ ys³) ⊆ zs³ → (ys³ U̬ xs³) ⊆ zs³
∪-comm-⊆-left xs³ xs³∪ys³⊆zs³ =
  ∪-join-⊆ (proj₂ (∪-unjoin-⊆ xs³ xs³∪ys³⊆zs³)) (proj₁ (∪-unjoin-⊆ xs³ xs³∪ys³⊆zs³))

∪-comm-⊆-right : ∀ {xs³ ys³} zs³ → xs³ ⊆ (ys³ U̬ zs³) → xs³ ⊆ (zs³ U̬ ys³)
∪-comm-⊆-right zs³ xs³⊆ys³∪zs³ = ⊆-trans xs³⊆ys³∪zs³ (∪-join-⊆ (∪ʳ zs³ ⊆-refl) (∪ˡ ⊆-refl))



distinct' : ∀{A : Set} -> (xs : List A) -> (ys : List A) -> Set
distinct'{A} xs ys = (z : A) -> z ∈ xs -> z ∈ ys -> ⊥

distinct : (xs : List ℕ × List ℕ × List ℕ) -> (ys : List ℕ × List ℕ × List ℕ) -> Set
distinct (S , s , v) (S1 , s1 , v1) = distinct' S S1 × distinct' s s1 × distinct' v v1

distinct-empty-left : ∀ {xs³} → distinct ([] ,′ [] ,′ []) xs³
distinct-empty-left = (λ _ ()) ,′ (λ _ ()) ,′ (λ _ ())

distinct-empty-right : ∀ {xs³} → distinct xs³ ([] ,′ [] ,′ [])
distinct-empty-right = (λ _ _ ()) ,′ (λ _ _ ()) ,′ (λ _ _ ())

distinct'-sym : ∀{A L1 L2} → (distinct'{A} L1 L2) → (distinct'{A} L2 L1)
distinct'-sym d = λ z x x₁ → d z x₁ x

distinct'-to-left : {xs ys zs : List ℕ} →
  (distinct' xs ys → distinct' xs zs) →
  distinct' ys xs → distinct' zs xs
distinct'-to-left f ys≠xs = distinct'-sym (f (distinct'-sym ys≠xs))

distinct-sym : ∀{VL1 VL2} → distinct VL1 VL2 → distinct VL2 VL1
distinct-sym (a , b , c) = (distinct'-sym a) , ((distinct'-sym b) , (distinct'-sym c))

dist'++ˡ : ∀{A V1 V2 V3} → (distinct'{A} V1 (V2 ++ V3)) → (distinct'{A} V1 V2)
dist'++ˡ {A} {V1} {V2} {V3} d = λ z x x₁ → d z x (++ˡ x₁)

dist'++ʳ : ∀{A V1 V2 V3} → (distinct'{A} V1 (V2 ++ V3)) → (distinct'{A} V1 V3)
dist'++ʳ {A} {V1} {V2} {V3} d = λ z x x₁ → d z x (++ʳ V2 x₁)


dist'++b : ∀{A V1 V2 V3 V4} → (distinct'{A} (V1 ++ V2) (V3 ++ V4)) → (distinct'{A} V1 V3)
dist'++b d = λ z x x₁ → d z (++ˡ x) (++ˡ x₁)

dist':: : ∀{A V1 V2 S} → (distinct'{A} V1 (S ∷ V2)) → (distinct' V1 V2)
dist'::{A}{V1}{V2}{S} d = dist'++ʳ{A}{V1}{[ S ]}{V2} d

dist'-sym : ∀{A L1 L2} → (distinct'{A} L1 L2) → (distinct' L2 L1)
dist'-sym d = λ z x x₁ →  d z x₁ x

distinct'-union-left : ∀ {xs ys zs : List ℕ} →
  distinct' xs zs → distinct' ys zs → distinct' (xs ++ ys) zs
distinct'-union-left {xs} xs≠zs ys≠zs x x∈xs++ys x∈zs with ++⁻ xs x∈xs++ys
... | inj₁ x∈xs = xs≠zs x x∈xs x∈zs
... | inj₂ x∈ys = ys≠zs x x∈ys x∈zs

distinct-union-left : ∀ {xs ys zs} →
  distinct xs zs → distinct ys zs → distinct (xs U̬ ys) zs
distinct-union-left xs≠zs xs≠ys =
  distinct'-union-left ,′ distinct'-union-left ,′ distinct'-union-left #
    xs≠zs # xs≠ys

distinct-union-right : ∀ {xs ys zs} →
  distinct zs xs → distinct zs ys → distinct zs (xs U̬ ys)
distinct-union-right zs≠xs zs≠ys =
  distinct-sym (distinct-union-left (distinct-sym zs≠xs) (distinct-sym zs≠ys))

⊆¹-respect-distinct'-left : ∀{xs ys zs} → xs ⊆¹ ys → distinct' ys zs → distinct' xs zs
⊆¹-respect-distinct'-left xs⊆ys ys≠zs x x∈xs x∈zs = ys≠zs x (xs⊆ys x x∈xs) x∈zs

⊆-respect-distinct-left : ∀{xs³ ys³ zs³} → xs³ ⊆ ys³ → distinct ys³ zs³ → distinct xs³ zs³
⊆-respect-distinct-left {xs³} {ys³} {zs³} xs³⊆ys³ ys³≠zs³ =
  ⊆¹-respect-distinct'-left ,′ ⊆¹-respect-distinct'-left ,′ ⊆¹-respect-distinct'-left #
    xs³⊆ys³ # ys³≠zs³

⊆¹-respect-distinct'-right : ∀{xs ys zs} → xs ⊆¹ ys → distinct' zs ys → distinct' zs xs
⊆¹-respect-distinct'-right xs⊆ys zs≠ys =
  distinct'-sym (⊆¹-respect-distinct'-left xs⊆ys (distinct'-sym zs≠ys))

⊆-respect-distinct-right : ∀{xs³ ys³ zs³} → xs³ ⊆ ys³ → distinct zs³ ys³ → distinct zs³ xs³
⊆-respect-distinct-right {xs³} {ys³} {zs³} xs³⊆ys³ zs³≠ys³ =
  distinct-sym (⊆-respect-distinct-left xs³⊆ys³ (distinct-sym zs³≠ys³))


distinct'-dec : (xs ys : List ℕ) -> Dec (∃ λ z -> z ∈ xs × z ∈ ys)
distinct'-dec [] ys = no λ { (z , () , z∈ys) }
distinct'-dec (x ∷ xs) ys with ListAny.any (\ x' -> x Data.Nat.≟ x') ys
distinct'-dec (x ∷ xs) ys | yes p = yes (x , here refl , p)
distinct'-dec (x ∷ xs) ys | no ¬p with distinct'-dec xs ys
distinct'-dec (x ∷ xs) ys | no ¬p | yes (z , z∈xs , x∈ys) = yes (z , there z∈xs , x∈ys)
distinct'-dec (x ∷ xs) ys | no ¬p₁ | no ¬p =
  no (\ { (.x , here refl , z∈ys) → ¬p₁ z∈ys ;
          (z , there z∈xs , z∈ys) → ¬p (z , z∈xs , z∈ys) } )

distinct-dec : (xs ys : List ℕ × List ℕ × List ℕ) ->
  Dec ((∃ λ S → (S ∈ proj₁ xs) × (S ∈ proj₁ ys)) ⊎
       (∃ λ s → (s ∈ proj₁ (proj₂ xs)) × (s ∈ proj₁ (proj₂ ys))) ⊎
       (∃ λ x → (x ∈ proj₂ (proj₂ xs)) × (x ∈ proj₂ (proj₂ ys))))
distinct-dec (S1 , s1 , x1) (S2 , s2 , x2) with distinct'-dec S1 S2
distinct-dec (S1 , s1 , x1) (S2 , s2 , x2) | yes S1S2 = yes (inj₁ S1S2)
distinct-dec (S1 , s1 , x1) (S2 , s2 , x2) | no ¬S1S2 with distinct'-dec s1 s2
distinct-dec (S1 , s1 , x1) (S2 , s2 , x2) | no ¬S1S2 | yes s1s2 =
  yes (inj₂ (inj₁ s1s2))
distinct-dec (S1 , s1 , x1) (S2 , s2 , x2) | no ¬S1S2 | no ¬s1s2 with distinct'-dec x1 x2
distinct-dec (S1 , s1 , x1) (S2 , s2 , x2) | no ¬S1S2 | no ¬s1s2 | yes x1x2 =
  yes (inj₂ (inj₂ x1x2))
distinct-dec (S1 , s1 , x1) (S2 , s2 , x2) | no ¬S1S2 | no ¬s1s2 | no ¬x1x2 =
  no (λ { (inj₁ x) → ¬S1S2 x ; (inj₂ (inj₁ x)) → ¬s1s2 x ; (inj₂ (inj₂ y)) → ¬x1x2 y })

distinct-not-distinct-dec : ∀ {xs ys} -> distinct xs ys ->
      ((∃ λ S → (S ∈ proj₁ xs) × (S ∈ proj₁ ys)) ⊎
       (∃ λ s → (s ∈ proj₁ (proj₂ xs)) × (s ∈ proj₁ (proj₂ ys))) ⊎
       (∃ λ x → (x ∈ proj₂ (proj₂ xs)) × (x ∈ proj₂ (proj₂ ys))))
      -> ⊥
distinct-not-distinct-dec {xs} {ys} DXY (inj₁ (NDXYS , NDXYs , NDXYx)) = (proj₁ DXY) NDXYS  NDXYs  NDXYx
distinct-not-distinct-dec {xs} {ys} DXY (inj₂ (inj₁ (NDXYS , NDXYs , NDXYx))) = (proj₁ (proj₂ DXY)) NDXYS  NDXYs  NDXYx
distinct-not-distinct-dec {xs} {ys} DXY (inj₂ (inj₂ (NDXYS , NDXYs , NDXYx))) = (proj₂ (proj₂ DXY)) NDXYS  NDXYs  NDXYx

distinct-dec-is-distinct : ∀ {xs ys} ->
      (((∃ λ S → (S ∈ proj₁ xs) × (S ∈ proj₁ ys)) ⊎
        (∃ λ s → (s ∈ proj₁ (proj₂ xs)) × (s ∈ proj₁ (proj₂ ys))) ⊎
        (∃ λ x → (x ∈ proj₂ (proj₂ xs)) × (x ∈ proj₂ (proj₂ ys))))
        -> ⊥) -> distinct xs ys
distinct-dec-is-distinct {xs} {ys} FAIL =
  ((λ z z∈xs z∈ys → FAIL (inj₁ (z , z∈xs , z∈ys))) ,
   (λ z z∈xs z∈ys → FAIL (inj₂ (inj₁ (z , z∈xs , z∈ys)))) ,
   (λ z z∈xs z∈ys → FAIL (inj₂ (inj₂ (z , z∈xs , z∈ys)))))

case_return_of_ : ∀ {a b} {A : Set a} (x : A) (B : A → Set b) → (∀ x → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

typeof : ∀{𝕝}{A : Set 𝕝} → A → Set 𝕝
typeof{_}{A} _ = A

fst : ∀{l} {A B C : Set l} → A × B × C → A
fst = proj₁

snd : ∀{l} {A B C : Set l} → A × B × C → B
snd = proj₁ ∘ proj₂

thd : ∀{l} {A B C : Set l} → A × B × C → C
thd = proj₂ ∘ proj₂

∈:: : ∀{A} {x y : A} → x ∈ (y ∷ []) → x ≡ y
∈:: (here px) = px
∈:: (there ())

n∉map-suc-n-+ : ∀ n xs  → ¬ (n ∈ Data.List.map (suc n +_) xs)
n∉map-suc-n-+ n [] ()
n∉map-suc-n-+ n (x ∷ xs) (here n≡suc⟨n+x⟩) with cong (_∸ n) n≡suc⟨n+x⟩
... | n∸n≡suc⟨n+x⟩∸n rewrite n∸n≡0 n | +-comm n x | m+n∸n≡m (suc x) n with n∸n≡suc⟨n+x⟩∸n
... | ()
n∉map-suc-n-+ n (x ∷ xs) (there n∈map-suc-n-+) = n∉map-suc-n-+ n xs n∈map-suc-n-+

map-+-swap-suc : ∀ n xs →
  Data.List.map (_+_ n) (Data.List.map suc xs) ≡ Data.List.map suc (Data.List.map (_+_ n) xs)
map-+-swap-suc n xs
  rewrite sym (map-compose {g = _+_ n} {f = suc}      xs)
        |      map-cong (λ m → +-comm n (suc m))      xs
        |      map-cong (λ m → cong suc (+-comm m n)) xs
        |      map-compose {g = suc}   {f = _+_ n}    xs
  = refl

map-+-compose-suc : ∀ n xs →
  Data.List.map (_+_ n) (Data.List.map suc xs) ≡ Data.List.map (_+_ (suc n)) xs
map-+-compose-suc n xs
  rewrite map-+-swap-suc n xs
        | sym (map-compose {g = suc} {f = _+_ n} xs)
  = refl

{-

This module implements sets of proofs indexed
by some key `K`, such that each key is unique.
This is encoded in UniqueSet by a list of proofs
that each key does not appear in the remainder
of the set.

-}

module UniquedSet where
  open import Data.Product hiding (map ; curry)
  open import Data.Maybe using (Maybe ; just ; nothing)
  open import Relation.Binary.PropositionalEquality
    using ([_] ; inspect)

  {-
   Proves that for some key accessor `f`,
   that key only occurs once in the list
  -}
  data UniquedList {A : Set} {B : Set}  (f : (A → B)) : List A → Set where
    e : (UniquedList f [])
    c : (x : A) → (x₁ : List A)
        → (fx∉l : ((f x) ∉ (Data.List.map f x₁)))
        → (UniquedList f x₁)
        → (UniquedList f (x ∷ x₁))

  {- A List indexed by K, such that each `K` only occurs once -}
  record UniquedSet {K : Set} (a : K → Set) : Set where
    constructor uniqued-set
    field
      lst : List (Σ[ n ∈ K ] (a n))
      unq : UniquedList proj₁ lst

  {- Curry a function which takes an exploded UniqueSet
     to take an actual UniqueSet.

     Useful when the function must do induction over the UniquedSet,
     as constantly taking the set appart and putting it back together
     disagrees with the termination checker.
  -}
  curry : ∀{𝕝}{B : Set 𝕝}{K}{A : K → Set}
          → (f : (lst : List (Σ[ n ∈ K ] (A n)))
          → UniquedList proj₁ lst → B)
          → (UniquedSet A) → B
  curry f (uniqued-set a b) = f a b

  {- 
    Map some function `f2` over the elements of the UniqueList
    using `f3` as the new accessor function.
  -}
  map : {A : Set} {B : Set} {C : Set} {D : Set} {f1 : A → B} {l : List A}
        → (f2 : A → C)
        → (f3 : C → D)
        → (UniquedList f1 l)
        → ((x : A) → (l : List A)
        → (f3 (f2 x)) ∈ (Data.List.map f3 (Data.List.map f2 l))
        → (f1 x) ∈ (Data.List.map f1 l))
        → (UniquedList f3 (Data.List.map f2 l))
  map f2 f3 e fix = e
  map{f1 = f1} f2 f3 (c x x₁ fx∉l l) fix = c (f2 x) (Data.List.map f2 x₁) (fx∉l ∘ (fix x x₁)) (map f2 f3 l fix)

  {- A to encode may-maybe on UniqueLists -}
  lift-maybe-pair : ∀{B : Set} → {A : B → Set} → (Σ B (Maybe ∘ A)) → Maybe (Σ B A)
  lift-maybe-pair (a , just x) = just (a , x)
  lift-maybe-pair (a , nothing) = nothing

  {- Removes `nothing`s from the list -}
  map-maybe : ∀{B} → {A : B → Set} → {l : List (Σ B (Maybe ∘ A))}
              → UniquedList proj₁ l
              → UniquedList proj₁ (Data.List.mapMaybe lift-maybe-pair l)
  map-maybe {B} {A} {.[]} e = e
  map-maybe {B} {A} {.((b , nothing) ∷ x₁)} (c (b , nothing) x₁ fx∉l ul) 
     =  map-maybe ul
  map-maybe {B} {A} {.((b , just x) ∷ x₁)} (c (b , just x) x₁ fx∉l ul)
    =  c (b , x) (Data.List.mapMaybe lift-maybe-pair x₁) (ug x₁ fx∉l) (map-maybe ul) 
    where
    ug : ∀ (l : List $ Σ B (Maybe ∘ A)) → b ∉ (Data.List.map proj₁ l) → b ∉ (Data.List.map proj₁ (Data.List.mapMaybe lift-maybe-pair l))
    ug [] ∉ ()
    ug ((b , nothing) ∷ l) ∉ ∈ = ug l (∉ ∘ there) ∈
    ug ((b , just x) ∷ l) ∉ (here px) = ∉ (here px)
    ug ((b , just x) ∷ l) ∉ (there ∈) = ug l (∉ ∘ there) ∈

  {- Remove `nothing`s from the set-}
  set-map-maybe : ∀{K}{A : K → Set} → UniquedSet (Maybe ∘ A) → UniquedSet A
  set-map-maybe u = uniqued-set (Data.List.mapMaybe lift-maybe-pair lst) (map-maybe unq)
    where open UniquedSet u

  {-
     map `fk` over the keys and `fa` over the values of the unique set.
     Requires the proof that fk is injective to maintain the proofs
     of uniqueness.
  -}
  set-map : ∀{K1 K2 : Set} {A1 : K1 → Set} {A2 : K2 → Set}
            → UniquedSet{K1} A1
            → (fk : K1 → K2)
            → (fa : ∀{k1} → (A1 k1) → (A2 (fk k1)))
            → (∀{a b} → (fk a) ≡ (fk b) → a ≡ b)
            → UniquedSet{K2} A2
  set-map{K1}{K2}{A1}{A2} st fk fa fix
    =  uniqued-set (Data.List.map f2 lst)
         $ map f2 f3 unq ug
       where
         open UniquedSet st
         f2 = (Prod.map fk fa)
         f3 =  proj₁
         ug : (x : ∃ A1 ) → (l : List (∃ A1))
              → (f3 (f2 x)) ∈ (Data.List.map f3 (Data.List.map f2 l))
              → (proj₁ x) ∈ (Data.List.map proj₁ l)
         ug x [] ()
         ug x (x₁ ∷ l) (here px) = here $ fix px
         ug x (x₁ ∷ l) (there x∈) = there (ug x l x∈)


