open import Relation.Binary
  using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; subst ; subst₂)
open import Data.Nat as Nat
  using (ℕ ; _≤′_ ; _+_)
open import Relation.Binary.PropositionalEquality using (sym ; cong ; module ≡-Reasoning )
open import Data.Unit
open import Level using (_⊔_)
open import Data.Nat

open ≡-Reasoning

import Relation.Unary as U
open import Data.Key

open import Function
  using (_∘_)

open import Relation.Nullary

module Data.FiniteMap
  (Key : Set)
  {{b : BijectiveKey Key}}
  where

open BijectiveKey b

open import utility
open UniquedSet using (UniquedList ; UniquedSet ; uniqued-set)

open import Data.Maybe using (just)
open import Data.Empty
  using (⊥-elim)
open import Data.List
  using (List ; _++_ ; [_] ; [] ; _∷_)
open import Data.List.Any
  using (any ; here ; there ; Any)
open import Data.Nat
  using (ℕ ; zero ; suc)
open import Data.Sum
  using (inj₁ ; inj₂ ; _⊎_)
open import Data.Product
  using (Σ ; Σ-syntax ; ∃ ; proj₁ ; proj₂ ; _×_ ; _,_ ; ∃-syntax ; uncurry ; map)
open import Function
  using (id ; _$_)
open import Relation.Nullary
  using (yes ; no)
open import Data.OrderedListMap(Key)(inject) as OMap hiding (insert-mono ; U-mono)
open import Data.Bool using (Bool ; true ; false)
open import Data.List.Properties using (map-compose)

private
  nbiject : ∀ {k1 k2} → k1 ≢ k2 → inject k1 ≢ inject k2
  nbiject = (_∘ inject-injective)

Map : Set → Set
Map = LMap

keys : ∀{Value} → Map Value → List ℕ
keys{Value} l = (Dom' Value l)

keys+∈ : ∀{Value} → (l : Map Value) → List (∃[ n ] (n ∈ (Dom' Value l)))
keys+∈{Value} l = (Dom'+∈ Value l)


inj= : Key → ℕ → Set
inj= = _≡_ ∘ inject

∈Dom : ∀{Value} → Key → Map Value → Set
∈Dom{Value} k m = (inject k) ∈ (Dom' Value m)

in-inject : ∀ {Value}{x : ℕ} → (l : Map Value) → x ∈ Dom' Value l → ∈Dom (surject x) l
in-inject{x = x} l ∈ rewrite surject-inject{x} = ∈



key-map : ∀{Value}{a}{L : Set a} → (l : Map Value) → (f : (k : Key) → (∈Dom k l) → L) → List L
key-map{L = L} l f
  = Data.List.map ((uncurry f) ∘ (map surject (in-inject l)))
                  (keys+∈ l)

key-unique-map : ∀{Value} → (l : Map Value) → (A : Key → Set) → (f : (k : Key) → (∈Dom k l) → (A k)) → UniquedSet A
key-unique-map{Value} l A f
  = uniqued-set (Data.List.map f2 lst)
    $ UniquedSet.map f2 proj₁ unq ug 
  where uld = (Dom'+∈-unique Value l)
        open UniquedSet.UniquedSet uld
        f2 = (λ { (k , ∈) → (surject k) , f (surject k) (in-inject l ∈)})
        ug : (x : ∃ (_∈ (Dom' Value l))) → (l₁ : List (∃ (_∈ (Dom' Value l))))
             → proj₁ (f2 x) ∈ (Data.List.map proj₁ (Data.List.map f2 l₁))
             → proj₁ x ∈ (Data.List.map proj₁ l₁)
        ug x [] ()
        ug x (x₁ ∷ l₁) (here px) rewrite surject-injective px = here refl
        ug x (x₁ ∷ l₁) (there x₂) = there (ug x l₁ x₂)

∈Check : ∀{Value}
         → (k : Key)
         → (m : Map Value)
         → Relation.Nullary.Dec (∈Dom k m)
∈Check{Value} k m = any (Nat._≟_ (inject k)) (Dom' Value m)

lookup : ∀{Value k} → (l : Map Value) → (∈Dom k l) → Value
lookup{Value}{k = k} m k∈ = deref Value (inject k) m k∈

update : ∀{Value} → (l : Map Value) → Key → Value → Map Value
update{Value} l k v = m-insert Value (just v) (inject k) l

-- Union map. For repeated keys, the values from the second map is preferred.
union : ∀{Value} → Map Value → Map Value → Map Value
union{Value} m1 m2 = (_U_ Value m1 m2)

empty : ∀{Value} → Map Value
empty = []

[_↦_] : ∀{Value} → (k : Key) → (v : Value) → Map  Value
[ k ↦ v ] = update empty k v

[_↦_,_↦_] : ∀{Value} →
              (k₁ : Key) → (v₁ : Value) →
              (k₂ : Key) → (v₂ : Value) →
              Map Value
[ k₁ ↦ v₁ , k₂ ↦ v₂ ] = update [ k₁ ↦ v₁ ] k₂ v₂

keys-1map : ∀{Value} → (k : Key) → (v : Value) → keys [ k ↦ v ] ≡ inject k ∷ []
keys-1map {Value} k v = Dom'-1map Value (inject k) v

keys-2map : ∀{Value} → (k₁ : Key) → (v₁ : Value) → (k₂ : Key) → (v₂ : Value) →
  (keys [ k₁ ↦ v₁ , k₂ ↦ v₂ ] ≡ inject k₁ ∷ [] × k₁ ≡ k₂) ⊎
  (keys [ k₁ ↦ v₁ , k₂ ↦ v₂ ] ≡ inject k₁ ∷ inject k₂ ∷ []) ⊎
  (keys [ k₁ ↦ v₁ , k₂ ↦ v₂ ] ≡ inject k₂ ∷ inject k₁ ∷ [])
keys-2map {Value} k₁ v₁ k₂ v₂ =
  Data.Sum.map (Data.Product.map id inject-injective) id
    (Dom'-2map Value (inject k₁) v₁ (inject k₂) v₂)

keys-1map-distinct : ∀{Value} → (k1 k2 : Key) → (v1 v2 : Value) → ¬ (k1 ≡ k2) → utility.distinct' (keys [ k1 ↦ v1 ]) (keys [ k2 ↦ v2 ])
keys-1map-distinct k1 k2 v1 v2 neg z k1∈ k2∈ rewrite (keys-1map k1 v1) | (keys-1map k2 v2) with k1∈ | k2∈
... | here refl | here px = (nbiject neg) px
... | there () | _
... | here px | there ()

keys-1map∈ : ∀{Value} → (k1 : Key) → (v1 : Value) → (inject k1) ∈ keys [ k1 ↦ v1 ]
keys-1map∈ k v rewrite keys-1map k v = here refl

2map-eq-one : ∀{V} k1 k2 v k1∈ →  (lookup{V}{k1} ([ k1 ↦ v , k2 ↦ v ]) k1∈) ≡ v
2map-eq-one {V} k1 k2 = insert-two-eq-one V (inject k1) (inject k2)

2map-eq-two : ∀{V} k1 k2 v k2∈ →  (lookup{V}{k2} ([ k1 ↦ v , k2 ↦ v ]) k2∈) ≡ v
2map-eq-two {V} k1 k2 = insert-two-eq-two V (inject k1) (inject k2)


-- theorems

update-in-keys : ∀{V} m k v →  ∈Dom k (update{V} m k v)
update-in-keys {V} m k = insert-in-domain V m (inject k)

lookup-∈-irr : ∀{Value k m} → (∈1 : ∈Dom k m) → (∈2 : ∈Dom k m) → lookup{Value}{k} m ∈1 ≡ lookup{Value}{k} m ∈2
lookup-∈-irr{Value} ∈1 ∈2 = deref-∈-irr Value ∈1 ∈2

insert-mono : ∀{Value k m k' v} → ∈Dom k m → ∈Dom k (update{Value} m k' v)
insert-mono{Value}{k}{m}{k'}{v} i = (OMap.insert-mono Value {m}{inject k}{inject k'}{v} i)

U-mono : ∀{Value m m' k} → ∈Dom k m → ∈Dom k (union{Value} m m')
U-mono{V}{m}{m'}{k} i =  OMap.U-mono V {m}{m'}{inject k} i

union-comm : ∀ {Value} → (m1 : Map Value) → (m2 : Map Value) → distinct' (keys m1) (keys m2) →  union m1 m2 ≡ union m2 m1
union-comm {Value} m1 m2 keys-m1≠keys-m2 = U-comm Value {m1} {m2} keys-m1≠keys-m2

union-assoc : ∀ {Value} → (m1 m2 m3 : Map Value) → union m1 (union m2 m3) ≡ union (union m1 m2) m3
union-assoc {Value} = U-assoc Value

keys-assoc-comm : ∀ {Value} m1 m2 m3 →
  keys (union {Value} (union {Value} m1 m2) m3) ≡
  keys (union {Value} (union {Value} m1 m3) m2)
keys-assoc-comm {Value} = Dom'-assoc-comm Value

U⁻-m : ∀ {Value m m' n} → ∈Dom n (union {Value} m m') → ∈Dom n m ⊎ ∈Dom n m'
U⁻-m {Value} {m} {m'} {n} = U⁻ Value {m} {m'} {inject n}

U-∉-irr-get-help-m : ∀{Value m m' k} → (k∈m : ∈Dom k m) → ¬ (∈Dom k m') → (k∈' : ∈Dom k (union {Value} m m'))→ lookup {Value} {k} m k∈m ≡ lookup {Value} {k} (union {Value} m m') k∈'
U-∉-irr-get-help-m {Value} = U-∉-irr-get-help Value

U-∉-irr-get-m : ∀{Value m m' k} → (k∈m : ∈Dom k m) → ¬ (∈Dom k m') → ∃ λ k∈' → lookup {Value} {k} m k∈m ≡ lookup {Value} {k} (union {Value} m m') k∈'
U-∉-irr-get-m {Value} = U-∉-irr-get Value

get-U-right-irr-m : ∀ {Value} k m m' →
  (k∈mUm' : ∈Dom k (union {Value} m m')) →
  (k∈m'   : ∈Dom k m') →
  lookup {Value} {k} (union {Value} m m') k∈mUm' ≡ lookup {Value} {k} m' k∈m'
get-U-right-irr-m {Value} k = deref-U-right-irr Value (inject k)

∈-get-U-irr-m : ∀ {Value} k m m' m'' k∈mUm'' k∈m'Um'' →
  (k∈m'' : ∈Dom k m'') →
    lookup {Value} {k} (union {Value} m  m'') k∈mUm'' ≡
    lookup {Value} {k} (union {Value} m' m'') k∈m'Um''
∈-get-U-irr-m {Value} k = ∈-deref-U-irr Value (inject k)

get-U-both-irr-m : ∀ {Value} k m m' m'' k∈m k∈m' k∈mUm'' k∈m'Um'' →
  lookup {Value} {k} m k∈m ≡ lookup {Value} {k} m' k∈m' →
    lookup {Value} {k} (union {Value} m  m'') k∈mUm'' ≡
    lookup {Value} {k} (union {Value} m' m'') k∈m'Um''
get-U-both-irr-m {Value} k = deref-U-both-irr Value (inject k)

putputget : ∀{Value m k k' v v'}
            → ¬ k ≡ k'
            → (∈1 : ∈Dom k m)
            → (∈2 : ∈Dom k (update{Value} m k' v'))
            → lookup{Value}{k} m ∈1 ≡ v
            → lookup{Value}{k} (update{Value} m k' v') ∈2 ≡ v
putputget{V}{m}{k}{k'}{v}{v'} neq kin1 kin2 eq = putputget-neq V {inject k}{inject k'}{m} (nbiject neq) kin1 kin2 eq

putput-overwrite : ∀{Value} m k v v'
                   → (update{Value} (update{Value} m k v) k v') ≡ (update m k v')
putput-overwrite {V} m k v v' = putputget-eq V (inject k) m v v'

getput-m : ∀ {Value} k m →
  (∈1 : ∈Dom k m) →
  m ≡ update {Value} m k (lookup {Value} {k} m ∈1)
getput-m {Value} k = getput Value (inject k)

putget-m : ∀{Value m k v} → (kin : ∈Dom k (update{Value} m k v)) → (lookup{Value}{k} (update{Value} m k v) kin) ≡ v
putget-m {V}{m}{k}{v} kin = putget V kin

update-union-union : ∀ {Value} k v m m' →
  (∈1 : ∈Dom k m) →
  (∈2 : ∈Dom k m') →
    union {Value} m m' ≡
    union {Value} (update {Value} m k v) m'
update-union-union {Value} k = put-U-U Value (inject k)

ineq-m : ∀{Value k m} → (k1 : ∈Dom{Value} k m) → (k2 : ∈Dom k m) → k1 ≡ k2
ineq-m {V}{k}{m} k1 k2 = ineq V {inject k}{m} k1 k2

put-comm : ∀{Value m k1 k2 v1 v2}
          → ¬ k1 ≡ k2 → (update (update{Value} m k1 v1) k2 v2) ≡ (update (update m k2 v2) k1 v1)
put-comm{V}{m}{k1}{k2}{v1}{v2} ¬k1≡k2 = insert-comm V {m}{inject k1}{inject k2}{v1}{v2} (nbiject ¬k1≡k2)

put-union-comm : ∀ {Value} k v m m' →
  ¬ (∈Dom k m') →
    union {Value} (update {Value} m k v) m' ≡
    update {Value} (union {Value} m m') k v
put-union-comm {Value} k = insert-U-comm Value (inject k)

union-=-irr : ∀ {Value} m m' → (keys{Value} m) ≡ (keys{Value} m') → ∀ k k∈ k∈2 → (lookup{Value}{k} (union m m') k∈) ≡ (lookup{Value}{k} m' k∈2)
union-=-irr {V} m m' eql k = U-=-irr V m m' eql (inject k)

union-single-overwrite : ∀ {V} k v1 v2 → union{V} [ k ↦ v1 ] [ k ↦ v2 ] ≡ [ k ↦ v2 ]
union-single-overwrite {V} k v1 v2 = U-single-overwrite V (inject k) v1 v2

update-single-val : ∀ {V} k v k∈ → lookup{V}{k} [ k ↦ v ] k∈ ≡ v
update-single-val {V} k v k∈ = set-single-val V (inject k) v k∈

single-val-overwrite : ∀ {V} k v m → (∈Dom{V} k m) → union{V}  ([ k ↦ v ]) m ≡ m
single-val-overwrite {V} k = overwrite-single-val V (inject k)

union-insert-eq : ∀{V} k v m → (update{V} m k v) ≡ (union{V} m [ k ↦ v ])
union-insert-eq {V} k = U-insert-eq V (inject k)

update-domain-eq : ∀{V} k v m → (inject k) ∈ keys{V} m → (keys m) ≡ (keys (update{V} m k v))
update-domain-eq {V} k = insert-domain-eq V (inject k)

--(OMap.insert-mono Value {m}{inject k}{inject k'}{v} i)
keys-2map∈ : ∀{Value} → (k1 : Key) → (v1 : Value) → (k2 : Key) → (v2 : Value) → (∈Dom k1 [ k1 ↦ v1 , k2 ↦ v2 ]) × (∈Dom k2 [ k1 ↦ v1 , k2 ↦ v2 ])
keys-2map∈ {V} k1 v1 k2 v2 = insert-mono (keys-1map∈ k1 v1) , update-in-keys ([ k1 ↦ v1 ]) k2 v2

count : ∀ {V} -> (V -> Bool) -> Map V -> ℕ
count {V} p m = ocount V p m

change-one-count-goes-down :
  ∀ {Value} (m : Map Value) ->
    (p : Value -> Bool) ->
    (k : Key) ->
    (k∈ : ∈Dom k m) ->
    p (lookup m k∈) ≡ true ->
    (v : Value) ->
    p v ≡ false ->
    count p m ≡ suc (count p (update m k v))
change-one-count-goes-down {V} m p k =
  change-one-ocount-goes-down V m p (inject k)

change-nothing-count-stays-same :
  ∀ {Value} (m : Map Value) ->
    (p : Value -> Bool) ->
    (k : Key) ->
    (k∈ : ∈Dom k m) ->
    (v : Value) ->
    p (lookup m k∈) ≡ p v ->
    count p m ≡ count p (update m k v)
change-nothing-count-stays-same {V} m p k =
  change-nothing-ocount-stays-same V m p (inject k)

count-merge≤′sum-count :
  ∀ {Value}
    (m1 m2 : Map Value) ->
    (p : Value -> Bool) ->
    count p (union m1 m2) ≤′ count p m1 + count p m2
count-merge≤′sum-count {V} m1 m2 p =
  ocount-merge≤′sum-ocount V m1 m2 p
