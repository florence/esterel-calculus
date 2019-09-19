open import Data.Nat as Nat
  using (ℕ ; _+_ ; zero ; suc) 

module Data.OrderedListMap.Properties
  (Key : Set)
  (inject : Key → ℕ)
  (Value : Set)
  where

open import Data.OrderedListMap(Key)(inject)(Value)
open import utility
  hiding (_⊆_)
  renaming (_⊆¹_ to _⊆_)

open import Data.List as List
  using (_∷_ ; [] ; List)
open import Data.List.Any as ListAny
  using (Any ; any ; here ; there)
open import Function
  using (_∘_ ; _$_ ; id ; _∋_)
open import Data.Product as Prod
  using (Σ ; Σ-syntax ; _,_ ; proj₁ ; proj₂ ; _×_ ; _,′_ ; ∃-syntax ; ∃)
open import Relation.Binary.PropositionalEquality as Eql
  using (_≡_ ; refl ; cong ; subst ; sym ; inspect ; [_] ; module ≡-Reasoning) 
open import Data.Maybe as Maybe
  using (Maybe ; just ; nothing)

open import Data.Empty
  using (⊥ ; ⊥-elim)

open import Data.List.Properties as ListP
  using (map-compose)
import Data.Nat.Properties as NatP

open ≡-Reasoning


ProdMap+proj₁≡l+proj₁ : ∀{A : Set}{B : Set}{C : A → Set}{D : B → Set}
                      → (l : A → B) → (r : ∀ {x} → C x → D (l x))
                      → (lst : List (Σ A C))
                      → (List.map proj₁ (List.map (Prod.map{P = C}{Q = D} l r) lst))
                        ≡
                        (List.map l (List.map proj₁ lst))
ProdMap+proj₁≡l+proj₁ l r [] = refl
ProdMap+proj₁≡l+proj₁{D = D} l r (x ∷ lst)
  =  cong (l (proj₁ x) ∷_) $ ProdMap+proj₁≡l+proj₁{D = D} l r lst 
  


tail-keys-∈-equal : ∀ mp x → (0 ∷ (List.map proj₁ (Dom'+∈ (nothing ∷ mp)))) ≡ (List.map proj₁ (Dom'+∈ (just x ∷ mp)))
tail-keys-∈-equal [] x = refl
tail-keys-∈-equal (x₁ ∷ mp) x
  rewrite ProdMap+proj₁≡l+proj₁ id (there{x = 0}) $ Dom'+∈-help (List.map suc (Dom' (x₁ ∷ mp)))
         | tail-keys-∈-equal mp x
         | ListP.map-id $ List.map proj₁ (Dom'+∈-help (List.map suc (Dom' (x₁ ∷ mp))))
        = refl

Dom'-help-suc-swap : ∀  l
                     → List.map proj₁ (Dom'+∈-help (List.map suc l))
                       ≡
                       (List.map suc $ List.map proj₁ $ Dom'+∈-help l)
Dom'-help-suc-swap [] = refl
Dom'-help-suc-swap (x ∷ l)
  rewrite ProdMap+proj₁≡l+proj₁ id (there{x = suc x}) (Dom'+∈-help (List.map suc l))
        | ProdMap+proj₁≡l+proj₁ id (there{x = x}) (Dom'+∈-help l)
        | ListP.map-id $ List.map proj₁ (Dom'+∈-help (List.map suc l)) 
        | ListP.map-id $ List.map proj₁ (Dom'+∈-help l) 
  = cong (suc x ∷_) $ Dom'-help-suc-swap l


proj₁∈-unchanged : ∀ sigs → Dom' sigs ≡ (List.map proj₁ $ Dom'+∈ sigs)
proj₁∈-unchanged [] = refl
proj₁∈-unchanged (nothing ∷ sigs)
  rewrite Dom'-help-suc-swap $ (Dom' sigs)
   = cong (List.map suc) $ proj₁∈-unchanged sigs
proj₁∈-unchanged (just x ∷ sigs)
  rewrite ProdMap+proj₁≡l+proj₁ id (there{x = 0}) $ Dom'+∈-help (List.map suc (Dom' sigs))
         | ListP.map-id $ List.map proj₁ (Dom'+∈-help (List.map suc (Dom' sigs)))
         | Dom'-help-suc-swap $ (Dom' sigs)
  = cong ((0 ∷_) ∘ List.map suc) $ proj₁∈-unchanged sigs

suc-isprodsucin : ∀ l → Dom'+∈-help (List.map suc l) ≡ List.map (Prod.map suc sucin) (Dom'+∈-help l)
suc-isprodsucin [] = refl
suc-isprodsucin (x ∷ l)
   rewrite suc-isprodsucin l
  = cong ((suc x , here refl) ∷_)
         $ (begin
              List.map (Prod.map₂ there) (List.map (Prod.map suc sucin) (Dom'+∈-help l))
              ≡⟨ sym $ ListP.map-compose (Dom'+∈-help l) ⟩
              List.map ((Prod.map₂ there) ∘ (Prod.map suc sucin)) (Dom'+∈-help l)
              ≡⟨ ListP.map-cong (λ { (fst , snd) → refl}) (Dom'+∈-help l) ⟩
              List.map ((Prod.map suc sucin) ∘ (Prod.map₂ there)) (Dom'+∈-help l)
              ≡⟨ ListP.map-compose (Dom'+∈-help l) ⟩
              List.map (Prod.map suc sucin) (List.map (Prod.map₂ there) (Dom'+∈-help l)) ∎)


lift-in : ∀ l x → x ∈ (Dom' l) → Any (λ {(k , _) → x ≡ k}) (Dom'+∈ l)
lift-in = lift-in' ∘ Dom'
 where
  -- like ListAny.map, but it allows the functions domain and range to differ
  ListAny-map : ∀{a b p q}{A : Set a}{B : Set b}{P : A → Set p}{Q : B → Set q}{l}
            → (f : A → B)
            → (cast : ∀ x → P x → Q (f x))
            → Any P l
            → Any Q (List.map f l)
  ListAny-map f cast (here px) = here (cast _ px)
  ListAny-map f cast (there any) = there (ListAny-map f cast any)

  lift-in' : ∀ l x → x ∈ l → Any (λ {(k , _) → x ≡ k}) (Dom'+∈-help l)
  lift-in' [] x ()
  lift-in' (x₁ ∷ l) x (here px) = here px
  lift-in' (x₁ ∷ l) x (there x∈)
    = there $ ListAny-map (Prod.map₂ there) (λ _ z → z) $ (lift-in' l x x∈)


lift-local : ∀ x1 x2 (a b : LMap)
             → (Dom' (x1 ∷ a)) ⊆ (Dom' (x2 ∷ b))
             → (Dom' a) ⊆ (Dom' b)
lift-local (just x₁) (just x₂) _ _ a⇒b x x∈a
  with (a⇒b (suc x) (there (sucin x∈a)))
... | here ()
... | there q = sucout q
lift-local (just x₁) (nothing) _ _ a⇒b x x∈a = sucout (a⇒b (suc x) (there (sucin x∈a)))
lift-local (nothing) (just x₁) _ _ a⇒b x x∈a
  with (a⇒b (suc x) (sucin x∈a))
... | here ()
... | there q = sucout q
lift-local (nothing) (nothing) _ _ a⇒b x x∈a = sucout (a⇒b (suc x) (sucin x∈a))

domain⇔-means-equal :
  ∀(a b : LMap)
  → (Dom' a) ⊆ (Dom' b)
  → (Dom' b) ⊆ (Dom' a)
  → ((Dom' a) ≡ (Dom' b))
domain⇔-means-equal List.[] List.[] a⇒b b⇒a = refl
domain⇔-means-equal List.[] (just x ∷ b) a⇒b b⇒a
  with b⇒a 0 (here refl)
... | ()
domain⇔-means-equal List.[] (nothing ∷ b) a⇒b b⇒a
  = cong (List.map suc)
    $ domain⇔-means-equal List.[] b (λ _ ())
    $ λ x x∈xs → sucout (b⇒a (suc x) (sucin x∈xs))
domain⇔-means-equal (just x ∷ a) List.[] a⇒b b⇒a
  with a⇒b 0 (here refl)
... | ()
domain⇔-means-equal (nothing ∷ a) List.[] a⇒b b⇒a
  = cong (List.map suc)
    $ domain⇔-means-equal a List.[] 
      (λ x x∈xs → sucout (a⇒b (suc x) (sucin x∈xs)))
    $ λ _ ()
domain⇔-means-equal (just x ∷ a) (nothing ∷ b) a⇒b b⇒a
  = ⊥-elim $ 0∈S $ a⇒b 0 (here refl)
domain⇔-means-equal (nothing ∷ a) (just x ∷ b) a⇒b b⇒a
  = ⊥-elim $ 0∈S $ b⇒a 0 (here refl)
domain⇔-means-equal (just x ∷ a) (just y ∷ b) a⇒b b⇒a
  = cong ((0 ∷_) ∘ (List.map suc))
    $ domain⇔-means-equal a b (lift-local (just x) (just y) a b a⇒b) (lift-local (just y) (just x) b a b⇒a) 
domain⇔-means-equal (nothing ∷ a) (nothing ∷ b) a⇒b b⇒a
  = cong (List.map suc)
     $ domain⇔-means-equal a b (lift-local nothing nothing a b a⇒b) (lift-local nothing nothing b a b⇒a)


module Canonical where
  open import Data.Sum
    using (_⊎_ ; inj₁ ; inj₂)
  data Canonical : (l : LMap) → Set where
    empty : Canonical []
    just-empty : ∀ x → Canonical (just x ∷ [])
    cons-j : ∀{l} x → Canonical l → Canonical ((just x) ∷ l)
    cons-n : ∀{x l} → (Canonical (x ∷ l)) → Canonical (nothing ∷ x ∷ l)

  canonical-insert-just : ∀{x l} y → Canonical (x ∷ l) →  Canonical (just y ∷ l)
  canonical-insert-just y (just-empty x) = just-empty y
  canonical-insert-just y (cons-j x can) = cons-j y can
  canonical-insert-just y (cons-n can) = cons-j y can

  m-insert-empty-is-canonical : ∀ x n → Canonical (m-insert (just x) n [])
  m-insert-empty-is-canonical x zero = just-empty x
  m-insert-empty-is-canonical x (suc zero) = cons-n (just-empty x)
  m-insert-empty-is-canonical x (suc (suc n)) = cons-n (m-insert-empty-is-canonical x (suc n))

  m-insert-maintains-canonical : ∀ l x n → Canonical l → Canonical (m-insert (just x) n l)
  m-insert-maintains-canonical [] x zero can = just-empty x
  m-insert-maintains-canonical (x₁ ∷ l) x zero can = canonical-insert-just x can
  m-insert-maintains-canonical [] x (suc n) can = m-insert-empty-is-canonical x (suc n)
  m-insert-maintains-canonical (just x₁ ∷ .[]) x (suc zero) (just-empty .x₁) = cons-j x₁ (just-empty x)
  m-insert-maintains-canonical (just x₁ ∷ l) x (suc zero) (cons-j .x₁ can)
    = cons-j x₁ (m-insert-maintains-canonical l x zero can )
  m-insert-maintains-canonical (just x₁ ∷ .[]) x (suc (suc n)) (just-empty .x₁)
    = cons-j x₁ (m-insert-empty-is-canonical x (suc n))
  m-insert-maintains-canonical (just x₁ ∷ l) x (suc (suc n)) (cons-j .x₁ can)
   = cons-j x₁ (m-insert-maintains-canonical l x (suc n) can)
  m-insert-maintains-canonical (nothing ∷ a ∷ b) x (suc zero) (cons-n can)
    = cons-n (m-insert-maintains-canonical (a ∷ b) x zero can)
  m-insert-maintains-canonical (nothing ∷ a ∷ b) x (suc (suc n)) (cons-n can)
    = cons-n (m-insert-maintains-canonical (a ∷ b) x (suc n) can)


  cannon-split : ∀(x y : Maybe Value)(l1 l2 : LMap)
    → (((x ∷ l1) U (y ∷ l2)) ≡ (x ∷ (l1 U l2)))
      ⊎
      (((x ∷ l1) U (y ∷ l2)) ≡ (y ∷ (l1 U l2)))
  cannon-split (just x) (just x₁) l1 l2 = inj₂ refl
  cannon-split (just x) nothing l1 l2 = inj₁ refl
  cannon-split nothing (just x) l1 l2 = inj₂ refl
  cannon-split nothing nothing l1 l2 = inj₁ refl

  U-maintains-canonical : ∀{m1 m2} → Canonical m1 → Canonical m2 → Canonical (m1 U m2)
  U-maintains-canonical {.[]} {.[]} empty empty = empty
  U-maintains-canonical {.[]} {.(just x ∷ [])} empty (just-empty x) = just-empty x
  U-maintains-canonical {.[]} {.(just x ∷ _)} empty (cons-j x c2) = (cons-j x c2)
  U-maintains-canonical {.[]} {.(nothing ∷ _ ∷ _)} empty (cons-n c2) = (cons-n c2)
  U-maintains-canonical {.(just x ∷ [])} {.[]} (just-empty x) empty = (just-empty x)
  U-maintains-canonical {.(just x ∷ [])} {.(just x₁ ∷ [])} (just-empty x) (just-empty x₁)
    = (just-empty x₁)
  U-maintains-canonical {.(just x ∷ [])} {.(just x₁ ∷ _)} (just-empty x) (cons-j x₁ c2)
    = (cons-j x₁ c2)
  U-maintains-canonical {.(just x ∷ [])} {.(nothing ∷ _ ∷ _)} (just-empty x) (cons-n c2)
    = cons-j x c2
  U-maintains-canonical {.(just x ∷ _)} {.[]} (cons-j x c1) empty = (cons-j x c1)
  U-maintains-canonical {.(just x ∷ _)} {.(just x₁ ∷ [])} (cons-j x c1) (just-empty x₁)
    = cons-j x₁ (subst Canonical (U-comm' el) c1)
  U-maintains-canonical {.(just x ∷ _)} {.(just x₁ ∷ _)} (cons-j x c1) (cons-j x₁ c2)
    = cons-j x₁ (U-maintains-canonical c1 c2)
  U-maintains-canonical {.(just x ∷ _)} {.(nothing ∷ _ ∷ _)} (cons-j x c1) (cons-n c2)
   = cons-j x (U-maintains-canonical c1 c2)
  U-maintains-canonical {.(nothing ∷ _ ∷ _)} {.[]} (cons-n c1) empty
    = cons-n c1
  U-maintains-canonical {.(nothing ∷ _ ∷ _)} {.(just x ∷ [])} (cons-n c1) (just-empty x)
     = cons-j x c1
  U-maintains-canonical {.(nothing ∷ _ ∷ _)} {.(just x ∷ _)} (cons-n c1) (cons-j x c2)
    = cons-j x (U-maintains-canonical c1 c2)
  U-maintains-canonical {(nothing ∷ (x ∷ l1))} {(nothing ∷ (y ∷ l2))} (cons-n c1) (cons-n c2)
    with cannon-split x y l1 l2
  ... | inj₁ eq rewrite eq = cons-n (subst Canonical eq (U-maintains-canonical c1 c2))
  ... | inj₂ eq rewrite eq = cons-n (subst Canonical eq (U-maintains-canonical c1 c2))
    


  map-injective : ∀{a b}{A : Set a}{B : Set b}
                  → (f : A → B) → (∀{x y} → f x ≡ f y → x ≡ y)
                  → ∀ l1 l2 → List.map f l1 ≡ List.map f l2
                  → l1 ≡ l2
  map-injective f inj [] [] eq = refl
  map-injective f inj [] (x ∷ l2) ()
  map-injective f inj (x ∷ l1) [] ()
  map-injective f inj (x ∷ l1) (x₁ ∷ l2) eq
    rewrite inj (ListP.∷-injectiveˡ eq)
          | map-injective f inj l1 l2 (ListP.∷-injectiveʳ eq)
    = refl

  canonical-and-dom-and-deref-is-eq :
    ∀ {m1 m2}
    → Canonical m1 → Canonical m2
    → Dom' m1 ≡ Dom' m2
    → (∀ k → (k∈1 : k ∈ Dom' m1) → (k∈2 : k ∈ Dom' m2)
       → (deref k m1 k∈1) ≡ (deref k m2 k∈2))
    → m1 ≡ m2
  canonical-and-dom-and-deref-is-eq {[]} {[]} c1 c2 eq-dom eq-range = refl
  canonical-and-dom-and-deref-is-eq {[]} {just x ∷ m2} c1 c2 () eq-range
  canonical-and-dom-and-deref-is-eq {[]} {nothing ∷ r@.(_ ∷ _)} empty (cons-n c2) eq-dom eq-range
     with canonical-and-dom-and-deref-is-eq
           empty c2
           (map-injective suc NatP.suc-injective [] (Dom' r) eq-dom)
           (λ k ())
  ... | ()
  canonical-and-dom-and-deref-is-eq {just x ∷ m1} {[]} c1 c2 () eq-range
  canonical-and-dom-and-deref-is-eq {nothing ∷ r@.(_ ∷ _)} {[]} (cons-n c1) empty eq-dom eq-range
       with canonical-and-dom-and-deref-is-eq
           c1 empty
           (map-injective suc NatP.suc-injective (Dom' r) [] eq-dom)
           (λ k k∈1 ())
  ... | () 
  canonical-and-dom-and-deref-is-eq {just x ∷ m1} {nothing ∷ m2} c1 c2 eq-dom eq-range
    = ⊥-elim (0∈S{l = Dom' m2}
               (subst
                (0 ∈_)
                eq-dom
                (here{x = 0}{xs = (List.map suc (Dom' m1))} refl)))
  canonical-and-dom-and-deref-is-eq {nothing ∷ m1} {just x ∷ m2} c1 c2 eq-dom eq-range
    = ⊥-elim (0∈S{l = Dom' m1}
               (subst
                (0 ∈_)
                (sym eq-dom)
                (here{x = 0}{xs = (List.map suc (Dom' m2))} refl)))
  canonical-and-dom-and-deref-is-eq {just x ∷ .[]} {just x₁ ∷ .[]} (just-empty .x) (just-empty .x₁) eq-dom eq-range
    rewrite (x ≡ x₁ ∋ (eq-range 0 (here refl) (here refl))) = refl
  canonical-and-dom-and-deref-is-eq {just x ∷ .[]} {just x₁ ∷ .[]} (just-empty .x) (cons-j .x₁ empty) eq-dom eq-range
      rewrite (x ≡ x₁ ∋ (eq-range 0 (here refl) (here refl))) = refl
  canonical-and-dom-and-deref-is-eq {just x ∷ .[]} {just x₁ ∷ .(just x₂ ∷ [])} (just-empty .x) (cons-j .x₁ (just-empty x₂)) () eq-range
  canonical-and-dom-and-deref-is-eq {just x ∷ .[]} {just x₁ ∷ .(just x₂ ∷ _)} (just-empty .x) (cons-j .x₁ (cons-j x₂ c2)) () eq-range
  canonical-and-dom-and-deref-is-eq {just x ∷ .[]} {just x₁ ∷ r@.(nothing ∷ _ ∷ _)} (just-empty .x) (cons-j .x₁ (cons-n c2)) eq-dom eq-range
    with canonical-and-dom-and-deref-is-eq empty (cons-n c2)
         (map-injective suc NatP.suc-injective [] (Dom' r) (ListP.∷-injectiveʳ eq-dom))
         (λ k ())
  ... | ()
  canonical-and-dom-and-deref-is-eq {just x ∷ m1} {just x₁ ∷ .[]} (cons-j .x c1) (just-empty .x₁) eq-dom eq-range
    rewrite (canonical-and-dom-and-deref-is-eq c1 empty
             (map-injective suc NatP.suc-injective (Dom' m1) [] (ListP.∷-injectiveʳ eq-dom))
             (λ k k∈1 ()))
          | (x ≡ x₁ ∋ (eq-range 0 (here refl) (here refl)))
    = refl
  canonical-and-dom-and-deref-is-eq {just x ∷ m1} {just x₁ ∷ m2} (cons-j .x c1) (cons-j .x₁ c2) eq-dom eq-range
    rewrite (x ≡ x₁ ∋ (eq-range 0 (here refl) (here refl)))
    = cong (just x₁ ∷_)
           (canonical-and-dom-and-deref-is-eq c1 c2
            (map-injective suc NatP.suc-injective (Dom' m1) (Dom' m2) (ListP.∷-injectiveʳ eq-dom))
            λ {k k∈1 k∈2
               → Eql.subst₂
                  _≡_
                  (deref-∈-irr _ k∈1)
                  (deref-∈-irr _ k∈2)
                  (eq-range (suc k) (n+1∈S{x = just x₁}{m = m1} k∈1) (n+1∈S{x = just x₁}{m = m2} k∈2))})

  canonical-and-dom-and-deref-is-eq {nothing ∷ m1@.(_ ∷ _)} {nothing ∷ m2@.(_ ∷ _)} (cons-n c1) (cons-n c2) eq-dom eq-range
    = cong (nothing ∷_)
           (canonical-and-dom-and-deref-is-eq c1 c2
            (map-injective suc NatP.suc-injective _ _ eq-dom)
            λ {k k∈1 k∈2
               → Eql.subst₂
                  _≡_
                  (deref-∈-irr _ k∈1)
                  (deref-∈-irr _ k∈2)
                  (eq-range (suc k) (n+1∈S{x = nothing}{m = m1} k∈1) (n+1∈S{x = nothing}{m = m2} k∈2))})

  normalize : LMap → ∃ Canonical
  normalize [] = [] , empty
  normalize (x ∷ l)
    with normalize l
  normalize (just x ∷ l)
          | l' , can
   = _ , cons-j x can
  normalize (nothing ∷ l) | [] , can
    = _ , can
  normalize (nothing ∷ l)
    | x ∷ l' , can = _ , cons-n can

