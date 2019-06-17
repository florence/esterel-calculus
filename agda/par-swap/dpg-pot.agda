module par-swap.dpg-pot where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym)
open import Data.Maybe using ()
open import Data.List.Any using (here ; there)
open import Data.List.Any.Properties using ( ++-comm ; ++⁻ ; ++⁺ˡ ; ++⁺ʳ )
open import Data.Nat as Nat using (ℕ)

open import par-swap
open import par-swap.properties

open import Esterel.Lang.CanFunction
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.CanFunction.Plug
open import Esterel.Environment as Env
open import Esterel.Context

open import utility

open import sn-calculus
open import context-properties -- get view, E-views
open import sn-calculus-props

open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)



canₛ-par :
  ∀ r₁ r₂ -> ∀ (θ : Env) (S : ℕ) →
   S ∈ Canₛ (r₂ ∥ r₁) θ →
   S ∈ Canₛ (r₁ ∥ r₂) θ
canₛ-par r₁ r₂ θ S S∈r₂∥r₁
 = ++-comm (proj₁ (Can r₂ θ)) (proj₁ (Can r₁ θ)) S∈r₂∥r₁

canₖ-par :
  ∀ r₁ r₂ -> ∀ (θ : Env) (k : Code) →
    k ∈ Canₖ (r₂ ∥ r₁) θ →
    k ∈ Canₖ (r₁ ∥ r₂) θ
canₖ-par
 = \ {r₁ r₂ θ S S∈r₂∥r₁ ->
      thing S
      (proj₁ (proj₂ (Can r₁ θ)))
      (proj₁ (proj₂ (Can r₂ θ)))
      S∈r₂∥r₁}  where

 simplify-foldr++-[] : ∀ (l2 : List Code) ->
   (Data.List.foldr{A = (List Code)}
     _++_
     []
     (Data.List.map (λ (k : Code) → []) l2)) ≡ []
 simplify-foldr++-[] [] = refl
 simplify-foldr++-[] (x ∷ l2) = simplify-foldr++-[] l2

 whatevs-left : ∀ S (whatevs : Code -> Code) l1 l2 ->
   Data.List.Any.Any (_≡_ S)
     (Data.List.foldr _++_ []
      (Data.List.map (λ k → Data.List.map (Code._⊔_ k) l2) l1))
   ->
   Data.List.Any.Any (_≡_ S)
     (Data.List.foldr _++_ []
      (Data.List.map (λ k → (whatevs k) ∷ Data.List.map (Code._⊔_ k) l2) l1))
 whatevs-left S whatevs [] l2 ()
 whatevs-left S whatevs (x ∷ l1) l2 blob
  with ++⁻ (Data.List.map (Code._⊔_ x) l2) blob
 ... | inj₁ y = there (++⁺ˡ y)
 ... | inj₂ y
  with whatevs-left S whatevs l1 l2 y
 ... | R = there (++⁺ʳ (Data.List.map (Code._⊔_ x) l2)  R)

 whatevs-right :
   ∀ S (whatevs : Code -> List Code) x l1 ->
   Data.List.Any.Any (_≡_ S) (Data.List.map (Code._⊔_ x) l1)
   ->
   Data.List.Any.Any (_≡_ S)
      (Data.List.foldr _++_ []
       (Data.List.map (λ k → (k Code.⊔ x) ∷ whatevs k)
        l1))
 whatevs-right S whatevs x [] blob = blob
 whatevs-right S whatevs x (x₁ ∷ l1) (here px)
  rewrite px = here (Code.⊔-comm x x₁)
 whatevs-right S whatevs x (x₁ ∷ l1) (there blob)
  = there (++⁺ʳ (whatevs x₁) (whatevs-right S whatevs x l1 blob))

 thing : ∀ S l1 l2 ->
    Data.List.Any.Any (_≡_ S)
     (Data.List.foldr _++_ []
      (Data.List.map
       (λ k → Data.List.map (Code._⊔_ k) l1)
       l2))
    ->
    Data.List.Any.Any (_≡_ S)
     (Data.List.foldr _++_ []
      (Data.List.map
       (λ k → Data.List.map (Code._⊔_ k) l2)
       l1))

 thing S l1 [] blob
   rewrite simplify-foldr++-[] l1
   = blob

 thing S l1 (x ∷ l2) blob
  with ++⁻ (Data.List.map (Code._⊔_ x) l1) blob
 thing S l1 (x ∷ l2) _ | inj₁ y =
   whatevs-right S (λ { k → Data.List.map (Code._⊔_ k) l2 }) x l1 y
 thing S l1 (x ∷ l2) _ | inj₂ y =
   whatevs-left S (\ { k ->  (k Code.⊔ x)}) l1 l2 (thing S l1 l2 y)

canₛₕ-par :
  ∀ r₁ r₂ -> ∀ (θ : Env) →
   Canₛₕ (r₂ ∥ r₁) θ ⊆¹ Canₛₕ (r₁ ∥ r₂) θ
canₛₕ-par r₁ r₂ θ S S∈r₂∥r₁
 = ++-comm (proj₂ (proj₂ (Can r₂ θ))) (proj₂ (proj₂ (Can r₁ θ))) S∈r₂∥r₁

canθₛ-C-par : ∀ sigs S'' -> ∀ {C p r₁ r₂} ->
    p ≐ C ⟦ r₁ ∥ r₂ ⟧c ->
    ∀ {θ} S' ->
     S' ∉ Canθₛ sigs S'' p θ ->
     S' ∉ Canθₛ sigs S'' (C ⟦ r₂ ∥ r₁ ⟧c) θ
canθₛ-C-par sigs S'' {C} {p} {r₁} {r₂} pC {θ} S' S'∉Canθₛ[p] S'∈Canθₛ[C⟦r₂∥r₁⟧c]
  with canθₛ-plug S'' sigs C (r₁ ∥ r₂) (r₂ ∥ r₁)
                 (canₛ-par r₁ r₂) (canₖ-par r₁ r₂) θ S'
... |  r₂r₁->r₁r₂ rewrite sym (unplugc pC) = S'∉Canθₛ[p] (r₂r₁->r₁r₂ S'∈Canθₛ[C⟦r₂∥r₁⟧c])

canθₛₕ-C-par : ∀ sigs S' -> ∀ {C p r₁ r₂} ->
    p ≐ C ⟦ r₁ ∥ r₂ ⟧c ->
    ∀ {θ} s' ->
     s' ∉ Canθₛₕ sigs S' p θ ->
     s' ∉ Canθₛₕ sigs S' (C ⟦ r₂ ∥ r₁ ⟧c) θ
canθₛₕ-C-par sigs S' {C} {p} {r₁} {r₂} pC {θ} s' s'∉Canθₛₕ[p] s'∈Canθₛₕ[C⟦r₂∥r₁⟧c]
  with canθₛₕ-plug S' sigs C (r₁ ∥ r₂) (r₂ ∥ r₁)
                  (canₛₕ-par r₁ r₂) (canₖ-par r₁ r₂) (canₛ-par r₁ r₂) θ s'
... | r₂r₁->r₁r₂ rewrite sym (unplugc pC) = s'∉Canθₛₕ[p] (r₂r₁->r₁r₂ s'∈Canθₛₕ[C⟦r₂∥r₁⟧c])


DPG-pot-view :
 ∀ {C r₁ r₂ p q θ θ' A A'} ->
  p ≐ C ⟦ r₁ ∥ r₂ ⟧c ->
  (psn⟶₁q : ρ⟨ θ , A ⟩· p sn⟶₁ ρ⟨ θ' , A' ⟩· q) ->
  (p≡q : p ≡ q) ->
  (A≡A' : A ≡ A') ->
  ->pot-view psn⟶₁q p≡q A≡A' ->
  Σ[ dd′ ∈ Term × Term ]
  (ρ⟨ θ , A ⟩· C ⟦ r₂ ∥ r₁ ⟧c sn⟶ (proj₂ dd′))
  ×
  ((proj₂ dd′) sn⟶* (proj₁ dd′))
  ×
  ((ρ⟨ θ' , A' ⟩· q) ∥R* (proj₁ dd′))
DPG-pot-view pC (ris-present S∈ x x₁) p≡q A≡A' ()
DPG-pot-view pC (ris-absent S∈ x x₁) p≡q A≡A' ()
DPG-pot-view pC (remit S∈ ¬S≡a x) p≡q A≡A' ()
DPG-pot-view pC (rraise-shared e' x) p≡q A≡A' ()
DPG-pot-view pC (rset-shared-value-old e' s∈ x x₁) p≡q A≡A' ()
DPG-pot-view pC (rset-shared-value-new e' s∈ x x₁) p≡q A≡A' ()
DPG-pot-view pC (rraise-var e' x₁) p≡q A≡A' ()
DPG-pot-view pC (rset-var x∈ e' x₁) p≡q A≡A' ()
DPG-pot-view pC (rif-false x∈ x₁ x₂) p≡q A≡A' ()
DPG-pot-view pC (rif-true x∈ x₁ x₂) p≡q A≡A' ()
DPG-pot-view pC (rabsence{θ}{_}{S} S∈ x x₁) .refl .refl (vabsence .S .S∈ .x .x₁)
  = _ , rcontext [] dchole
         (rabsence{θ}{_}{S} S∈ x (canθₛ-C-par (sig θ) 0 pC (Signal.unwrap S) x₁)) ,
    rrefl ,
    Context1-∥R* (cenv _ _) (∥Rn (∥Rstep pC) ∥R0)
DPG-pot-view pC (rreadyness{θ}{_}{s} s∈ x x₁) .refl .refl (vreadyness .s .s∈ .x .x₁)
  = _ , rcontext [] dchole
         (rreadyness{s = s} s∈ x (canθₛₕ-C-par (sig θ) 0 pC (SharedVar.unwrap s) x₁)) ,
    rrefl ,
    Context1-∥R* (cenv _ _) (∥Rn (∥Rstep pC) ∥R0)
DPG-pot-view pC (rmerge x) p≡q A≡A' ()

