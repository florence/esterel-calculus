{-# OPTIONS --allow-unsolved-metas #-}
module Esterel.Lang.CanFunction.Monotonic where
{-

-}

open import Esterel.Lang.CanFunction.SetSigMonotonic public

open import Esterel.Lang.CanFunction.NonMergePotentialRules
open import Esterel.Lang.CanFunction.CanThetaVisit as V
open import Esterel.Lang.CanFunction
open import Esterel.Lang.CanFunction.Base
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Signal.Ordering as SO
  using (_⊑_)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)
open import utility
open import Esterel.Environment as Env
  using (Env ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap ; isSig∈ ;
         sig ; var ; shr ; Θ)
open import Esterel.Lang
  using (Term)
open Term
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)



open import Data.Sublist as SL
  using (elem ; empty ; Sublist ; sublist ; get)
open import Data.Sublist.Properties as SLP
  using ()

open import Function
  using (_$_ ; _∘_ ; flip ; _∋_ ; id)
open import Relation.Binary.PropositionalEquality
  using (refl ; _≡_ ; subst ; trans ; cong ; sym ; inspect ; [_] ; module ≡-Reasoning)
open import Data.Product as Prod
  using (Σ ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_ ; ∃-syntax ; Σ-syntax)
open import Data.List as List
  using ([])
open import Level
  hiding (suc)
open import Relation.Binary
  using (Rel)
open import Relation.Unary
  using (_⊆′_)
open import Relation.Nullary
  using (¬_ ; Dec)
open import Relation.Nullary.Negation
  using (contradiction)
open Dec
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List.Any as Any

open import Data.List.Any.Properties as AnyP
  using (++⁻)
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ)
open import Data.List.Properties as ListP
  using (map-id ; map-compose ; map-cong)
open import Data.Nat as Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_)
open import Data.Sum
  using (inj₁ ; inj₂)


open ≡-Reasoning

-- does one environment have less information that the other
infix 6 _⊑θ_
_⊑θ_ : Rel Env 0ℓ
θ1 ⊑θ θ2 = ∀ S → (∈1 : Env.isSig∈ S θ1) → ∃[ ∈2 ] (Env.sig-stats {S} θ1 ∈1 ⊑ Env.sig-stats {S} θ2 ∈2)

⊑θ-refl : ∀ θ → θ ⊑θ θ
⊑θ-refl θ S S∈ = S∈ , SO.refl

⊑θ-empty : ∀ θ → Env.[]env ⊑θ θ
⊑θ-empty θ _ ()

⊑θ-extend-both : ∀{θ1 θ2}
                 → θ1 ⊑θ θ2
                 → ∀ S stat
                 → (θ1 ← [S]-env-build S stat)
                   ⊑θ
                   (θ2 ← [S]-env-build S stat)
⊑θ-extend-both{θ1}{θ2} f S stat S' S'∈
  with S Signal.≟ S'
... | yes refl
  rewrite Env.sig-stats-1map-right-← S stat θ1 S'∈
  = (Env.sig-∈-single-right-← S stat θ2)
    , subst
       (stat ⊑_)
       (sym $ Env.sig-stats-1map-right-← S stat θ2 (Env.sig-∈-single-right-← S stat θ2))
       SO.refl
... | no ¬refl
   = Env.sig-←-monoˡ S' θ2 ([S]-env-build S stat) (proj₁ inner∈,inner⊑)
     , {!subst
         (Env.sig-stats{S'} θ1 S'∈2 ⊑_)
         (Env.sig-←-∉-irr-stats' S' θ2 ([S]-env-build S stat) (proj₁ inner∈,inner⊑)
             (Env.sig-∉-single S' S stat (¬refl ∘ sym))
             (Env.sig-←-monoˡ S' θ2 ([S]-env-build S stat) (proj₁ inner∈,inner⊑)))
         (proj₂ inner∈,inner⊑)!}
   where
    S'∈2 : Env.isSig∈ S' θ1
    S'∈2 = {!!}
    inner∈,inner⊑ = f S' {!!}


⊑θ-extendˡ : ∀{θ1 θ2}
            → θ1 ⊑θ θ2 → ∀ S S∈
            → (θ1 ← [S]-env-build S (Env.sig-stats{S} θ2 S∈)) ⊑θ θ2 
⊑θ-extendˡ{θ1}{θ2} θ1⊑θ2 S S∈
  = subst
    ((θ1 ← [S]-env-build S (Env.sig-stats{S} θ2 S∈)) ⊑θ_)
    (begin
      (θ2 ← [S]-env-build S (Env.sig-stats{S} θ2 S∈))
      ≡⟨ sym (Env.sig-set=← θ2 S (Env.sig-stats{S} θ2 S∈) S∈) ⟩
      (Env.set-sig {S} θ2 S∈ (Env.sig-stats{S} θ2 S∈))
      ≡⟨ (Env.sig-re-set-is-eq θ2 S (Env.sig-stats{S} θ2 S∈) S∈ refl) ⟩
      θ2 ∎)
    (⊑θ-extend-both{θ1}{θ2} θ1⊑θ2 S (Env.sig-stats{S} θ2 S∈)) 
  -- 

⊑θ-extend : ∀{θ1 θ2}
            → θ1 ⊑θ θ2 → ∀ S stat
            → (∀ S∈ → Env.sig-stats{S} θ1 S∈ ⊑ stat)
            → θ1 ⊑θ (θ2 ← ([S]-env-build S stat))
⊑θ-extend{θ1}{θ2} θ1⊑θ2 S stat S∈⊑ S' S'∈
 with S Signal.≟ S'
... | yes refl
    = Env.sig-∈-single-right-← S stat θ2
      , subst
         (Env.sig-stats{S} θ1 S'∈ ⊑_)
         (sym $ Env.sig-stats-1map-right-← S stat θ2 $ Env.sig-∈-single-right-← S stat θ2)
         (S∈⊑ S'∈)
... | no ¬refl
  = Env.sig-←-monoˡ S' θ2 ([S]-env-build S stat) (proj₁ inner∈,inner⊑)
    , subst
       (Env.sig-stats{S'} θ1 S'∈ ⊑_)
       (Env.sig-←-∉-irr-stats' S' θ2 ([S]-env-build S stat) (proj₁ inner∈,inner⊑)
           (Env.sig-∉-single S' S stat (¬refl ∘ sym))
           (Env.sig-←-monoˡ S' θ2 ([S]-env-build S stat) (proj₁ inner∈,inner⊑)))
       (proj₂ inner∈,inner⊑)
  where
    inner∈,inner⊑ = θ1⊑θ2 S' S'∈

⊑θ-to-⊑ : ∀{θ1 θ2} → θ1 ⊑θ θ2
        → ∀ S S∈2 S∈ → Env.sig-stats{S} θ1 S∈ ⊑ Env.sig-stats{S} θ2 S∈2
⊑θ-to-⊑ {θ1}{θ2} θ1⊑θ2 S S∈2 S∈ with
   θ1⊑θ2 S S∈ 
... | a , ⊑res  = subst
                   (λ x →  Env.sig-stats{S} θ1 S∈ ⊑ Env.sig-stats{S} θ2 x)
                   (Env.sig∈-eq{S}{θ2} a S∈2)
                   ⊑res

canₛ-add-sig-monotonic : ∀ p θ S status →
  ∀ S' →
    S' ∈ Canₛ p (θ ← [S]-env-build S status) →
    S' ∈ Canₛ p (θ ← [S]-env S)
canₛ-add-sig-monotonic p θ S status
  with Env.sig-←-monoʳ S ([S]-env S) θ $ Env.sig-∈-single S Signal.unknown
... | ∈2
  rewrite 
    begin
       (θ ← [S]-env-build S status)
       ≡⟨ sym $ Env.sig-single-←-←-overwrite θ S Signal.unknown status  ⟩
       ((θ ← [S]-env S) ← [S]-env-build S status)
       ≡⟨ sym $ Env.sig-set=← (θ ← [S]-env S) S status ∈2 ⟩
       (Env.set-sig{S} (θ ← [S]-env S) ∈2 status) ∎
  = (canₛ-set-sig-monotonic p S (θ ← [S]-env S) ∈2 status (Env.sig-stats-1map-right-← S Signal.unknown θ ∈2)) 


canₛ-unknown-lemma : ∀ p θ S 
                   → ¬ isSig∈ S θ
                   → ∀ S' stat
                   → S' ∈ Canₛ p (θ ← [S]-env-build S stat)
                   → S' ∈ Canₛ p θ 
canₛ-unknown-lemma  p θ S S∉ S' stat  S'∈
  rewrite can-is-unknown-lemma p θ S S∉
  = canₛ-add-sig-monotonic p θ S stat S' S'∈

Canₛ-sig-set-monotonic : ∀  θ p S status
  → (∀ S∈ → (Env.sig-stats {S} θ S∈ ⊑ status))
  → (_∈ (Canₛ p (θ ← [S]-env-build S status))) ⊆′ (_∈ (Canₛ p θ))
Canₛ-sig-set-monotonic θ p S status lat
  with Env.Sig∈ S θ
... | no S∉ = flip (canₛ-unknown-lemma p θ S S∉) status
... | yes S∈
  with Env.sig-stats {S} θ S∈ | lat S∈ | inspect (Env.sig-stats {S} θ) S∈
... | .(Env.sig-stats {S} θ S∈) | SO.refl | [ refl ]
   rewrite sym $ Env.sig-set=← θ S status S∈
         | cong (λ x → (_∈ (Canₛ p x)) ⊆′ (_∈ (Canₛ p θ)))  (Env.sig-re-set-is-eq θ S (Env.sig-stats {S} θ S∈) S∈ refl)
  =  λ a b → b
... | .Signal.unknown | SO.uknw | [ eq ]
  rewrite sym $ Env.sig-set=← θ S status S∈
  = canₛ-set-sig-monotonic p S θ S∈ status eq

mono-neq-extend : ∀ θ S status
     → (∀ S∈ → (Env.sig-stats {S} θ S∈ ⊑ status))
     → ∀ S' stat'
     → ¬ S' ≡ S
     → (∀ S∈ → (Env.sig-stats {S} (θ ← [S]-env-build S' stat') S∈ ⊑ status))
mono-neq-extend θ S status S∈⇒⊑ S' stat' S'≠S S∈
  with Env.sig-←⁻{θ}{[S]-env-build S' stat'} S S∈
... | inj₂ S∈⊥ = contradiction S∈⊥ (Env.sig-∉-single S S' stat' (S'≠S ∘ sym))
... | inj₁ S∈θ
  =  subst
      (_⊑ status)
      (Env.sig-←-∉-irr-stats' S θ ([S]-env-build S' stat')
          S∈θ (Env.sig-∉-single S S' stat' (S'≠S ∘ sym)) S∈)
      (S∈⇒⊑ S∈θ)

mutual
  Canθ-visit-rec-step-consistent :
    ∀ {off} sigs θ p
    → (slo : Sublist (SigMap.keys+∈ sigs) (suc off))
    → (sli : Sublist (SigMap.keys+∈ sigs) off)
    → ∀ S1 stat 
    → (∀ S∈ → (Env.sig-stats {S1} θ S∈ ⊑ stat))
    → (proj₁ (Canθ-visit-rec-step sigs θ p slo sli))
      ⊑
      (proj₁ (Canθ-visit-rec-step sigs (θ ← ([S]-env-build S1 stat)) p slo sli))
  Canθ-visit-rec-step-consistent sigs θ p l@(elem n n<l slo) sli S1 stat ∈⊑ 
    with SLP.sublist-irrelevant slo sli
       | SigMap.lookup{k = (proj₁ (get l)) ₛ} sigs (proj₂ (get l))
  ... | refl | Signal.present = SO.refl
  ... | refl | Signal.absent = SO.refl
  ... | refl | Signal.unknown
    with any (_≟_  (proj₁ (get l)))
             (proj₁ (revisit (θ ← ([S]-env-build ((proj₁ (get l)) ₛ) Signal.unknown))))
       | any (_≟_  (proj₁ (get l)))
             (proj₁ (revisit ((θ ← ([S]-env-build S1 stat)) ← ([S]-env-build ((proj₁ (get l)) ₛ) Signal.unknown))))
      where revisit = (λ θ → SL.visit (V.visit-lift-sig{sigs = sigs} (V.Canθ-lookup sigs)) (Can p) θ sli)
  ... | yes _ | yes _  = SO.refl 
  ... | yes _ | no _  = SO.uknw 
  ... | no _  | no _ = SO.refl
  ... | no ¬∈  | yes ∈
    with ((proj₁ (get l)) ₛ) Signal.≟ S1
  ... | yes refl
    rewrite Env.sig-single-←-←-overwrite θ S1 stat Signal.unknown
    =  (contradiction ∈) ¬∈
  ... | no ¬refl
    rewrite
       (sym $ Env.←-assoc-comm θ ([S]-env-build ((proj₁ (get l)) ₛ) Signal.unknown) ([S]-env-build S1 stat)
           $ Env.sig-single-noteq-distinct ((proj₁ (get l)) ₛ) Signal.unknown S1 stat
           $ λ x → ¬refl (trans (cong Signal.wrap x) Signal.unwrap-inverse))
    = contradiction
        (Canθₛ-visit-sig-set-monotonic-rec sigs
                                           (θ ← ([S]-env-build ((proj₁ (get l)) ₛ) Signal.unknown))
                                           p
                                           S1
                                           stat
                                           (mono-neq-extend θ S1 stat ∈⊑ ((proj₁ (get l)) ₛ) Signal.unknown ¬refl)
                                           sli
                                           (proj₁ (get l)) ∈)
        ¬∈ 
  
  Canθₛ-visit-sig-set-monotonic-rec : ∀{off} sigs θ p S status
    → (∀ S∈ → (Env.sig-stats {S} θ S∈ ⊑ status))
    → (sl : Sublist (SigMap.keys+∈ sigs) off)
    → ((_∈ (Canθₛ-visit-rec sigs p sl (θ ← [S]-env-build S status)))
      ⊆′
      (_∈ (Canθₛ-visit-rec sigs p sl θ)))
  Canθₛ-visit-sig-set-monotonic-rec sigs θ p S_set stat lat Sublist.empty S' S'∈Can←
    = Canₛ-sig-set-monotonic θ p S_set stat lat S' S'∈Can←
  Canθₛ-visit-sig-set-monotonic-rec sigs θ p Ss stat ⊑l l@(Sublist.elem n n<l sl) S' S'∈Can←
    with Canθ-visit-rec-step sigs (θ ← [S]-env-build Ss stat) p l sl
       | Canθ-visit-rec-step sigs θ p l sl
       | Canθ-visit-rec-step-consistent sigs θ p l sl Ss stat ⊑l
  ... | (set , eq , setsub)  | (set1 , eq1 , set1sub) | set1⊑set
    with (Signal.wrap (proj₁ (get l))) Signal.≟ Ss
  ... | yes refl
   = (subst
        (λ x → S' ∈ proj₁ x)
        (sym $ eq1)
        $ Canθₛ-visit-sig-set-monotonic-rec sigs (θ ← [S]-env-build Ss set1) p Ss set
          S∈⊑2
          sl S' S'∈3 ) 
    where
      S∈⊑2 : ∀ S∈ → Env.sig-stats {Ss} (θ ← [S]-env-build Ss set1) S∈ ⊑ set
      S∈⊑2 S∈ rewrite Env.sig-stats-1map-right-← Ss set1 θ S∈
         = set1⊑set
      S'∈2 =
        subst
        id
        (begin
         (S' ∈ (Canθₛ-visit-rec sigs p l (θ ← [S]-env-build Ss stat)))
         ≡⟨ cong (λ x → (S' ∈ proj₁ x)) eq ⟩
         (S' ∈ (Canθₛ-visit-rec sigs p sl ((θ ← [S]-env-build Ss stat) ← [S]-env-build Ss set)))
         ≡⟨ cong (λ t →  (S' ∈ (Canθₛ-visit-rec sigs p sl t)))
               $ Env.sig-single-←-←-overwrite θ Ss stat set ⟩
         (S' ∈ (Canθₛ-visit-rec sigs p sl (θ ← [S]-env-build Ss set))) ∎)
        S'∈Can←
      S'∈3 =
        subst
        id
        (begin
         (S' ∈ (Canθₛ-visit-rec sigs p sl (θ ← [S]-env-build Ss set)))
         ≡⟨ cong (λ t →  (S' ∈ (Canθₛ-visit-rec sigs p sl t)))
               $ sym $ Env.sig-single-←-←-overwrite θ Ss set1 set ⟩
         (S' ∈ (Canθₛ-visit-rec sigs p sl ((θ ← [S]-env-build Ss set1) ← [S]-env-build Ss set)))∎)
        S'∈2
        
  ... | no ¬refl
    = subst
       id
       (cong (S' ∈_ ∘ proj₁) $ sym eq1)
       step2
       
        where
         Shere = ((proj₁ (get l)) ₛ)
         θset = (θ ← [S]-env-build Shere set)
         θset1 = (θ ← [S]-env-build Shere set1)
         θset1set = (θset1 ← [S]-env-build Shere set)
         mono1 = ((mono-neq-extend θ Ss stat ⊑l) Shere set ¬refl)
         S'∈x : S' ∈ (Canθₛ-visit-rec sigs p sl
                       ((θ ← [S]-env-build Shere set)
                           ← [S]-env-build Ss stat))
         S'∈x = subst
                 id
                 ((begin
                 ((S' ∈ (Canθₛ-visit-rec sigs p l
                       ((θ ← [S]-env-build Ss stat)))))
                 ≡⟨ cong (S' ∈_ ∘ proj₁) eq ⟩
                 (S' ∈ (Canθₛ-visit-rec sigs p sl
                       ((θ ← [S]-env-build Ss stat)
                           ← [S]-env-build Shere set)))
                 ≡⟨ (cong (λ θ → S' ∈ (Canθₛ-visit-rec sigs p sl θ))
                       $ sym
                       $ Env.←-assoc-comm θ ([S]-env-build Shere set) ([S]-env-build Ss stat)
                       $ Env.sig-single-noteq-distinct Shere set Ss stat
                       $ λ x → ¬refl (trans (cong Signal.wrap x) Signal.unwrap-inverse)) ⟩
                 (S' ∈ (Canθₛ-visit-rec sigs p sl
                       (θset ← [S]-env-build Ss stat))) ∎))
                 S'∈Can←


         step1 : (S' ∈ (Canθₛ-visit-rec sigs p sl θset))
         step1
            = (Canθₛ-visit-sig-set-monotonic-rec sigs θset p Ss stat mono1 sl S' S'∈x)
         step1·5 : (S' ∈ (Canθₛ-visit-rec sigs p sl θset1set))
         step1·5 rewrite Env.sig-single-←-←-overwrite θ Shere set1 set
            = step1 
         ⊑2 : ∀ S∈ → Env.sig-stats {Shere} θset1 S∈ ⊑ set
         ⊑2 S∈ rewrite Env.sig-stats-1map-right-← Shere set1 θ S∈
            = set1⊑set
         step2 : (S' ∈ (Canθₛ-visit-rec sigs p sl θset1))
         step2
            = (Canθₛ-visit-sig-set-monotonic-rec sigs θset1 p Shere set ⊑2 sl S' step1·5)

Canθₛ-visit-sig-set-monotonic : ∀ sigs θ p S status
  → (∀ S∈ → (Env.sig-stats {S} θ S∈ ⊑ status))
  → (_∈ (Canθₛ-visit p sigs (θ ← [S]-env-build S status))) ⊆′ (_∈ (Canθₛ-visit p sigs θ))
Canθₛ-visit-sig-set-monotonic sigs θ p S_set stat lat
  =   Canθₛ-visit-sig-set-monotonic-rec sigs θ p S_set stat lat $ (SL.sublist (SigMap.keys+∈ sigs)) 

subdomain-copy : ∀{off} sigs → Env
  → SubDomain sigs off
  → Env
subdomain-copy _ θ empty = θ
subdomain-copy sigs θ l@(elem n n<l sl)
  = (subdomain-copy sigs θ sl)
    ←
    [S]-env-build (subdomain-sig sigs l) (subdomain-lookup sigs l)

subdomain-copy-useless : ∀ θ1 θ2
  → subdomain-copy (sig θ2) θ1 (subdomain (sig θ2))
     ≡
    (Θ (sig θ2) (shr θ1) (var θ1))
subdomain-copy-useless θ1 θ2 = {!!}

subdomain-copy-maintains-⊑ : ∀{off θ1 θ2}
  → θ1 ⊑θ θ2 
  → (sl : SubDomain (sig θ2) off)
  → (subdomain-copy (sig θ2) θ1 sl) ⊑θ θ2 
subdomain-copy-maintains-⊑ θ1⊑θ2 empty = θ1⊑θ2
subdomain-copy-maintains-⊑{_}{θ1}{θ2} θ1⊑θ2 l@(elem n n<l sl)
  = ⊑θ-extendˡ{subdomain-copy (sig θ2) θ1 sl}{θ2}
              (subdomain-copy-maintains-⊑ {_} {θ1} {θ2} θ1⊑θ2 sl)
              (subdomain-sig (sig θ2) l)
              (subdomain-∈ (sig θ2) l) 

Canₛ-θ-monotonic-step : ∀{off} θ1 θ2 p
  → θ1 ⊑θ θ2
  → (sl : SubDomain (sig θ2) off)
  → (_∈ (Canₛ p (subdomain-copy (sig θ2) θ1 sl))) ⊆′ (_∈ (Canₛ p θ1))
Canₛ-θ-monotonic-step θ1 θ2 p θ1⊑θ2 empty S' S'∈ = S'∈
Canₛ-θ-monotonic-step θ1 θ2 p θ1⊑θ2 l@(elem n n<l sl) S' S'∈
  = Canₛ-θ-monotonic-step θ1 θ2 p θ1⊑θ2 sl S'
    $ Canₛ-sig-set-monotonic  (subdomain-copy (sig θ2) θ1 sl) p
          (subdomain-sig (sig θ2) l) (subdomain-lookup (sig θ2) l)
            (⊑θ-to-⊑ {(subdomain-copy (sig θ2) θ1 sl)} {θ2}
              (subdomain-copy-maintains-⊑{_}{θ1}{θ2} θ1⊑θ2 sl)
              (subdomain-sig (sig θ2) l)
              (subdomain-∈ (sig θ2) l)) S' S'∈ 

Canₛ-θ-monotonic : ∀ θ1 θ2 p
  → θ1 ⊑θ θ2
  → ((_∈ (Canₛ p θ2)) ⊆′ (_∈ (Canₛ p θ1)))
Canₛ-θ-monotonic θ1 θ2 p θ1⊑θ2 S' S'∈
  = Canₛ-θ-monotonic-step θ1 θ2 p θ1⊑θ2 (subdomain (sig θ2)) S'
   $ (subst
      id
      (begin
      S' ∈ Canₛ p θ2
      ≡⟨ cong (S' ∈_ ∘ proj₁)
             $ can-shr-var-irr p θ2 (Θ (sig θ2) (shr θ1) (var θ1)) refl ⟩
      S' ∈ Canₛ p (Θ (sig θ2) (shr θ1) (var θ1))
      ≡⟨ cong (S' ∈_ ∘ (Canₛ p)) $ sym $ subdomain-copy-useless θ1 θ2 ⟩
      S' ∈ Canₛ p (subdomain-copy (sig θ2) θ1 (subdomain (sig θ2))) ∎)
      S'∈)

Canθₛ-visit-θ-monotonic-rec : ∀{off} sigs θ1 θ2 p
  → θ1 ⊑θ θ2
  → (sl : Sublist (SigMap.keys+∈ sigs) off)
  → ((_∈ (Canθₛ-visit-rec sigs p sl θ2))
     ⊆′
    (_∈ (Canθₛ-visit-rec sigs p sl θ1)))

Canθₛ-visit-θ-monotonic-rec sigs θ1 θ2 p θ1⊑θ2 empty S S∈
  = Canₛ-θ-monotonic θ1 θ2 p θ1⊑θ2 S S∈ 
Canθₛ-visit-θ-monotonic-rec sigs θ1 θ2 p θ1⊑θ2 (elem n n<l sl) S S∈
  = {!Canθₛ-visit-θ-monotonic-rec sigs θ1 θ2 p θ1⊑θ2 sl S!}

Canθₛ-visit-θ-monotonic : ∀ sigs θ1 θ2 p
  → θ1 ⊑θ θ2
  → ((_∈ (Canθₛ-visit p sigs θ2))
     ⊆′
    (_∈ (Canθₛ-visit p sigs θ1)))
Canθₛ-visit-θ-monotonic sigs θ1 θ2 p θ1⊑θ2
  = Canθₛ-visit-θ-monotonic-rec sigs θ1 θ2 p θ1⊑θ2
    $ sublist (SigMap.keys+∈ sigs)


    
