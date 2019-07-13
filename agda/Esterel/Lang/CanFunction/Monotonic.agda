module Esterel.Lang.CanFunction.Monotonic where
{-

-}

open import Esterel.Lang.CanFunction.SetSigMonotonic public

open import Esterel.Lang.CanFunction.NonMergePotentialRules
open import Esterel.Lang.CanFunction.CanThetaVisit as V
  using (Canθ-visit ; Canθ-visit≡Canθ ; Canθₛ-visit ; Canθₛ-visit-rec ; Canθ-visit-rec-step )
open import Esterel.Lang.CanFunction
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
  using (Env ; _←_ ; Dom ; module SigMap ; module ShrMap ; module VarMap ; isSig∈)
open Env.Env
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
    = {!!}
  
  {-
  Canθₛ-visit-sig-set-monotonic-rec sigs θ p S_set stat lat Sublist.empty
    = Canₛ-sig-set-monotonic θ p S_set stat lat
  Canθₛ-visit-sig-set-monotonic-rec sigs θ p Ss stat ⊑ l@(Sublist.elem n n<l sl)
   with SigMap.lookup{k = proj₁ (get l) ₛ} sigs (proj₂ (get l))
  Canθₛ-visit-sig-set-monotonic-rec sigs θ p Ss stat ⊑ l@(Sublist.elem n n<l sl) | Signal.absent
    with (Signal.wrap (proj₁ (get l))) Signal.≟ Ss
  ... | yes refl
     rewrite Env.sig-single-←-←-overwrite θ Ss stat Signal.absent
    = λ x x₁ → x₁
  ... | no ¬eq
    rewrite sym $ Env.←-assoc-comm θ ([S]-env-build ((proj₁ (get l)) ₛ) Signal.absent) ([S]-env-build Ss stat)
                $ (Env.sig-single-noteq-distinct ((proj₁ (get l)) ₛ) Signal.absent Ss stat λ x → ¬eq (trans (cong Signal.wrap x) Signal.unwrap-inverse))
    = Canθₛ-visit-sig-set-monotonic-rec sigs (θ ← [S]-env-build ((proj₁ (get l)) ₛ) set) p Ss stat
       ((mono-extend θ Ss stat ⊑) ((proj₁ (get l)) ₛ) set ¬eq)
      sl
    where set = Signal.absent
  Canθₛ-visit-sig-set-monotonic-rec sigs θ p Ss stat ⊑ l@(Sublist.elem n n<l sl) | Signal.present
    with (Signal.wrap (proj₁ (get l))) Signal.≟ Ss
  ... | yes refl
     rewrite Env.sig-single-←-←-overwrite θ Ss stat Signal.present
    = λ x x₁ → x₁
  ... | no ¬eq
    rewrite sym $ Env.←-assoc-comm θ ([S]-env-build ((proj₁ (get l)) ₛ) Signal.present) ([S]-env-build Ss stat)
                $ (Env.sig-single-noteq-distinct ((proj₁ (get l)) ₛ) Signal.present Ss stat λ x → ¬eq (trans (cong Signal.wrap x) Signal.unwrap-inverse))
    = Canθₛ-visit-sig-set-monotonic-rec sigs (θ ← [S]-env-build ((proj₁ (get l)) ₛ) set) p Ss stat
       ((mono-extend θ Ss stat ⊑) ((proj₁ (get l)) ₛ) set ¬eq)
      sl
    where set = Signal.present
  Canθₛ-visit-sig-set-monotonic-rec sigs θ p Ss stat ⊑ l@(Sublist.elem n n<l sl) | Signal.unknown
    with (Signal.wrap (proj₁ (get l))) Signal.≟ Ss
  ... | yes refl = {!
     rewrite Env.sig-single-←-←-overwrite θ Ss stat Signal.unknown
    = λ x x₁ → x₁!}
  ... | no ¬eq = {!
    rewrite sym $ Env.←-assoc-comm θ ([S]-env-build ((proj₁ (get l)) ₛ) Signal.unknown) ([S]-env-build Ss stat)
                $ (Env.sig-single-noteq-distinct ((proj₁ (get l)) ₛ) Signal.unknown Ss stat λ x → ¬eq (trans (cong Signal.wrap x) Signal.unwrap-inverse))
    = Canθₛ-visit-sig-set-monotonic-rec sigs (θ ← [S]-env-build ((proj₁ (get l)) ₛ) set) p Ss stat
       ((mono-extend θ Ss stat ⊑) ((proj₁ (get l)) ₛ) set ¬eq)
      sl
    where set = Signal.unknown !}
  -}
  {-
    with any (Nat._≟_ (proj₁ (get l))) (proj₁ (revisit (θ ← [S]-env ((proj₁ (get l)) ₛ))))
      where revisit = (λ θ → SL.visit (V.visit-lift-sig{sigs = sigs} (V.Canθ-lookup sigs)) (Can p) θ sl)
    ... | yes _ = {!!}
  ... | no _ = {!!}
  -}
  {-
    with (Signal.wrap (proj₁ (get l))) Signal.≟ Ss
  ... | yes refl
     rewrite Env.sig-single-←-←-overwrite θ Ss stat Signal.absent
    = λ x x₁ → x₁
  ... | no ¬eq
    rewrite sym $ Env.←-assoc-comm θ ([S]-env-build ((proj₁ (get l)) ₛ) Signal.absent) ([S]-env-build Ss stat)
                $ (Env.sig-single-noteq-distinct ((proj₁ (get l)) ₛ) Signal.absent Ss stat λ x → ¬eq (trans (cong Signal.wrap x) Signal.unwrap-inverse))
    = Canθₛ-visit-sig-set-monotonic-rec sigs (θ ← [S]-env-build ((proj₁ (get l)) ₛ) set) p Ss stat
       ((mono-extend θ Ss stat ⊑) ((proj₁ (get l)) ₛ) set ¬eq)
      sl
    where set = Signal.absent -}
  

Canθₛ-visit-sig-set-monotonic : ∀ sigs θ p S status
  → (∀ S∈ → (Env.sig-stats {S} θ S∈ ⊑ status))
  → (_∈ (Canθₛ-visit p sigs (θ ← [S]-env-build S status))) ⊆′ (_∈ (Canθₛ-visit p sigs θ))
Canθₛ-visit-sig-set-monotonic sigs θ p S_set stat lat
  =   Canθₛ-visit-sig-set-monotonic-rec sigs θ p S_set stat lat $ (SL.sublist (SigMap.keys+∈ sigs)) 
     

