module binding-preserve where

open import utility
  renaming (_U̬_ to _∪_ ; _|̌_ to _-_)
open import sn-calculus
open import Function using (_∋_ ; _$_ ; _∘_)

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
  using (done; halted ; paused ; value-max)
open import Esterel.Context
open import Esterel.Context.Properties
open import Esterel.Environment
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)


open done
open halted
open paused
open Context1
open EvaluationContext1

open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; [] ; _∷_ ; [_] ; _++_)
open import Data.List.Any
  using (Any ; any ; here ; there)
open import Data.List.Any.Properties
  using (++ˡ ; ++ʳ)
open import Data.Nat
  using (ℕ ; zero ; suc ; _≟_ ; _+_)
open import Data.Product
  using (Σ ; proj₁ ; proj₂ ; ∃ ; _,_ ; _,′_ ; _×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; id)
open import Relation.Nullary
  using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; sym ; module ≡-Reasoning ; subst)

open ≡-Reasoning using (_≡⟨_⟩_ ; _≡⟨⟩_ ; _∎)

open ListSet Data.Nat._≟_
  using (set-subtract ; set-subtract-merge ; set-subtract-notin; set-subtract-[]; set-subtract-split)

++-distribute-subtract : ∀ xs ys zs →
  set-subtract (xs ++ ys) zs ≡
  set-subtract xs zs ++ set-subtract ys zs
++-distribute-subtract []       ys zs = refl
++-distribute-subtract (x ∷ xs) ys zs with any (_≟_ x) zs
... | yes x∈zs = ++-distribute-subtract xs ys zs
... | no  x∉zs = cong (x ∷_) (++-distribute-subtract xs ys zs)

subtract-⊆¹ : ∀ xs ys → set-subtract xs ys ⊆¹ xs
subtract-⊆¹ []       ys = ⊆¹-refl
subtract-⊆¹ (x ∷ xs) ys with any (_≟_ x) ys
... | yes x∈ys = λ   w w∈xs-ys         → ++ʳ [ x ] (subtract-⊆¹ xs ys w w∈xs-ys)
... | no  x∉ys = λ { w (here refl)     → here refl
                   ; w (there w∈xs-ys) → there (subtract-⊆¹ xs ys w w∈xs-ys) }

R-maintain-raise-shared-0 : ∀{xs θ e} → ∀ s e' →
  (ShrMap.keys (ShrMap.[ s ↦ SharedVar.old ,′ δ {θ} {e} e' ]) ++ xs)
  ⊆¹ (SharedVar.unwrap s ∷ xs)
R-maintain-raise-shared-0 s e' s' s'∈[s]++BV
  rewrite ShrMap.keys-1map s (SharedVar.old ,′ δ e')
  = s'∈[s]++BV

R-maintain-raise-shared-1 : ∀ ys {θ e} → ∀ s e' →
  set-subtract ys (ShrMap.keys ShrMap.[ s ↦ SharedVar.old ,′ δ {θ} {e} e' ])
  ⊆¹ set-subtract ys (SharedVar.unwrap s ∷ [])
R-maintain-raise-shared-1 ys s e' s' s'∈ys-[s]
  rewrite ShrMap.keys-1map s (SharedVar.old ,′ δ e')
  = s'∈ys-[s]

R-maintain-raise-sig-0 : ∀{xs} → ∀ S →
  (SigMap.keys (SigMap.[ S ↦ Signal.unknown ]) ++ xs)
  ⊆¹ (Signal.unwrap S ∷ xs)
R-maintain-raise-sig-0 S S' S'∈[S]++BV
  rewrite SigMap.keys-1map S Signal.unknown
  = S'∈[S]++BV

R-maintain-raise-sig-1 : ∀ ys → ∀ S →
  set-subtract ys (SigMap.keys SigMap.[ S ↦ Signal.unknown ])
  ⊆¹ set-subtract ys (Signal.unwrap S ∷ [])
R-maintain-raise-sig-1 ys S S' S'∈ys-[S]
  rewrite SigMap.keys-1map S Signal.unknown
  = S'∈ys-[S]

R-maintain-lift-1 : ∀ S xs ys {zs} →
  set-subtract xs ys ⊆¹ zs → set-subtract (S ∷ xs) ys ⊆¹ (S ∷ zs)
R-maintain-lift-1 S xs ys xs-ys⊆zs S' S'∈⟨S∷xs⟩-ys with any (_≟_ S) ys
R-maintain-lift-1 S xs ys xs-ys⊆zs S' (here refl)      | no  _ =
  here refl
R-maintain-lift-1 S xs ys xs-ys⊆zs S' (there S'∈xs-ys) | no  _ =
  there (xs-ys⊆zs S' S'∈xs-ys)
...                                                    | yes _ =
  there (xs-ys⊆zs S' S'∈⟨S∷xs⟩-ys)

R-maintain-lift-2' : ∀ {zs ws} xs ys →
  set-subtract xs ys ⊆¹ zs →
  set-subtract (xs ++ ws) ys ⊆¹ (zs ++ ws)
R-maintain-lift-2' {zs} {ws} xs ys xs-ys⊆zs
  rewrite ++-distribute-subtract xs ws ys =
  ∪¹-join-⊆¹ (λ u → ++ˡ ∘ xs-ys⊆zs u)
  (⊆¹-trans (subtract-⊆¹ ws ys) (λ u → ++ʳ zs ∘ ⊆¹-refl u))

R-maintain-lift-6' : ∀ {zs} ws xs ys →
  set-subtract xs ys ⊆¹ zs →
  set-subtract (ws ++ xs) ys ⊆¹ (ws ++ zs)
R-maintain-lift-6' {zs} ws xs ys xs-ys⊆zs
  rewrite ++-distribute-subtract ws xs ys =
  ∪¹-join-⊆¹ (⊆¹-trans (subtract-⊆¹ ws ys) (λ u → ++ˡ ∘ ⊆¹-refl u))
  (λ u → ++ʳ ws ∘ xs-ys⊆zs u)

R-maintain-lift-2 : ∀ {zs³ ws³} xs³ ys³ →
  (xs³ - ys³) ⊆ zs³ →
  ((xs³ ∪ ws³) - ys³) ⊆ (zs³ ∪ ws³)
R-maintain-lift-2 xs³ ys³ xs³-ys³⊆zs³ =
  R-maintain-lift-2' ,′ R-maintain-lift-2' ,′ R-maintain-lift-2' #
    xs³ # ys³ # xs³-ys³⊆zs³

R-maintain-lift-6 : ∀ {zs³} ws³ xs³ ys³ →
  (xs³ - ys³) ⊆ zs³ →
  ((ws³ ∪ xs³) - ys³) ⊆ (ws³ ∪ zs³)
R-maintain-lift-6 ws³ xs³ ys³ xs³-ys³⊆zs³ =
  R-maintain-lift-6' ,′ R-maintain-lift-6' ,′ R-maintain-lift-6' #
    ws³ # xs³ # ys³ # xs³-ys³⊆zs³

R-maintain-lift-3' : ∀ {ys zs ws} xs →
  (xs ++ ys) ⊆¹ zs →
  distinct' zs ws →
  distinct' ys ws
R-maintain-lift-3' xs xs++ys⊆zs zs≠ws x x∈ys x∈ws =
  zs≠ws x (xs++ys⊆zs x (++ʳ xs x∈ys)) x∈ws

R-maintain-lift-3 : ∀ {ys³ zs³ ws³} xs³ →
  (xs³ ∪ ys³) ⊆ zs³ →
  distinct zs³ ws³ →
  distinct ys³ ws³
R-maintain-lift-3 xs³ xs³∪ys³⊆zs³ zs³≠ws³ =
  R-maintain-lift-3' ,′ R-maintain-lift-3' ,′ R-maintain-lift-3' #
    xs³ # xs³∪ys³⊆zs³ # zs³≠ws³

R-maintain-lift-4' : ∀ {xs ws us vs zs} ys →
  set-subtract xs ys ⊆¹ us → distinct' us zs →
  (ys ++ ws) ⊆¹ vs →         distinct' vs zs →
  distinct' xs zs
R-maintain-lift-4' {.a ∷ xs} ys xs-ys⊆us us≠zs ys++ws⊆vs vs≠zs
                   a (here refl) a∈zs with any (_≟_ a) ys
... | yes a∈ys = vs≠zs a (ys++ws⊆vs a (++ˡ a∈ys)) a∈zs
... | no  a∉ys = us≠zs a (xs-ys⊆us a (here refl)) a∈zs
R-maintain-lift-4' {x ∷ xs} ys xs-ys⊆us us≠zs ys++ws⊆vs vs≠zs
                   a (there a∈xs) a∈zs with any (_≟_ x) ys
... | yes x∈ys = R-maintain-lift-4' ys xs-ys⊆us us≠zs ys++ws⊆vs vs≠zs a a∈xs a∈zs
... | no  x∉ys = R-maintain-lift-4' ys (proj₂ (∪¹-unjoin-⊆¹ [ x ] xs-ys⊆us))
                                       us≠zs ys++ws⊆vs vs≠zs a a∈xs a∈zs

R-maintain-lift-4 : ∀ {ws³ us³ vs³ xs³ zs³} ys³ →
  (xs³ - ys³) ⊆ us³ → distinct us³ zs³ →
  (ys³ ∪ ws³) ⊆ vs³ → distinct vs³ zs³ →
  distinct xs³ zs³
R-maintain-lift-4 ys³ xs³-ys³⊆us³ us³≠zs³ ys³∪ws³⊆vs³ vs³≠zs³ =
  R-maintain-lift-4' ,′ R-maintain-lift-4' ,′ R-maintain-lift-4' #
    ys³ # xs³-ys³⊆us³ # us³≠zs³ # ys³∪ws³⊆vs³ # vs³≠zs³

R-maintain-lift-5 : ∀ xs³ ys³ {zs³ ws³} →
  (ys³ ∪ zs³) ⊆ ws³ →
  (ys³ ∪ (xs³ ∪ zs³)) ⊆ (xs³ ∪ ws³)
R-maintain-lift-5 xs³ ys³ ys³∪zs³⊆ws³ with ∪-unjoin-⊆ ys³ ys³∪zs³⊆ws³
... | ys³⊆ws³ , zs³⊆ws³ = ∪-join-⊆ (∪ʳ xs³ ys³⊆ws³) (∪-respect-⊆-right xs³ zs³⊆ws³)

R-maintain-lift-0 : ∀{p θ q BVp FVp E} →
  CorrectBinding p BVp FVp →
  p ≐ E  ⟦ ρ θ · q ⟧e →
  ∃ λ { (BV' , FV') →
    (BV' ⊆ BVp × FV' ⊆ FVp) ×
    CorrectBinding (ρ θ · E ⟦ q ⟧e) BV' FV' }
R-maintain-lift-0 cbp dehole = _ , (⊆-refl , ⊆-refl) , cbp
R-maintain-lift-0 (CBpar {BVq = BVq'} {FVq = FVq'} cbp' cbq'
                         BVp'≠BVq' FVp'≠BVq' BVp'≠FVq' Xp'≠Xq')
                  (depar₁ p'≐E⟦ρθ⟧)
  with R-maintain-lift-0 cbp' p'≐E⟦ρθ⟧
... | (BV' , FV') , (BV'⊆BVp' , FV'⊆FVp') ,
      CBρ {θ} {_} {BVp''} {FVp''} cbp'' =
  _ ,
  (⊆-subst-left (∪-assoc (Dom θ) BVp'' BVq') (∪-respect-⊆-left BV'⊆BVp') ,′
   R-maintain-lift-2 FVp'' (Dom θ) FV'⊆FVp') ,′
  CBρ (CBpar cbp'' cbq'
             (R-maintain-lift-3 (Dom θ) BV'⊆BVp' BVp'≠BVq')
             (R-maintain-lift-4 (Dom θ) FV'⊆FVp' FVp'≠BVq' BV'⊆BVp' BVp'≠BVq')
             (R-maintain-lift-3 (Dom θ) BV'⊆BVp' BVp'≠FVq')
             (R-maintain-lift-4' (proj₂ (proj₂ (Dom θ))) (proj₂ (proj₂ FV'⊆FVp'))
                                 Xp'≠Xq' (proj₂ (proj₂ BV'⊆BVp')) (proj₂ (proj₂ BVp'≠FVq'))))
R-maintain-lift-0 (CBpar {BVp = BVp'} {FVp = FVp'} cbp' cbq'
                         BVp'≠BVq' FVp'≠BVq' BVp'≠FVq' Xp'≠Xq')
                  (depar₂ q'≐E⟦ρθ⟧)
  with R-maintain-lift-0 cbq' q'≐E⟦ρθ⟧
... | (BV' , FV') , (BV'⊆BVq' , FV'⊆FVq') ,
      CBρ {θ} {_} {BVq''} {FVq''} cbq'' =
  _ ,
  (R-maintain-lift-5 BVp' (Dom θ) BV'⊆BVq' ,′
   R-maintain-lift-6 FVp' FVq'' (Dom θ) FV'⊆FVq') ,′
  CBρ (CBpar cbp' cbq''
             (distinct-sym (R-maintain-lift-3 (Dom θ) BV'⊆BVq' (distinct-sym BVp'≠BVq')))
             (distinct-sym (R-maintain-lift-3 (Dom θ) BV'⊆BVq' (distinct-sym FVp'≠BVq')))
             (distinct-sym (R-maintain-lift-4 (Dom θ)
                                              FV'⊆FVq' (distinct-sym BVp'≠FVq')
                                              BV'⊆BVq' (distinct-sym BVp'≠BVq')))
             (distinct'-sym
              (R-maintain-lift-4' (proj₂ (proj₂ (Dom θ))) (proj₂ (proj₂ FV'⊆FVq'))
                                  (distinct'-sym Xp'≠Xq') (proj₂ (proj₂ BV'⊆BVq'))
                                  (distinct'-sym (proj₂ (proj₂ FVp'≠BVq'))))))
R-maintain-lift-0 (CBseq cbp' cbq' BV≠FV) (deseq p'≐E⟦ρθ⟧)
  with R-maintain-lift-0 cbp' p'≐E⟦ρθ⟧
... | (BV' , FV') , (BV'⊆BVp' , FV'⊆FVp') ,
      CBρ {θ} {_} {BVp''} {FVp''} cbp'' =
  _ ,
  (∪-join-⊆
    (∪ˡ (∪-unjoin-⊆ˡ {Dom θ} BV'⊆BVp'))
    (∪-respect-⊆-left (∪-unjoin-⊆ʳ (Dom θ) BV'⊆BVp')) ,′
   R-maintain-lift-2 FVp'' (Dom θ) FV'⊆FVp') ,′
  CBρ (CBseq cbp'' cbq'
             (⊆-respect-distinct-left (∪-unjoin-⊆ʳ (Dom θ) BV'⊆BVp') BV≠FV))
R-maintain-lift-0 (CBloopˢ cbp' cbq' BVp'≠FVq' BVq'≠FVq') (deloopˢ p'≐E⟦ρθ⟧)
  with R-maintain-lift-0 cbp' p'≐E⟦ρθ⟧
... | (BV' , FV') , (BV'⊆BVp' , FV'⊆FVp') ,
      CBρ {θ} {_} {BVp''} {FVp''} cbp'' =
  _ ,
  (∪-join-⊆
    (∪ˡ (∪-unjoin-⊆ˡ {Dom θ} BV'⊆BVp'))
    (∪-respect-⊆-left (∪-unjoin-⊆ʳ (Dom θ) BV'⊆BVp')) ,′
   R-maintain-lift-2 FVp'' (Dom θ) FV'⊆FVp') ,′
  CBρ (CBloopˢ cbp'' cbq'
               (⊆-respect-distinct-left (∪-unjoin-⊆ʳ (Dom θ) BV'⊆BVp') BVp'≠FVq') BVq'≠FVq')
R-maintain-lift-0 (CBsusp {S = S} cbp' S∉BV) (desuspend p'≐E⟦ρθ⟧)
  with R-maintain-lift-0 cbp' p'≐E⟦ρθ⟧
... | (BV' , FV') , (BV'⊆BVp' , FV'⊆FVp') ,
      CBρ {θ} {_} {BVp''} {FVp''} cbp'' =
  _ ,
  (BV'⊆BVp' ,′
   (R-maintain-lift-1 (Signal.unwrap S) (proj₁ FVp'') (proj₁ (Dom θ)) (proj₁ FV'⊆FVp') ,′
    proj₁ (proj₂ FV'⊆FVp') ,′
    proj₂ (proj₂ FV'⊆FVp'))) ,′
  CBρ (CBsusp cbp''
              (λ S' S'∈[S] S'∈BV →
                 S∉BV S' S'∈[S] (proj₁ BV'⊆BVp' S' (++ʳ (proj₁ (Dom θ)) S'∈BV))))
R-maintain-lift-0 (CBtrap cbp') (detrap p'≐E⟦ρθ⟧)
  with R-maintain-lift-0 cbp' p'≐E⟦ρθ⟧
... | (BV' , FV') , ⟨BV'⊆BVp'⟩×⟨FV'⊆FVp'⟩ , CBρ cbp'' =
  _ , ⟨BV'⊆BVp'⟩×⟨FV'⊆FVp'⟩ ,′ CBρ (CBtrap cbp'')

R-maintain-raise-var-0 : ∀{xs θ e} → ∀ x e' →
  (VarMap.keys (VarMap.[ x ↦ δ {θ} {e} e' ]) ++ xs)
  ⊆¹ (SeqVar.unwrap x ∷ xs)
R-maintain-raise-var-0 x e' x' x'∈[x]++BV
  rewrite VarMap.keys-1map x (δ e')
  = x'∈[x]++BV

R-maintain-raise-var-1 : ∀ ys {θ e} → ∀ x e' →
  set-subtract ys (VarMap.keys VarMap.[ x ↦ δ {θ} {e} e' ])
  ⊆¹ set-subtract ys (SeqVar.unwrap x ∷ [])
R-maintain-raise-var-1 ys x e' x' x'∈ys-[x]
  rewrite VarMap.keys-1map x (δ e')
  = x'∈ys-[x]

R-maintains-binding : ∀{p q BV FV} → CorrectBinding p BV FV → p sn⟶₁ q → ∃ λ { (BV' , FV') → CorrectBinding q BV' FV' × BV' ⊆ BV × FV' ⊆ FV}
R-maintains-binding (CBpar{BVp = BVp}{FVp = FVp} cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-right hnothin (dhalted q')) = _ , cbq , ∪ʳ BVp ((λ x x₁ → x₁) , (λ x x₁ → x₁) , (λ x x₁ → x₁)) , ∪ʳ FVp ((λ x x₁ → x₁) , (λ x x₁ → x₁) , (λ x x₁ → x₁))
R-maintains-binding (CBpar cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-right (hexit _) (dhalted hnothin))
  = _ , CBexit , ((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ()))) , ((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))
R-maintains-binding (CBpar cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-right (hexit _) (dhalted (hexit _))) = _ , CBexit , (((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))) , ((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))
R-maintains-binding (CBpar{BVp = BVp}{FVp = FVp} cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-right hnothin (dpaused q')) = _ , cbq , ∪ʳ BVp ((λ x x₁ → x₁) , (λ x x₁ → x₁) , (λ x x₁ → x₁)) , ∪ʳ FVp ((λ x x₁ → x₁) , (λ x x₁ → x₁) , (λ x x₁ → x₁))
R-maintains-binding (CBpar cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-right (hexit _) (dpaused q')) = _ , CBexit , (((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))) , ((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))
R-maintains-binding (CBpar{BVp = BVp}{FVp = FVp} cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-left (dhalted hnothin) q') = _ , cbq , ∪ʳ BVp ((λ x x₁ → x₁) , (λ x x₁ → x₁) , (λ x x₁ → x₁)) , ∪ʳ FVp ((λ x x₁ → x₁) , (λ x x₁ → x₁) , (λ x x₁ → x₁))
R-maintains-binding (CBpar cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-left (dhalted (hexit _)) hnothin) = _ , CBexit , (((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))) , ((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))
R-maintains-binding (CBpar cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-left (dhalted (hexit _)) (hexit _)) = _ , CBexit , (((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))) , ((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))
R-maintains-binding (CBpar cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-left (dpaused p') hnothin) = _ , cbp , ∪ˡ ((λ x x₁ → x₁) , (λ x x₁ → x₁) , (λ x x₁ → x₁)), ∪ˡ ((λ x x₁ → x₁) , (λ x x₁ → x₁) , (λ x x₁ → x₁))
R-maintains-binding (CBpar cbp cbq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) (rpar-done-left (dpaused p') (hexit _)) = _ , CBexit , (((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))) , ((λ x → λ ()) , ((λ x → λ ()) , (λ x → λ ())))
R-maintains-binding {(ρ θ · p)} (CBρ cb) red@(ris-present S∈ θS≡present p≐E⟦presentS⟧)
  with binding-extract cb p≐E⟦presentS⟧
... | _ , _ , cbpresent@(CBpresent {S = S} cbp' cbq')
  with binding-subst cb p≐E⟦presentS⟧
                     cbpresent (∪ˡ ⊆-refl) (∪ʳ (+S S base) (∪ˡ ⊆-refl))
                     cbp'
... | _ , (a , b) , cb' = _ , CBρ cb' , ∪-respect-⊆-right (Dom θ) a , ⊆-respect-|̌ (Dom θ) b
R-maintains-binding {(ρ θ · p)} (CBρ cb) red@(ris-absent S∈ θS≡absent p≐E⟦presentS⟧)
  with binding-extract cb p≐E⟦presentS⟧
... | _ , _ , cbpresent@(CBpresent {S = S} {BVp = BVp'} {FVp = FVp'} cbp' cbq') 
  with binding-subst cb p≐E⟦presentS⟧
                     cbpresent (∪ʳ BVp' ⊆-refl) (∪ʳ (+S S base) (∪ʳ FVp' ⊆-refl))
                     cbq'
... | _ , (a , b) , cb' = _ , CBρ cb' , ∪-respect-⊆-right (Dom θ) a , ⊆-respect-|̌ (Dom θ) b
R-maintains-binding {(ρ θ · p)} (CBρ cb) (remit{S = S} S∈ θS≢absent p≐E⟦emitS⟧)
  with binding-extract cb p≐E⟦emitS⟧
... | _ , _ , cbemit
  with binding-subst cb p≐E⟦emitS⟧
                     cbemit ⊆-empty-left ⊆-empty-left
                     CBnothing
... | _ , (a , b) , cbp'
      rewrite cong fst (sig-set-dom-eq S Signal.present  θ S∈)
   = _ , CBρ cbp' , ∪-respect-⊆-right (Dom θ') a , ⊆-respect-|̌ (Dom θ') b
     where θ' = (set-sig{S} θ S∈ Signal.present)
R-maintains-binding {(loop p)} {FV = FV2} (CBloop {BV = BV}{FV = FV} cb BV≠FV) rloop-unroll =
   _ , (CBloopˢ cb cb BV≠FV BV≠FV) , (sub BV , sub FV)
   where
     sub1 : ∀ x → (x ++ x) ⊆¹ x
     sub1 x z y with ++⁻ x y
     ... | inj₁ a = a
     ... | inj₂ a = a
     sub : ∀ x → (x ∪ x) ⊆ x
     sub x = sub1 , sub1 , sub1 # x
R-maintains-binding (CBseq{BVp = BVp}{FVp = FVp} cbp cbq BV≠FV) rseq-done = _ , cbq , ∪ʳ BVp ⊆-refl , ∪ʳ FVp ⊆-refl
R-maintains-binding (CBseq cbp cbq BV≠FV) rseq-exit = _ , CBexit , ⊆-empty-left , ⊆-empty-left
R-maintains-binding (CBloopˢ cbp cbq BV≠FV _) rloopˢ-exit = _ , CBexit , ⊆-empty-left , ⊆-empty-left
R-maintains-binding (CBsusp cb _) (rsuspend-done _) = _ , cb , ⊆-refl , ((λ x x₁ → there x₁) , (λ x z → z) , (λ x z → z))
R-maintains-binding (CBtrap cb) (rtrap-done hnothin) = _ , CBnothing ,  ⊆-empty-left ,  ⊆-empty-left
R-maintains-binding (CBtrap cb) (rtrap-done (hexit zero)) = _ , CBnothing ,  ⊆-empty-left ,  ⊆-empty-left
R-maintains-binding (CBtrap cb) (rtrap-done (hexit (suc n))) = _ , CBexit , ⊆-empty-left ,  ⊆-empty-left
R-maintains-binding (CBsig{S = S}{FV = FV} cb) rraise-signal
   = _ , CBρ cb
       , ( (R-maintain-raise-sig-0 S) ,′ ⊆¹-refl ,′ ⊆¹-refl) 
       , ((R-maintain-raise-sig-1 (fst FV) S) ,′ ⊆¹-refl ,′ ⊆¹-refl)
R-maintains-binding (CBρ{θ = θ} cb) (rraise-shared {s = s} {e} e' p≐E⟦shared⟧)
  with binding-extract cb p≐E⟦shared⟧
... | _ , _ , cbshr@(CBshared {FV = FV} cbp)
  with binding-subst cb p≐E⟦shared⟧
                     cbshr (⊆¹-refl ,′ -- S'∈BVp
                            R-maintain-raise-shared-0 s e' ,′
                            ⊆¹-refl)   -- x'∈BVp
                           (∪ʳ (FVₑ e)
                               (⊆¹-refl ,′  -- S'∈FVe+⟨FVp-s⟩
                                R-maintain-raise-shared-1 (proj₁ (proj₂ FV)) s e' ,′
                                ⊆¹-refl))   -- x'∈FVe+⟨FVp-s⟩
                     (CBρ cbp)
... | _ , (a , b) , cbp' = _ , CBρ cbp' ,  ∪-respect-⊆-right (Dom θ) a ,  ⊆-respect-|̌ (Dom θ) b
R-maintains-binding (CBρ{θ = θ} cb) (rset-shared-value-old{s = s} e' s∈ θs≡old p≐E⟦s⇐e⟧)
  with binding-extract cb p≐E⟦s⇐e⟧
... | _ , _ , cbshrset
  with binding-subst cb p≐E⟦s⇐e⟧
                     cbshrset ⊆-empty-left ⊆-empty-left
                     CBnothing
... | _ , (a , b) , cb'
      rewrite cong snd (shr-set-dom-eq s SharedVar.new (δ e') θ s∈)
     = _ , CBρ cb' , ∪-respect-⊆-right (Dom (set-shr{s = s} θ s∈ SharedVar.new (δ e'))) a ,  ⊆-respect-|̌ (Dom (set-shr{s = s} θ s∈ SharedVar.new (δ e'))) b
R-maintains-binding (CBρ{θ = θ} cb) (rset-shared-value-new{s = s} e' s∈ θs≡new p≐E⟦s⇐e⟧)
  with binding-extract cb p≐E⟦s⇐e⟧
... | _ , _ , cbshrset
  with binding-subst cb p≐E⟦s⇐e⟧
                     cbshrset ⊆-empty-left ⊆-empty-left
                     CBnothing
... | _ , (a , b) , cb'
      rewrite cong snd (shr-set-dom-eq s SharedVar.new ((shr-vals{s} θ s∈) + (δ e')) θ s∈)
     = _ , CBρ cb' , ( ∪-respect-⊆-right (Dom (set-shr{s = s} θ s∈ SharedVar.new _)) a) , ⊆-respect-|̌ (Dom (set-shr{s = s} θ s∈ SharedVar.new _)) b
R-maintains-binding (CBρ{θ = θ} cb) (rraise-var {x = x} {e = e} e' p≐E⟦var⟧)
  with binding-extract cb p≐E⟦var⟧
... | _ , _ , cbvar@(CBvar {FV = FV} cbp)
  with binding-subst cb p≐E⟦var⟧
                     cbvar (⊆¹-refl ,′
                            ⊆¹-refl ,′
                            R-maintain-raise-var-0 x e')
                           (∪ʳ (FVₑ e)
                               (⊆¹-refl ,′
                                ⊆¹-refl ,′
                                R-maintain-raise-var-1 (proj₂ (proj₂ FV)) x e'))
                     (CBρ cbp)
... | _ , (a , b) , cb' = _ , CBρ cb' , ( ∪-respect-⊆-right (Dom θ) a) , ⊆-respect-|̌ (Dom θ) b
R-maintains-binding (CBρ{θ = θ} cb) (rset-var{x = x} x∈ e' p≐E⟦x≔e⟧)
  with binding-extract cb p≐E⟦x≔e⟧
... | _ , _ , cbvarset
  with binding-subst cb p≐E⟦x≔e⟧
                     cbvarset ⊆-empty-left ⊆-empty-left
                     CBnothing
... | _ , (a , b) , cb'
    rewrite cong thd (seq-set-dom-eq x (δ e') θ x∈)
   = _ , CBρ cb' ,  ∪-respect-⊆-right (Dom (set-var{x} θ x∈ (δ e'))) a , ⊆-respect-|̌ (Dom (set-var{x} θ x∈ (δ e'))) b
R-maintains-binding (CBρ{θ = θ} cb) (rif-false x∈ θx≡zero p≐E⟦if⟧)
  with binding-extract cb p≐E⟦if⟧
... | _ , _ , cbif@(CBif {x = x} {BVp = BVp} {FVp = FVp} cbp cbq)
  with binding-subst cb p≐E⟦if⟧
                     cbif (∪ʳ BVp ⊆-refl) (∪ʳ (+x x base) (∪ʳ FVp ⊆-refl))
                     cbq
... | _ , (a , b) , cb' = _ , CBρ cb' , ( ∪-respect-⊆-right (Dom θ) a) , ( ⊆-respect-|̌ (Dom θ) b)
R-maintains-binding (CBρ{θ = θ} cb) (rif-true x∈ θx≡suc p≐E⟦if⟧)
  with binding-extract cb p≐E⟦if⟧
... | _ , _ , cbif@(CBif {x = x} cbp cbq)
  with binding-subst cb p≐E⟦if⟧
                     cbif (∪ˡ ⊆-refl) (∪ʳ (+x x base) (∪ˡ ⊆-refl))
                     cbp
... | _ , (a , b) , cb' = _ , CBρ cb' , ∪-respect-⊆-right (Dom θ) a , ( ⊆-respect-|̌ (Dom θ) b)
R-maintains-binding (CBρ{θ = θ} cb) (rabsence{S = S} S∈ θS≡unknown S∉canₛ) rewrite cong fst (sig-set-dom-eq S Signal.absent θ S∈) = _ , CBρ cb , ⊆-refl , ⊆-refl
R-maintains-binding (CBρ{θ = θ} cb) (rreadyness{s = s} s∈ θs≡old⊎θs≡new s∉canₛₕ)  rewrite cong snd (shr-set-dom-eq s SharedVar.ready (shr-vals{s} θ s∈) θ s∈) = _ , CBρ cb , ⊆-refl , ⊆-refl
R-maintains-binding (CBρ{θ = θo}{BV = BVo}{FV = FVo} cb) (rmerge{θ₂ = θi} p≐E⟦ρθ⟧) with R-maintain-lift-0 cb p≐E⟦ρθ⟧
... | _ , (a , b) , cb'@(CBρ{BV = BVi}{FV = FVi} cbp'')
        = _ , CBρ cbp'' ,
         bvsub ,
         fvsub
     where
     fvsubS : (set-subtract (fst FVi) (fst (Dom (θo ← θi)))) ⊆¹ (set-subtract (fst FVo) (fst (Dom θo)))
     fvsubS x x∈FVi\Dom⟨θo←θi⟩ with set-subtract-merge{fst FVi}{(fst (Dom (θo ← θi)))}{x} x∈FVi\Dom⟨θo←θi⟩
     ... | (x∈FVi , x∉Dom⟨θo←θi⟩) = set-subtract-notin ((fst b) x (set-subtract-notin x∈FVi x∉Dom⟨θi⟩)) x∉Dom⟨θo⟩
       where
          x∉Dom⟨θo⟩ : x ∉ fst (Dom θo)
          x∉Dom⟨θo⟩ x∈Dom⟨θo⟩ = x∉Dom⟨θo←θi⟩ (sig-←-monoˡ (x ₛ) θo θi x∈Dom⟨θo⟩) 
          
          x∉Dom⟨θi⟩ : x ∉ fst (Dom θi)
          x∉Dom⟨θi⟩ x∈Dom⟨θi⟩ = x∉Dom⟨θo←θi⟩ (sig-←-monoʳ (x ₛ) θi θo x∈Dom⟨θi⟩)

     fvsubs : (set-subtract (snd FVi) (snd (Dom (θo ← θi)))) ⊆¹ (set-subtract (snd FVo) (snd (Dom θo)))
     fvsubs x x∈FVi\Dom⟨θo←θi⟩ with set-subtract-merge{snd FVi}{(snd (Dom (θo ← θi)))}{x} x∈FVi\Dom⟨θo←θi⟩
     ... | (x∈FVi , x∉Dom⟨θo←θi⟩) = set-subtract-notin ((snd b) x (set-subtract-notin x∈FVi x∉Dom⟨θi⟩)) x∉Dom⟨θo⟩
       where
          x∉Dom⟨θo⟩ : x ∉ snd (Dom θo)
          x∉Dom⟨θo⟩ x∈Dom⟨θo⟩ = x∉Dom⟨θo←θi⟩ (shr-←-monoˡ (x ₛₕ) θo θi x∈Dom⟨θo⟩) 
          
          x∉Dom⟨θi⟩ : x ∉ snd (Dom θi)
          x∉Dom⟨θi⟩ x∈Dom⟨θi⟩ = x∉Dom⟨θo←θi⟩ (shr-←-monoʳ (x ₛₕ) θi θo x∈Dom⟨θi⟩)

     fvsubx : (set-subtract (thd FVi) (thd (Dom (θo ← θi)))) ⊆¹ (set-subtract (thd FVo) (thd (Dom θo)))
     fvsubx x x∈FVi\Dom⟨θo←θi⟩ with set-subtract-merge{thd FVi}{(thd (Dom (θo ← θi)))}{x} x∈FVi\Dom⟨θo←θi⟩
     ... | (x∈FVi , x∉Dom⟨θo←θi⟩) = set-subtract-notin ((thd b) x (set-subtract-notin x∈FVi x∉Dom⟨θi⟩)) x∉Dom⟨θo⟩
       where
          x∉Dom⟨θo⟩ : x ∉ thd (Dom θo)
          x∉Dom⟨θo⟩ x∈Dom⟨θo⟩ = x∉Dom⟨θo←θi⟩ (seq-←-monoˡ (x ᵥ) θo θi x∈Dom⟨θo⟩)

          x∉Dom⟨θi⟩ : x ∉ thd (Dom θi)
          x∉Dom⟨θi⟩ x∈Dom⟨θi⟩ = x∉Dom⟨θo←θi⟩ (seq-←-monoʳ (x ᵥ) θi θo x∈Dom⟨θi⟩)


     fvsub : (FVi - (Dom (θo ← θi))) ⊆ (FVo - (Dom θo))
     fvsub = fvsubS , fvsubs , fvsubx
     bvsubS : ((fst (Dom (θo ← θi))) ++ (fst BVi)) ⊆¹ ((fst (Dom θo)) ++ (fst BVo))
     bvsubS x y with ++⁻ (fst (Dom (θo ← θi))) y
     ... | inj₂ x∈BVi = ++ʳ (fst $ Dom θo) ((fst a) x (++ʳ (fst $ Dom θi) x∈BVi))
     ... | inj₁ x∈⟨θo←θi⟩ with sig-←⁻{θo}{θi} (x ₛ) x∈⟨θo←θi⟩
     ... | inj₁ x∈θo = ++ˡ x∈θo
     ... | inj₂ x∈θi = ++ʳ (fst $ Dom θo) ((fst a) x (++ˡ x∈θi))


     bvsubs : ((snd (Dom (θo ← θi))) ++ (snd BVi)) ⊆¹ ((snd (Dom θo)) ++ (snd BVo))
     bvsubs x y with ++⁻ (snd (Dom (θo ← θi))) y
     ... | inj₂ x∈BVi = ++ʳ (snd $ Dom θo) ((snd a) x (++ʳ (snd $ Dom θi) x∈BVi))
     ... | inj₁ x∈⟨θo←θi⟩ with shr-←⁻{θo}{θi} (x ₛₕ) x∈⟨θo←θi⟩
     ... | inj₁ x∈θo = ++ˡ x∈θo
     ... | inj₂ x∈θi = ++ʳ (snd $ Dom θo) ((snd a) x (++ˡ x∈θi))


     bvsubx : ((thd (Dom (θo ← θi))) ++ (thd BVi)) ⊆¹ ((thd (Dom θo)) ++ (thd BVo))
     bvsubx x y with ++⁻ (thd (Dom (θo ← θi))) y
     ... | inj₂ x∈BVi = ++ʳ (thd $ Dom θo) ((thd a) x (++ʳ (thd $ Dom θi) x∈BVi))
     ... | inj₁ x∈⟨θo←θi⟩ with seq-←⁻{θo}{θi} (x ᵥ) x∈⟨θo←θi⟩
     ... | inj₁ x∈θo = ++ˡ x∈θo
     ... | inj₂ x∈θi = ++ʳ (thd $ Dom θo) ((thd a) x (++ˡ x∈θi))

     bvsub : ((Dom (θo ← θi)) ∪ BVi) ⊆ ((Dom θo) ∪ BVo)
     bvsub = bvsubS , bvsubs , bvsubx

-- R-maintains-binding : ∀{p q BV FV} → CorrectBinding p BV FV → p sn⟶₁ q → ∃ λ { (BV' , FV') → CorrectBinding q BV' FV' }
sn⟶-maintains-binding : ∀ {p BV FV q} → CorrectBinding p BV FV → p sn⟶ q → ∃ λ {(BVq , FVq) → CorrectBinding q BVq FVq × BVq ⊆ BV × FVq ⊆ FV }
sn⟶-maintains-binding CBp (rcontext C dc p₁sn⟶₁q₁)
  with binding-extractc' CBp dc
... | (BVp₁ , FVp₁) , CBp₁
  with R-maintains-binding CBp₁ p₁sn⟶₁q₁
... | (BVq₁ , FVq₁) , (CBq₁ , BVq₁⊆BVp₁ , FVq₁⊆FVp₁)
  with binding-substc' CBp dc CBp₁ BVq₁⊆BVp₁ FVq₁⊆FVp₁ CBq₁
... | (BVq , FVq) , ((BVq⊆BVp , FVq⊆FVp), CBq) =
  (BVq , FVq) , (CBq , BVq⊆BVp , FVq⊆FVp)


sn⟶*-maintains-binding : ∀ {p BV FV q} → CorrectBinding p BV FV → p sn⟶* q → ∃ λ {(BVq , FVq) → CorrectBinding q BVq FVq}

sn⟶*-maintains-binding cb rrefl = _ , cb
sn⟶*-maintains-binding cb (rstep x psn⟶*q)
  = sn⟶*-maintains-binding (proj₁ (proj₂ (sn⟶-maintains-binding cb x))) psn⟶*q

CB-preservation :  ∀ p q C → CB (C ⟦ p ⟧c) → p sn⟶₁ q → CB (C ⟦ q ⟧c)
CB-preservation p q C CBp psn⟶₁q with
  sn⟶-maintains-binding{p = C ⟦ p ⟧c}{q = C ⟦ q ⟧c} CBp (rcontext C Crefl psn⟶₁q)
... | (BV , FV) , CBq , _ with BVFVcorrect (C ⟦ q ⟧c) BV FV CBq
... | refl , refl = CBq

CB-preservation* :  ∀ p q → CB p → p sn⟶* q → CB q
CB-preservation* p q CBp psn⟶*q with
  sn⟶*-maintains-binding CBp psn⟶*q
... | (BV , FV) , CBq with BVFVcorrect q BV FV CBq
... | refl , refl = CBq
