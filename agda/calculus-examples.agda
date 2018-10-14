module calculus-examples where

open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.List.Any using (here ; there ; any)
open import Data.List.Any.Properties
open import Data.OrderedListMap
open import Data.Sum using (inj₁ ; inj₂ ; _⊎_)
open import Data.Maybe.Base
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Bool.Base using (true ; false)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (subst ; cong ; sym ; trans)

open import calculus
open import utility

open import Esterel.Environment as Env
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ ; unknown ; present ; absent ; _≟ₛₜ_)
open import Esterel.Variable.Shared as SharedVar using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar using (SeqVar)

open import Esterel.Lang
open import Esterel.Lang.CanFunction
open import Esterel.Lang.CanFunction.Properties
open import Esterel.Lang.CanFunction.SetSigMonotonic using (canₛ-set-sig-monotonic)
open import Esterel.Lang.Properties
open import Esterel.Lang.Binding
open import Esterel.Context
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import context-properties
open import Esterel.Lang.CanFunction.Base using (canₛ-⊆-FV)

open import Data.Nat as Nat
  using (ℕ ; zero ; suc ; _+_) renaming (_⊔_ to _⊔ℕ_)
open import Data.Nat.Properties.Simple
  using (+-comm)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; _,′_ ; proj₁ ; proj₂ ; _×_)


open import eval

{- rewriting a present to the true branch -}
{- cannot prove without the `signal` form -}
ex1 : ∀ S p q -> CB p ->
    signl S (emit S >> (present S ∣⇒ p ∣⇒ q)) ≡ₑ
    signl S (emit S >> p) # []
ex1 S p q CBp = calc where

  θS→unk : Env
  θS→unk = Θ SigMap.[ S ↦ Signal.unknown ] [] []

  S∈θS→unk : SigMap.∈Dom S (sig θS→unk)
  S∈θS→unk = sig-∈-single S Signal.unknown

  θS→unk[S]≡unk : sig-stats{S = S} θS→unk S∈θS→unk ≡ Signal.unknown
  θS→unk[S]≡unk = sig-stats-1map' S Signal.unknown S∈θS→unk

  θS→pre : Env
  θS→pre = set-sig{S} θS→unk S∈θS→unk Signal.present

  S∈θS→pre : SigMap.∈Dom S (sig θS→pre)
  S∈θS→pre = sig-set-mono' {S} {S} {θS→unk} {Signal.present} {S∈θS→unk} S∈θS→unk

  θS→pre[S]≡pre : sig-stats{S = S} θS→pre S∈θS→pre ≡ Signal.present
  θS→pre[S]≡pre = sig-putget{S} {θS→unk} {Signal.present} S∈θS→unk S∈θS→pre

  θS→unk[S]≠absent : ¬ sig-stats{S = S} θS→unk S∈θS→unk ≡ Signal.absent
  θS→unk[S]≠absent is rewrite θS→unk[S]≡unk = unknotabs is where
    unknotabs : Signal.unknown ≡ Signal.absent → ⊥
    unknotabs ()

  CBsignalS[emitS>>p] : CB (signl S (emit S >> p))
  CBsignalS[emitS>>p]
   = CBsig (CBseq (CBemit{S}) CBp ((λ z → λ ()) , (λ z → λ ()) , (λ z → λ ())))

  calc : signl S (emit S >> (present S ∣⇒ p ∣⇒ q)) ≡ₑ
         signl S (emit S >> p) # []
  calc =
    ≡ₑtran {r = (ρ θS→unk · (emit S >> (present S ∣⇒ p ∣⇒ q)))}
           (≡ₑstep [raise-signal])
   (≡ₑtran {r = (ρ θS→pre · (nothin >> (present S ∣⇒ p ∣⇒ q)))}
           (≡ₑstep ([emit] S∈θS→unk θS→unk[S]≠absent (deseq dehole)))
   (≡ₑtran {r = (ρ θS→pre · (present S ∣⇒ p ∣⇒ q))}
           (≡ₑctxt (dcenv dchole) (dcenv dchole) (≡ₑstep [seq-done]))
   (≡ₑtran {r = (ρ θS→pre · p)}
           (≡ₑstep ([is-present] S S∈θS→pre θS→pre[S]≡pre dehole))
   (≡ₑsymm CBsignalS[emitS>>p]
           (≡ₑtran {r = (ρ θS→unk · (emit S >> p))}
                   (≡ₑstep [raise-signal])
           (≡ₑtran {r = (ρ θS→pre · (nothin >> p))}
                   (≡ₑstep ([emit] S∈θS→unk θS→unk[S]≠absent (deseq dehole)))
           (≡ₑtran {r = ρ θS→pre · p}
                   (≡ₑctxt (dcenv dchole) (dcenv dchole) (≡ₑstep [seq-done]))
           ≡ₑrefl)))))))

Canₛpresent-fact : ∀ S p q ->
  (Signal.unwrap S) ∈ Canₛ (present S ∣⇒ p ∣⇒ q) (Θ SigMap.[ S ↦ Signal.unknown ] [] []) ->
  (Signal.unwrap S ∈ Canₛ p (Θ SigMap.[ S ↦ Signal.unknown ] [] [])) ⊎
  (Signal.unwrap S ∈ Canₛ q (Θ SigMap.[ S ↦ Signal.unknown ] [] []))
Canₛpresent-fact S  p q S∈Canₛ[presentSpq]
  with Env.Sig∈ S (Θ SigMap.[ S ↦ Signal.unknown ] [] [])
Canₛpresent-fact S p q S∈Canₛ[presentSpq] | yes S∈
  with  ⌊ present ≟ₛₜ (Env.sig-stats{S} (Θ SigMap.[ S ↦ Signal.unknown ] [] []) S∈) ⌋
Canₛpresent-fact S p q S∈Canₛ[presentSpq] | yes S∈ | true
 = inj₁ S∈Canₛ[presentSpq]
Canₛpresent-fact S p q S∈Canₛ[presentSpq] | yes S∈ | false
  with ⌊ absent ≟ₛₜ Env.sig-stats{S} (Θ SigMap.[ S ↦ Signal.unknown ] [] []) S∈ ⌋
Canₛpresent-fact S p q S∈Canₛ[presentSpq] | yes S∈ | false | true
  = inj₂ S∈Canₛ[presentSpq]
Canₛpresent-fact S p q S∈Canₛ[presentSpq] | yes S∈ | false | false
  =  ++⁻ (Canₛ p (Θ SigMap.[ S ↦ Signal.unknown ] [] [])) S∈Canₛ[presentSpq]
Canₛpresent-fact S p q _ | no ¬p
  = ⊥-elim (¬p (SigMap.update-in-keys [] S unknown))

{- rewriting a present to the false branch -}
ex2 : ∀ S p q C -> CB (C ⟦ signl S q ⟧c) ->
   Signal.unwrap S ∉ (Canₛ p (Θ SigMap.[ S ↦ unknown ] [] [])) ->
   Signal.unwrap S ∉ (Canₛ q (Θ SigMap.[ S ↦ unknown ] [] [])) ->
   signl S (present S ∣⇒ p ∣⇒ q) ≡ₑ
   signl S q # C
ex2 S p q C CBq s∉Canₛp s∉Canₛq = calc where

 θS→unk : Env
 θS→unk = Θ SigMap.[ S ↦ Signal.unknown ] [] []

 S∈θS→unk : SigMap.∈Dom S (sig θS→unk)
 S∈θS→unk = sig-∈-single S Signal.unknown

 θS→unk[S]≡unk : sig-stats{S = S} θS→unk S∈θS→unk ≡ Signal.unknown
 θS→unk[S]≡unk = sig-stats-1map' S Signal.unknown S∈θS→unk

 θS→abs : Env
 θS→abs = set-sig{S} θS→unk S∈θS→unk Signal.absent

 S∈θS→abs : SigMap.∈Dom S (sig θS→abs)
 S∈θS→abs = sig-set-mono' {S} {S} {θS→unk} {Signal.absent} {S∈θS→unk} S∈θS→unk

 θS→abs[S]≡abs : sig-stats{S = S} θS→abs S∈θS→abs ≡ Signal.absent
 θS→abs[S]≡abs = sig-putget{S} {θS→unk} {Signal.absent} S∈θS→unk S∈θS→abs

 S∉Canθₛq : Signal.unwrap S ∉ Canθₛ SigMap.[ S ↦ unknown ] 0 q []env
 S∉Canθₛq S∈Canθₛq = s∉Canₛq (Canθₛunknown->Canₛunknown S q S∈Canθₛq)

 S∉CanθₛpresentSpq : Signal.unwrap S ∉ Canθₛ SigMap.[ S ↦ unknown ]
                                            0
                                            (present S ∣⇒ p ∣⇒ q)
                                            []env
 S∉CanθₛpresentSpq S∈Canθₛ
   with Canθₛunknown->Canₛunknown S (present S ∣⇒ p ∣⇒ q) S∈Canθₛ
 ... | fact
   with Canₛpresent-fact S p q fact
 ... | inj₁ s∈Canₛp = s∉Canₛp s∈Canₛp
 ... | inj₂ s∈Canₛq = s∉Canₛq s∈Canₛq

 bwd : signl S q ≡ₑ (ρ θS→abs · q) # C
 bwd =
    ≡ₑtran (≡ₑstep [raise-signal])
   (≡ₑtran (≡ₑstep ([absence] S S∈θS→unk θS→unk[S]≡unk S∉Canθₛq))
    ≡ₑrefl)

 fwd : signl S (present S ∣⇒ p ∣⇒ q) ≡ₑ
       (ρ θS→abs · q) # C
 fwd =
     ≡ₑtran (≡ₑstep [raise-signal])
    (≡ₑtran (≡ₑstep ([absence] S S∈θS→unk θS→unk[S]≡unk S∉CanθₛpresentSpq))
    (≡ₑtran (≡ₑstep ([is-absent] S S∈θS→abs θS→abs[S]≡abs dehole))
     ≡ₑrefl)) where

 calc :  signl S (present S ∣⇒ p ∣⇒ q) ≡ₑ
         signl S q # C
 calc = ≡ₑtran fwd (≡ₑsymm CBq bwd)

{- lifting an emit out of a par -}
ex3 : ∀ S p q -> CB (p ∥ q) ->
  signl S ((emit S >> p) ∥ q) ≡ₑ
  signl S  (emit S >> (p ∥ q)) # []
ex3 S p q CBp∥q = calc where

  θS→unk : Env
  θS→unk = Θ SigMap.[ S ↦ Signal.unknown ] [] []

  S∈θS→unk : SigMap.∈Dom S (sig θS→unk)
  S∈θS→unk = sig-∈-single S Signal.unknown

  θS→unk[S]≡unk : sig-stats{S = S} θS→unk S∈θS→unk ≡ Signal.unknown
  θS→unk[S]≡unk = sig-stats-1map' S Signal.unknown S∈θS→unk

  θS→pre : Env
  θS→pre = set-sig{S} θS→unk S∈θS→unk Signal.present

  θS→unk[S]≠absent : ¬ sig-stats{S = S} θS→unk S∈θS→unk ≡ Signal.absent
  θS→unk[S]≠absent is rewrite θS→unk[S]≡unk = unknotabs is where
    unknotabs : Signal.unknown ≡ Signal.absent → ⊥
    unknotabs ()

  calc : signl S ((emit S >> p) ∥ q) ≡ₑ
         signl S  (emit S >> (p ∥ q)) # []
  calc =
    ≡ₑtran {r = ρ θS→unk · ((emit S >> p) ∥ q)}
           (≡ₑstep [raise-signal])
   (≡ₑtran {r = ρ θS→pre · (nothin >> p ∥ q)}
           (≡ₑstep ([emit]{S = S} S∈θS→unk θS→unk[S]≠absent (depar₁ (deseq dehole))))
   (≡ₑtran {r = ρ θS→pre · (p ∥ q)}
           (≡ₑctxt (dcenv (dcpar₁ dchole))
                   (dcenv (dcpar₁ dchole))
                   (≡ₑstep [seq-done]))
           (≡ₑsymm (CBsig (CBseq CBemit CBp∥q
                                 (((λ z → λ ()) ,
                                   (λ z → λ ()) ,
                                   (λ z → λ ())))))
                   (≡ₑtran {r = ρ θS→unk · (emit S >> (p ∥ q))}
                           (≡ₑstep [raise-signal])
                   (≡ₑtran (≡ₑstep ([emit] S∈θS→unk θS→unk[S]≠absent (deseq dehole)))
                           (≡ₑctxt (dcenv dchole)  (dcenv dchole) (≡ₑstep [seq-done])))))))

{- pushing a trap across a par -}
ex4 : ∀ n p q -> CB p ->
      done q -> p ≡ₑ q # [] ->
      (trap (exit (suc n) ∥ p)) ≡ₑ (exit n ∥ trap p) # []

ex4 = ex4-split where

  basealwaysdistinct : ∀ x -> distinct base x
  basealwaysdistinct x = (λ { z () x₂ }) , (λ { z () x₂ }) , (λ { z () x₂})

  CBplugrpartrap : ∀ n -> ∀ {r r′ BVp FVp} ->
      CorrectBinding r BVp FVp →
      r′ ≐ ceval (epar₂ (exit n)) ∷ ceval etrap ∷ [] ⟦ r ⟧c →
      CB r′
  CBplugrpartrap n {p} {p′} {BVp} {FVp} CBp r′dc
    with BVFVcorrect p BVp FVp CBp | unplugc r′dc
  ... | refl , refl | refl = CBpar CBexit (CBtrap CBp)
                                   (basealwaysdistinct BVp)
                                   (basealwaysdistinct (BVars p))
                                   (basealwaysdistinct (FVars p))
                                   (λ { _ () _ })

  CBplugtraprpar : ∀ n -> {r r′ : Term}
      {BVp FVp : Σ (List ℕ) (λ x → List ℕ × List ℕ)} →
      CorrectBinding r BVp FVp →
      r′ ≐ ceval etrap ∷ ceval (epar₂ (exit (suc n))) ∷ [] ⟦ r ⟧c →
      CB r′
  CBplugtraprpar n {r} {r′} {BVp} {FVp} CBr r′C
    with unplugc r′C
  ... | refl
    with BVFVcorrect r BVp FVp CBr
  ... | refl , refl
   = CBtrap (CBpar CBexit CBr
                   (basealwaysdistinct BVp)
                   (basealwaysdistinct (BVars r))
                   (basealwaysdistinct (FVars r))
                   (λ { _ () _}))

  ex4-split : ∀ n p q -> CB p ->
              done q -> p ≡ₑ q # [] ->
              (trap (exit (suc n) ∥ p)) ≡ₑ (exit n ∥ trap p) # []
  ex4-split n p .nothin CBp (dhalted hnothin) p≡ₑnothin =
    ≡ₑtran {r = trap (exit (suc n) ∥ nothin)}
           (≡ₑctxt (dctrap (dcpar₂ dchole))
                   (dctrap (dcpar₂ dchole))
                   (≡ₑ-context [] _ (CBplugtraprpar n) p≡ₑnothin))
    (≡ₑtran {r = trap (exit (suc n))}
            (≡ₑctxt (dctrap dchole)
                    (dctrap dchole)
                    (≡ₑtran (≡ₑstep [par-swap])
                            (≡ₑstep ([par-nothing] (dhalted (hexit (suc n)))))))
    (≡ₑtran {r = exit n}
            (≡ₑstep ([trap-done] (hexit (suc n))))
    (≡ₑsymm (CBpar CBexit (CBtrap CBp)
                   (basealwaysdistinct (BVars p))
                   (basealwaysdistinct (BVars p))
                   (basealwaysdistinct (FVars p))
                   (λ { _ () _ }))
            (≡ₑtran {r = exit n ∥ trap nothin}
                    (≡ₑctxt (dcpar₂ (dctrap dchole))
                            (dcpar₂ (dctrap dchole))
                            (≡ₑ-context [] _ (CBplugrpartrap n) p≡ₑnothin))
            (≡ₑtran {r = exit n ∥ nothin}
                    (≡ₑctxt (dcpar₂ dchole) (dcpar₂ dchole) (≡ₑstep ([trap-done] hnothin)))
            (≡ₑtran {r = nothin ∥ exit n}
                    (≡ₑstep [par-swap])
            (≡ₑtran {r = exit n}
                    (≡ₑstep ([par-nothing] (dhalted (hexit n))))
            ≡ₑrefl)))))))

  ex4-split n p .(exit 0) CBp (dhalted (hexit 0)) p≡ₑexit0 =
    ≡ₑtran {r = trap (exit (suc n) ∥ exit 0) }
           (≡ₑctxt (dctrap (dcpar₂ dchole))
                   (dctrap (dcpar₂ dchole))
                   (≡ₑ-context [] _ (CBplugtraprpar n) p≡ₑexit0))
           (≡ₑtran {r = trap (exit (suc n))}
                   (≡ₑctxt (dctrap dchole) (dctrap dchole)
                           (≡ₑstep ([par-2exit] (suc n) zero)))
           (≡ₑtran {r = exit n}
                   (≡ₑstep ([trap-done] (hexit (suc n))))
           (≡ₑsymm (CBpar CBexit (CBtrap CBp)
                          (basealwaysdistinct (BVars p))
                          (basealwaysdistinct (BVars p))
                          (basealwaysdistinct (FVars p))
                          (λ { _ () _ }))
                   (≡ₑtran {r = exit n ∥ trap (exit 0)}
                           (≡ₑctxt (dcpar₂ (dctrap dchole))
                                   (dcpar₂ (dctrap dchole))
                                   (≡ₑ-context [] _ (CBplugrpartrap n) p≡ₑexit0))
                   (≡ₑtran {r = exit n ∥ nothin }
                           (≡ₑctxt (dcpar₂ dchole) (dcpar₂ dchole)
                                   (≡ₑstep ([trap-done] (hexit zero))))
                   (≡ₑtran {r = nothin ∥ exit n}
                           (≡ₑstep [par-swap])
                   (≡ₑtran {r = exit n}
                           (≡ₑstep ([par-nothing] (dhalted (hexit n))))
                   ≡ₑrefl)))))))

  ex4-split n p .(exit (suc m)) CBp (dhalted (hexit (suc m))) p≡ₑexitm =
    ≡ₑtran {r = trap (exit (suc n) ∥ exit (suc m)) }
           (≡ₑctxt (dctrap (dcpar₂ dchole))
                   (dctrap (dcpar₂ dchole))
                   (≡ₑ-context [] _ (CBplugtraprpar n) p≡ₑexitm))
    (≡ₑtran {r = trap (exit (suc n ⊔ℕ (suc m)))}
            (≡ₑctxt (dctrap dchole) (dctrap dchole)
                    (≡ₑstep ([par-2exit] (suc n) (suc m))))
    (≡ₑtran {r = ↓_ {p = (exit (suc n ⊔ℕ (suc m)))} (hexit (suc n ⊔ℕ (suc m))) }
            (≡ₑstep ([trap-done] (hexit (suc (n ⊔ℕ m)))))
    (≡ₑsymm (CBpar CBexit (CBtrap CBp)
                          (basealwaysdistinct (BVars p))
                          (basealwaysdistinct (BVars p))
                          (basealwaysdistinct (FVars p))
                          (λ { _ () _ }))
            (≡ₑtran {r = exit n ∥ trap (exit (suc m))}
                    (≡ₑctxt (dcpar₂ (dctrap dchole))
                            (dcpar₂ (dctrap dchole))
                            (≡ₑ-context [] _ (CBplugrpartrap n) p≡ₑexitm))
            (≡ₑtran {r = exit n ∥  ↓_ {p = exit (suc m)} (hexit (suc m))}
                    (≡ₑctxt (dcpar₂ dchole) (dcpar₂ dchole)
                            (≡ₑstep ([trap-done] (hexit (suc m)))) )
            (≡ₑtran {r =  ↓_ {p = (exit (suc n ⊔ℕ (suc m)))} (hexit (suc n ⊔ℕ (suc m))) }
                    (≡ₑstep ([par-2exit] n m))
            ≡ₑrefl))))))

  ex4-split n p q CBp (dpaused pausedq) p≡ₑq =
    ≡ₑtran {r = trap (exit (suc n) ∥ q)}
           (≡ₑctxt (dctrap (dcpar₂ dchole))
                   (dctrap (dcpar₂ dchole))
                   (≡ₑ-context [] _ (CBplugtraprpar n) p≡ₑq))
    (≡ₑtran {r = trap (exit (suc n))}
            (≡ₑctxt (dctrap dchole) (dctrap dchole)
                    (≡ₑstep ([par-1exit] (suc n) pausedq)))
    (≡ₑtran {r = exit n}
            (≡ₑstep ([trap-done] (hexit (suc n))))
    (≡ₑsymm (CBpar CBexit (CBtrap CBp)
                        (basealwaysdistinct (BVars p))
                        (basealwaysdistinct (BVars p))
                        (basealwaysdistinct (FVars p))
                        (λ { _ () _ }))
            (≡ₑtran {r = exit n ∥ trap q}
                    (≡ₑctxt (dcpar₂ (dctrap dchole))
                            (dcpar₂ (dctrap dchole))
                            (≡ₑ-context [] _ (CBplugrpartrap n) p≡ₑq))
            (≡ₑtran {r = exit n}
                    (≡ₑstep ([par-1exit] n (ptrap pausedq)))
            ≡ₑrefl)))))


{- lifting a signal out of an evaluation context -}
ex5 : ∀ S p q r E -> CB r ->
      q ≐ E ⟦(signl S p)⟧e ->
      r ≐ E ⟦ p ⟧e ->
      (ρ []env · q) ≡ₑ (ρ []env · (signl S r)) # []
ex5 S p q r E CBr decomp1 decomp2 = calc where

  θS→unk : Env
  θS→unk = Θ SigMap.[ S ↦ Signal.unknown ] [] []

  replugit : q ≐ Data.List.map ceval E ⟦ signl S p ⟧c ->
             E ⟦ ρ θS→unk · p ⟧e ≐ Data.List.map ceval E ⟦ ρ θS→unk · p ⟧c
  replugit x = ⟦⟧e-to-⟦⟧c Erefl

  calc : (ρ []env · q) ≡ₑ (ρ []env · (signl S r)) # []
  calc =
    ≡ₑtran {r = ρ []env · (E ⟦ (ρ θS→unk · p) ⟧e)}
           (≡ₑctxt (dcenv (⟦⟧e-to-⟦⟧c decomp1))
                   (dcenv (replugit (⟦⟧e-to-⟦⟧c decomp1)))
                   (≡ₑstep [raise-signal]))
   (≡ₑtran {r = ρ θS→unk · (E ⟦ p ⟧e)}
           (≡ₑstep ([merge]{E = E} Erefl))
           (≡ₑsymm (CBρ (CBsig CBr))
                 (≡ₑtran {r = ρ []env · (ρ θS→unk · r)}
                         (≡ₑctxt (dcenv dchole) (dcenv dchole) (≡ₑstep [raise-signal]))
                         (≡ₑstep ([merge] {E = []}
                                          (subst (\ x ->
                                            ρ θS→unk · x ≐ [] ⟦
                                            ρ θS→unk · E ⟦ p ⟧e ⟧e)
                                            (unplug decomp2) dehole))))))

{- two specific examples of lifting a signal out of an evaluation context -}
ex6 : ∀ S p q -> CB (p ∥ q) ->
      (ρ []env · ((signl S p) ∥ q)) ≡ₑ (ρ []env · (signl S (p ∥ q))) # []
ex6 S p q CBp∥q =
  ex5 S p (signl S p ∥ q) (p ∥ q) ((epar₁ q) ∷ []) CBp∥q (depar₁ dehole) (depar₁ dehole)

ex7 : ∀ S p q -> CB (p >> q) ->
      (ρ []env · ((signl S p) >> q)) ≡ₑ (ρ []env · (signl S (p >> q))) # []
ex7 S p q CBp>>q =
  ex5 S p (signl S p >> q) (p >> q) ((eseq q) ∷ []) CBp>>q (deseq dehole) (deseq dehole)

{- pushing a seq into the bottom of a present

   This is something that our calculus cannot handle
   in general; this shows just a smaller case of
   the general relationship we'd like to prove,
   namely that, if we have correct binding:

      (present S ∣⇒ p ∣⇒ q) >> r)
      ≡ₑ
      present S ∣⇒ (p >> r) ∣⇒ (q >> r)
-}

ex8 : ∀ S p q r ->
    Signal.unwrap S ∉ (Canₛ p (Θ SigMap.[ S ↦ unknown ] [] [])) ->
    Signal.unwrap S ∉ (Canₛ q (Θ SigMap.[ S ↦ unknown ] [] [])) ->
            CB ((signl S (present S ∣⇒  p       ∣⇒  q)) >> r) ->
    (ρ []env · ((signl S (present S ∣⇒  p       ∣⇒  q)) >> r)) ≡ₑ
    (ρ []env ·  (signl S (present S ∣⇒ (p >> r) ∣⇒ (q  >> r)))) # []
ex8 S p q r s∉Canₛp s∉Canₛq CBall = calc where

  θS→unk : Env
  θS→unk = Θ SigMap.[ S ↦ Signal.unknown ] [] []

  S∈θS→unk : SigMap.∈Dom S (sig θS→unk)
  S∈θS→unk = sig-∈-single S Signal.unknown

  θS→unk[S]≡unk : sig-stats{S = S} θS→unk S∈θS→unk ≡ Signal.unknown
  θS→unk[S]≡unk = sig-stats-1map' S Signal.unknown S∈θS→unk

  θS→abs : Env
  θS→abs = set-sig{S} θS→unk S∈θS→unk Signal.absent

  S∈θS→abs : SigMap.∈Dom S (sig θS→abs)
  S∈θS→abs = sig-set-mono' {S} {S} {θS→unk} {Signal.absent} {S∈θS→unk} S∈θS→unk

  θS→abs[S]≡abs : sig-stats{S = S} θS→abs S∈θS→abs ≡ Signal.absent
  θS→abs[S]≡abs = sig-putget{S} {θS→unk} {Signal.absent} S∈θS→unk S∈θS→abs

  CB1 : ∀ {p q r BV FV} -> CorrectBinding ((signl S (present S ∣⇒ p ∣⇒ q)) >> r) BV FV ->
             CB (signl S (present S ∣⇒ p ∣⇒ q))
  CB1 {p} {q} {r} {.(BVp U̬ BVq)} {.(FVp U̬ FVq)}
         (CBseq{ps}{qs}{BVp}{BVq}{FVp}{FVq} CBall₁ CBall₂ BVp≠FVq) with
           BVFVcorrect (signl S (present S ∣⇒ p ∣⇒ q)) BVp FVp CBall₁
  ... | refl , refl = CBall₁

  CB2 : ∀ {p q BV FV} -> CorrectBinding (signl S (present S ∣⇒ p ∣⇒ q)) BV FV ->
        CB (present S ∣⇒ p ∣⇒ q)
  CB2 {p} {q} {.(+S S BV)} {.(FV |̌(+S S base))} (CBsig{p₁}{S}{BV}{FV} CBs) with
       BVFVcorrect (present S ∣⇒ p ∣⇒ q) BV FV CBs
  ... | refl , refl = CBs

  CB3 : ∀ {p q BV FV} -> CorrectBinding (present S ∣⇒ p ∣⇒ q) BV FV -> CB q
  CB3 {p} {q} {. (BVp U̬ BVq)} {.(+S S (FVp U̬ FVq))}
      (CBpresent{S}{p'}{q'}{BVp}{FVp}{BVq}{FVq} CBp CBq) with
      BVFVcorrect q BVq FVq CBq
  ... | refl , refl = CBq

  CB4 : ∀ {p q BV FV} -> CorrectBinding (present S ∣⇒ p ∣⇒ q) BV FV -> CB p
  CB4 {p} {q} {. (BVp U̬ BVq)} {.(+S S (FVp U̬ FVq))}
      (CBpresent{S}{p'}{q'}{BVp}{FVp}{BVq}{FVq} CBp CBq) with
      BVFVcorrect p BVp FVp CBp
  ... | refl , refl = CBp

  CB5 : ∀ {p q r BV FV} -> CorrectBinding ((signl S (present S ∣⇒ p ∣⇒ q)) >> r) BV FV -> CB r
  CB5 {p} {q} {r} {.(BVp U̬ BVq)} {.(FVp U̬ FVq)}
         (CBseq{ps}{qs}{BVp}{BVq}{FVp}{FVq} CBall₁ CBall₂ BVp≠FVq) with
           BVFVcorrect r BVq FVq CBall₂
  ... | refl , refl = CBall₂

  CB6 : ∀ {p q r BV FV} ->
        CorrectBinding ((signl S (present S ∣⇒ p ∣⇒ q)) >> r) BV FV ->
        (distinct (+S S ((BVars p) U̬ (BVars q))) (FVars r))
  CB6 {p} {q} {r} {.(BVp U̬ BVq)} {.(FVp U̬ FVq)}
         (CBseq{ps}{qs}{BVp}{BVq}{FVp}{FVq} CBall₁ CBall₂ BVp≠FVr) with
           BVFVcorrect r BVq FVq CBall₂ | BVFVcorrect (signl S (present S ∣⇒ p ∣⇒ q)) BVp FVp CBall₁
  ... | refl , refl | refl , refl = BVp≠FVr

  CBp : CB p
  CBp = (CB4 (CB2 (CB1 CBall)))

  CBq : CB q
  CBq = (CB3 (CB2 (CB1 CBall)))

  CBr = CB5 CBall

  S+BVp∪BVqdistinctFVr : distinct (+S S ((BVars p) U̬ (BVars q))) (FVars r)
  S+BVp∪BVqdistinctFVr = CB6 CBall

  BVp∪BVqdistinctFVr : distinct ((BVars p) U̬ (BVars q)) (FVars r)
  BVp∪BVqdistinctFVr =
    ⊆-respect-distinct-left ((λ x x₁ → there x₁) , (λ x x₁ → x₁) , (λ x z → z))
                            S+BVp∪BVqdistinctFVr

  S+BVqdistinctFVr : distinct (+S S (BVars q)) (FVars r)
  S+BVqdistinctFVr =
      ⊆-respect-distinct-left
      (f (proj₁ (BVars p)) (proj₁ (BVars q)) ,
       (λ x x₁ → ++⁺ʳ (proj₁ (proj₂ (BVars p))) x₁) ,
       (λ x x₁ → ++⁺ʳ (proj₂ (proj₂ (BVars p))) x₁))
      S+BVp∪BVqdistinctFVr where
   f : ∀ l m x ->
      Data.List.Any.Any (_≡_ x) ((Signal.unwrap S) ∷ m) →
      Data.List.Any.Any (_≡_ x) ((Signal.unwrap S) ∷ (l ++ m))
   f x l m (here px) = here px
   f x l m (there x∈0::l) = there (++⁺ʳ x x∈0::l)

  distinctBVpFVr : distinct (BVars p) (FVars r)
  distinctBVpFVr = ⊆-respect-distinct-left (∪ˡ ⊆-refl) BVp∪BVqdistinctFVr
  distinctBVqFVr : distinct (BVars q) (FVars r)
  distinctBVqFVr = ⊆-respect-distinct-left (∪ʳ (BVars p) ⊆-refl) BVp∪BVqdistinctFVr

  CBp>>r : CB (p >> r)
  CBp>>r = (CBseq CBp CBr distinctBVpFVr)
  CBq>>r : CB (q >> r)
  CBq>>r = (CBseq CBq CBr distinctBVqFVr)

  CBsym : CB (ρ []env · signl S (present S ∣⇒ p >> r ∣⇒ q >> r))
  CBsym = CBρ (CBsig (CBpresent CBp>>r CBq>>r))

  CBsignlSq>>r : CB (signl S q >> r)
  CBsignlSq>>r = CBseq (CBsig {S = S} CBq) CBr S+BVqdistinctFVr

  CBsignlS[q>>r] : CB (signl S (q >> r))
  CBsignlS[q>>r] = CBsig {S = S} CBq>>r

  CBseq->S∉Canₛr : ∀ {p q r} ->
          (BV : VarList) -> (FV : VarList) ->
          CorrectBinding ((signl S (present S ∣⇒  p       ∣⇒  q)) >> r) BV FV ->
          Signal.unwrap S ∉ (Canₛ r θS→unk)
  CBseq->S∉Canₛr {p} {q} {r} _ _
      (CorrectBinding.CBseq {FVq = FVr}
                            (CorrectBinding.CBsig CBpresentS∣⇒p∣⇒q)
                            CBr (BVp≠FVq-S , _ , _)) =
    λ s∈Canr → BVp≠FVq-S (Signal.unwrap S) (here refl) (canₛ-⊆-FV _ CBr S s∈Canr)


  s∉Canₛr : Signal.unwrap S ∉ (Canₛ r θS→unk)
  s∉Canₛr = CBseq->S∉Canₛr (BVars ((signl S (present S ∣⇒ p ∣⇒ q)) >> r))
                          (FVars ((signl S (present S ∣⇒ p ∣⇒ q)) >> r))
                          CBall

  s∉Canₛp>>r : Signal.unwrap S ∉ (Canₛ (p >> r) θS→unk)
  s∉Canₛp>>r with any (Code._≟_ Code.nothin) (Canₖ p θS→unk)
  s∉Canₛp>>r | yes 0∈Canp++Canr = nocando where
    nocando :  Data.List.Any.Any (_≡_ (Signal.unwrap S))
                                 ((Canₛ p θS→unk) ++ (Canₛ r θS→unk)) → ⊥
    nocando x with ++⁻ (Canₛ p θS→unk) x
    nocando x | inj₁ x₁ = s∉Canₛp x₁
    nocando x | inj₂ y =  s∉Canₛr y
  s∉Canₛp>>r | no ¬p = s∉Canₛp

  s∉Canₛq>>r : Signal.unwrap S ∉ (Canₛ (q >> r) θS→unk)
  s∉Canₛq>>r with any (Code._≟_ Code.nothin) (Canₖ q θS→unk)
  s∉Canₛq>>r | yes 0∈Canq++Canr = nocando where
    nocando :  Data.List.Any.Any (_≡_ (Signal.unwrap S))
                                 ((Canₛ q θS→unk) ++ (Canₛ r θS→unk)) → ⊥
    nocando x with ++⁻ (Canₛ q θS→unk) x
    nocando x | inj₁ x₁ = s∉Canₛq x₁
    nocando x | inj₂ y =  s∉Canₛr y
  s∉Canₛq>>r | no ¬p = s∉Canₛq

  calc : (ρ []env · ((signl S (present S ∣⇒  p       ∣⇒  q)     ) >> r)) ≡ₑ
         (ρ []env ·  (signl S (present S ∣⇒ (p >> r) ∣⇒ (q >> r)))) # []
  calc = ≡ₑtran {r = ρ []env · (signl S q) >> r}
                (≡ₑctxt (dcenv (dcseq₁ dchole)) (dcenv (dcseq₁ dchole))
                        (ex2 S p q _ (CBρ CBsignlSq>>r) s∉Canₛp s∉Canₛq))
                (≡ₑtran {r = ρ []env · (ρ θS→unk · q) >> r}
                        (≡ₑctxt (dcenv (dcseq₁ dchole))
                                       (dcenv (dcseq₁ dchole))
                                       (≡ₑstep [raise-signal]))
                (≡ₑtran {r = ρ θS→unk · (q >> r)}
                        (≡ₑstep ([merge] (deseq dehole)))
                (≡ₑsymm CBsym
                        (≡ₑtran {r = ρ []env · signl S (q >> r)}
                                (≡ₑctxt (dcenv dchole) (dcenv dchole)
                                        (ex2 S (p >> r) (q >> r) _
                                             (CBρ CBsignlS[q>>r])
                                            s∉Canₛp>>r s∉Canₛq>>r))
                       (≡ₑtran {r = ρ []env · (ρ θS→unk · q >> r)}
                               (≡ₑctxt (dcenv dchole) (dcenv dchole)
                                       (≡ₑstep [raise-signal]))
                       (≡ₑtran {r = ρ θS→unk · q >> r}
                               (≡ₑstep ([merge] dehole))
                        ≡ₑrefl))))))

{- rearranging signal forms -}
ex9 : ∀ S1 S2 p ->
     CB p ->
     signl S1 (signl S2 p) ≡ₑ signl S2 (signl S1 p) # []
ex9 S1 S2 p CBp =
  ≡ₑtran {r = ρ (Θ SigMap.[ S1 ↦ Signal.unknown ] [] []) · (signl S2 p)}
         (≡ₑstep [raise-signal])
 (≡ₑtran {r = (ρ Θ SigMap.[ S1 ↦ Signal.unknown ] [] [] ·
              (ρ Θ SigMap.[ S2 ↦ Signal.unknown ] [] [] · p))}
         (≡ₑctxt (dcenv dchole) (dcenv dchole) (≡ₑstep [raise-signal]))
 (≡ₑtran {r = (ρ (Θ SigMap.[ S1 ↦ Signal.unknown ] [] []) ←
               (Θ SigMap.[ S2 ↦ Signal.unknown ] [] []) ·
               p)}
         (≡ₑstep ([merge] dehole))
 (≡ₑsymm (CBsig (CBsig CBp))
         (≡ₑtran {r = ρ (Θ SigMap.[ S2 ↦ Signal.unknown ] [] []) · (signl S1 p)}
                 (≡ₑstep [raise-signal])
         (≡ₑtran {r = (ρ Θ SigMap.[ S2 ↦ Signal.unknown ] [] [] ·
                        (ρ Θ SigMap.[ S1 ↦ Signal.unknown ] [] [] · p))}
                 (≡ₑctxt (dcenv dchole) (dcenv dchole) (≡ₑstep [raise-signal]))
         (≡ₑtran {r = (ρ (Θ SigMap.[ S2 ↦ Signal.unknown ] [] []) ←
                        (Θ SigMap.[ S1 ↦ Signal.unknown ] [] []) ·
                          p)}
                 (≡ₑstep ([merge] dehole))
                 (map-order-irr S1 S2 p))))))) where

  distinct-Ss-env'' : ∀ S1 S2 S3 ->
     ¬ Signal.unwrap S1 ≡ Signal.unwrap S2 ->
     Data.List.Any.Any (_≡_ S3) (Signal.unwrap S1 ∷ []) ->
     Data.List.Any.Any (_≡_ S3) (Signal.unwrap S2 ∷ []) ->
     ⊥
  distinct-Ss-env'' S1 S2 S3 S1≠S2 (here S3=S1) (here S3=S2) rewrite S3=S1 = S1≠S2 S3=S2
  distinct-Ss-env'' S1 S2 S3 S1≠S2 (here px) (there ())
  distinct-Ss-env'' S1 S2 S3 S1≠S2 (there ()) S3∈Domθ2

  distinct-Ss-env' : ∀ S1 S2 S3 ->
     ¬ Signal.unwrap S1 ≡ Signal.unwrap S2 ->
     Data.List.Any.Any (_≡_ S3) (Signal.unwrap S1 ∷ []) ->
     S3 ∈ proj₁ (Dom (Θ SigMap.[ S2 ↦ Signal.unknown ] [] [])) ->
     ⊥
  distinct-Ss-env' S1 S2 S3 S1≠S2 S3∈Domθ1 S3∈Domθ2
     rewrite SigMap.keys-1map S2 Signal.unknown =
       distinct-Ss-env'' S1 S2 S3 S1≠S2 S3∈Domθ1 S3∈Domθ2

  distinct-Ss-env : ∀ S1 S2 S3 ->
     ¬ Signal.unwrap S1 ≡ Signal.unwrap S2 ->
     S3 ∈ proj₁ (Dom (Θ SigMap.[ S1 ↦ Signal.unknown ] [] [])) ->
     S3 ∈ proj₁ (Dom (Θ SigMap.[ S2 ↦ Signal.unknown ] [] [])) ->
     ⊥
  distinct-Ss-env S1 S2 S3 S1≠S2 S3∈Domθ1 S3∈Domθ2
    rewrite SigMap.keys-1map S1 Signal.unknown =
      distinct-Ss-env' S1 S2 S3 S1≠S2 S3∈Domθ1 S3∈Domθ2

  distinct-doms : ∀ S1 S2 ->
    ¬ (Signal.unwrap S1 ≡ Signal.unwrap S2) ->
    distinct (Env.Dom (Θ SigMap.[ S1 ↦ Signal.unknown ] [] []))
             (Env.Dom (Θ SigMap.[ S2 ↦ Signal.unknown ] [] []))
  distinct-doms S1 S2 S1≠S2 =
    (λ {S3 S3∈θ1 S3∈θ2 -> distinct-Ss-env S1 S2 S3 S1≠S2 S3∈θ1 S3∈θ2})
    ,
    (λ x₁ x₂ → λ ())
    ,
    (λ x₁ x₂ → λ ())

  map-order-irr' : ∀ S1 S2 ->
     (Θ SigMap.[ S1 ↦ Signal.unknown ] [] []) ←
     (Θ SigMap.[ S2 ↦ Signal.unknown ] [] [])
     ≡
     (Θ SigMap.[ S2 ↦ Signal.unknown ] [] []) ←
     (Θ SigMap.[ S1 ↦ Signal.unknown ] [] [])
  map-order-irr' S1 S2 with (Signal.unwrap S1) Nat.≟ (Signal.unwrap S2)
  map-order-irr' S1 S2 | yes S1=S2 rewrite S1=S2 = refl
  map-order-irr' S1 S2 | no ¬S1=S2 =  Env.←-comm
                               ((Θ SigMap.[ S1 ↦ Signal.unknown ] [] []))
                               ((Θ SigMap.[ S2 ↦ Signal.unknown ] [] []))
                               (distinct-doms S1 S2 ¬S1=S2)

  map-order-irr : ∀ S1 S2 p ->
       (ρ
         Θ SigMap.[ S2 ↦ Signal.unknown ] [] [] ←
         Θ SigMap.[ S1 ↦ Signal.unknown ] [] []
         · p)
        ≡ₑ
        (ρ
         Θ SigMap.[ S1 ↦ Signal.unknown ] [] [] ←
         Θ SigMap.[ S2 ↦ Signal.unknown ] [] []
         · p) # []
  map-order-irr S1 S2 p rewrite map-order-irr' S1 S2 = ≡ₑrefl 

{- dropping a loop whose body is just `exit` -}

ex10 : ∀ C n -> (loop (exit n)) ≡ₑ (exit n) # C
ex10 C n = ≡ₑtran (≡ₑstep [loop-unroll]) (≡ₑstep [loopˢ-exit])

{- (nothin ∥ p) ≡ₑ p, but only if we know that
   p goes to something that's done -}
ex11 : ∀ p q ->
  CB p -> done q -> p ≡ₑ q # [] ->
  (nothin ∥ p) ≡ₑ p # []
ex11 = calc where

  ex11-pq : ∀ q C -> done q -> (nothin ∥ q) ≡ₑ q # C
  ex11-pq .nothin C (dhalted hnothin) =
    ≡ₑtran (≡ₑstep [par-swap]) (≡ₑstep ([par-nothing] (dhalted hnothin)))
  ex11-pq .(exit n) C (dhalted (hexit n)) =
    ≡ₑstep ([par-nothing] (dhalted (hexit n)))
  ex11-pq q C (dpaused p/paused) =
   ≡ₑstep ([par-nothing] (dpaused p/paused))

  basealwaysdistinct : ∀ x -> distinct base x
  basealwaysdistinct x = (λ { z () x₂ }) , (λ { z () x₂ }) , (λ { z () x₂})

  CBp->CBnothingp : {r r′ : Term}
      {BVp FVp : Σ (List ℕ) (λ x → List ℕ × List ℕ)} →
      CorrectBinding r BVp FVp →
      r′ ≐ ceval (epar₂ nothin) ∷ [] ⟦ r ⟧c → CB r′
  CBp->CBnothingp {r} CBr r′dc
   with sym (unplugc r′dc) | BVFVcorrect _ _ _ CBr
  ... | refl | refl , refl
   = CBpar CBnothing CBr
      (basealwaysdistinct (BVars r))
      (basealwaysdistinct (BVars r))
      (basealwaysdistinct (FVars r))
      (λ { _ () _ })

  calc : ∀ p q ->
    CB p -> done q -> p ≡ₑ q # [] ->
    (nothin ∥ p) ≡ₑ p # []
  calc p q CBp doneq p≡ₑq =
    ≡ₑtran {r = (nothin ∥ q)}
           (≡ₑctxt (dcpar₂ dchole)
                   (dcpar₂ dchole)
                   (≡ₑ-context [] _ CBp->CBnothingp p≡ₑq))
           (≡ₑtran {r = q} (ex11-pq q [] doneq) (≡ₑsymm CBp p≡ₑq))

{- an emit (first) in sequence is the same as emit in parallel -}
ex12 : ∀ S p q ->
      CB p -> done q -> p ≡ₑ q # [] ->
      (signl S ((emit S) ∥ p)) ≡ₑ (signl S ((emit S) >> p)) # []
ex12 S p q CBp doneq p≡ₑq = calc where

  θS→unk : Env
  θS→unk = Θ SigMap.[ S ↦ Signal.unknown ] [] []

  S∈θS→unk : SigMap.∈Dom S (sig θS→unk)
  S∈θS→unk = sig-∈-single S Signal.unknown

  θS→unk[S]≡unk : sig-stats{S = S} θS→unk S∈θS→unk ≡ Signal.unknown
  θS→unk[S]≡unk = sig-stats-1map' S Signal.unknown S∈θS→unk

  θS→pre : Env
  θS→pre = set-sig{S} θS→unk S∈θS→unk Signal.present

  θS→unk[S]≠absent : ¬ sig-stats{S = S} θS→unk S∈θS→unk ≡ Signal.absent
  θS→unk[S]≠absent is rewrite θS→unk[S]≡unk = unknotabs is where
    unknotabs : Signal.unknown ≡ Signal.absent → ⊥
    unknotabs ()

  CBp->CBρθSp : {r r′ : Term}
      {BVp FVp : Σ (List ℕ) (λ x → List ℕ × List ℕ)} →
      CorrectBinding r BVp FVp → r′ ≐ cenv θS→pre ∷ [] ⟦ r ⟧c → CB r′
  CBp->CBρθSp {r} CBr r′dc
    with sym (unplugc r′dc) | BVFVcorrect _ _ _ CBr
  ... | refl | refl , refl = CBρ CBr

  basealwaysdistinct : ∀ x -> distinct base x
  basealwaysdistinct x = (λ { z () x₂ }) , (λ { z () x₂ }) , (λ { z () x₂})

  CBsiglSemitS>>p : CB (signl S (emit S >> p))
  CBsiglSemitS>>p =
    CBsig (CBseq CBemit CBp (basealwaysdistinct (FVars p)))

  calc : (signl S ((emit S) ∥ p)) ≡ₑ
         (signl S ((emit S) >> p)) # []
  calc =
     ≡ₑtran {r = ρ θS→unk · ((emit S) ∥ p)}
            (≡ₑstep [raise-signal])
    (≡ₑtran {r =  ρ θS→pre · (nothin ∥ p)}
            (≡ₑstep ([emit] S∈θS→unk θS→unk[S]≠absent (depar₁ dehole)))
    (≡ₑtran {r = ρ θS→pre · p}
            (≡ₑctxt (dcenv dchole) (dcenv dchole)
                    (≡ₑ-context [] (cenv _ ∷ [])
                                CBp->CBρθSp
                                (ex11 p q CBp doneq p≡ₑq)))
    (≡ₑsymm CBsiglSemitS>>p
            (≡ₑtran {r = ρ θS→unk · (emit S >> p)}
                    (≡ₑstep [raise-signal])
            (≡ₑtran {r = ρ θS→pre · nothin >> p}
                    (≡ₑstep ([emit] S∈θS→unk θS→unk[S]≠absent (deseq dehole)))
                    (≡ₑctxt (dcenv dchole) (dcenv dchole)
                            (≡ₑstep [seq-done])))))))
