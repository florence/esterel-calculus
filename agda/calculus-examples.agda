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

{-

This example is not true (and not provable under the current calculus)

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
           -}

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
ex2b : ∀ S p q C -> CB (C ⟦ signl S q ⟧c) ->
   Signal.unwrap S ∉ (Canₛ p (Θ SigMap.[ S ↦ unknown ] [] [])) ->
   Signal.unwrap S ∉ (Canₛ q (Θ SigMap.[ S ↦ unknown ] [] [])) ->
   signl S (present S ∣⇒ p ∣⇒ q) ≡ₑ
   signl S q # C
ex2b S p q C CBq s∉Canₛp s∉Canₛq = calc where

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

 bwd : signl S q ≡ₑ (ρ⟨ θS→abs , WAIT ⟩· q) # C
 bwd =
    ≡ₑtran (≡ₑstep [raise-signal])
   (≡ₑtran (≡ₑstep ([absence] S S∈θS→unk θS→unk[S]≡unk S∉Canθₛq))
    ≡ₑrefl)

 fwd : signl S (present S ∣⇒ p ∣⇒ q) ≡ₑ
       (ρ⟨ θS→abs , WAIT ⟩· q) # C
 fwd =
     ≡ₑtran (≡ₑstep [raise-signal])
    (≡ₑtran (≡ₑstep ([absence] S S∈θS→unk θS→unk[S]≡unk S∉CanθₛpresentSpq))
    (≡ₑtran (≡ₑstep ([is-absent] S S∈θS→abs θS→abs[S]≡abs dehole))
     ≡ₑrefl)) where

 calc :  signl S (present S ∣⇒ p ∣⇒ q) ≡ₑ
         signl S q # C
 calc = ≡ₑtran fwd (≡ₑsymm CBq bwd)

ex2 : ∀ S p q C ->
   CB (C ⟦ signl S q ⟧c) ->
   (∀ status -> Signal.unwrap S ∉ (Canₛ p (Θ SigMap.[ S ↦ status ] [] []))) ->
   (∀ status -> Signal.unwrap S ∉ (Canₛ q (Θ SigMap.[ S ↦ status ] [] []))) ->
   signl S (present S ∣⇒ p ∣⇒ q) ≡ₑ
   signl S q # C
ex2 S p q C CB noSp noSq = ex2b S p q C CB (noSp unknown) (noSq unknown)

{- 
 Although true, the this example is not provable under the current calculus 
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
    ≡ₑtran {r = ρ⟨ θS→unk · ((emit S >> p) ∥ q)}
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
                           -}

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
      (ρ⟨ []env , WAIT ⟩· q) ≡ₑ (ρ⟨ []env , WAIT ⟩· (signl S r)) # []
ex5 S p q r E CBr decomp1 decomp2 = calc where

  θS→unk : Env
  θS→unk = Θ SigMap.[ S ↦ Signal.unknown ] [] []

  replugit : q ≐ Data.List.map ceval E ⟦ signl S p ⟧c ->
             E ⟦ ρ⟨ θS→unk , WAIT ⟩· p ⟧e ≐ Data.List.map ceval E ⟦ ρ⟨ θS→unk , WAIT ⟩· p ⟧c
  replugit x = ⟦⟧e-to-⟦⟧c Erefl

  calc : (ρ⟨ []env , WAIT ⟩· q) ≡ₑ (ρ⟨ []env , WAIT ⟩· (signl S r)) # []
  calc =
    ≡ₑtran {r = ρ⟨ []env , WAIT ⟩· (E ⟦ (ρ⟨ θS→unk , WAIT ⟩· p) ⟧e)}
           (≡ₑctxt (dcenv (⟦⟧e-to-⟦⟧c decomp1))
                   (dcenv (replugit (⟦⟧e-to-⟦⟧c decomp1)))
                   (≡ₑstep [raise-signal]))
   (≡ₑtran {r = ρ⟨ θS→unk , WAIT ⟩· (E ⟦ p ⟧e)}
           (≡ₑstep ([merge]{E = E} Erefl))
           (≡ₑsymm (CBρ (CBsig CBr))
                 (≡ₑtran {r = ρ⟨ []env , WAIT ⟩· (ρ⟨ θS→unk , WAIT ⟩· r)}
                         (≡ₑctxt (dcenv dchole) (dcenv dchole) (≡ₑstep [raise-signal]))
                         (≡ₑstep ([merge] {E = []}
                                          (subst (\ x ->
                                            ρ⟨ θS→unk , WAIT ⟩· x ≐ [] ⟦
                                            ρ⟨ θS→unk , WAIT ⟩· E ⟦ p ⟧e ⟧e)
                                            (unplug decomp2) dehole))))))

{- two specific examples of lifting a signal out of an evaluation context -}
ex6 : ∀ S p q -> CB (p ∥ q) ->
      (ρ⟨ []env , WAIT ⟩· ((signl S p) ∥ q)) ≡ₑ (ρ⟨ []env , WAIT ⟩· (signl S (p ∥ q))) # []
ex6 S p q CBp∥q =
  ex5 S p (signl S p ∥ q) (p ∥ q) ((epar₁ q) ∷ []) CBp∥q (depar₁ dehole) (depar₁ dehole)

ex7 : ∀ S p q -> CB (p >> q) ->
      (ρ⟨ []env , WAIT ⟩· ((signl S p) >> q)) ≡ₑ (ρ⟨ []env , WAIT ⟩· (signl S (p >> q))) # []
ex7 S p q CBp>>q =
  ex5 S p (signl S p >> q) (p >> q) ((eseq q) ∷ []) CBp>>q (deseq dehole) (deseq dehole)

{- pushing a seq into a binding form (a signal in this case).

   this shows the need for the outer environment ρ [} · _
   in order to manipulate the environment.
-}
ex8-worker : ∀ {BV FV} S p q ->
      CorrectBinding ((signl S  p) >> q) BV FV ->
      (ρ⟨ []env , WAIT ⟩· (signl S  p) >> q) ≡ₑ
      (ρ⟨ []env , WAIT ⟩·  signl S (p  >> q)) # []
ex8-worker S p q (CBseq {BVp = BVsigS·p} {FVq = FVq} (CBsig {BV = BVp} CBp) CBq BVsigS·p≠FVq) =
             ≡ₑtran {r = ρ⟨ []env , WAIT ⟩· (ρ⟨ [S]-env S , WAIT ⟩· p) >> q} {C = []}
               (≡ₑctxt {C = []} {C′ = cenv []env WAIT ∷ ceval (eseq q) ∷ []}
                 Crefl Crefl
                 (≡ₑstep ([raise-signal] {p} {S})))
            (≡ₑtran {r = ρ⟨ [S]-env S , WAIT ⟩· p >> q} {C = []}
               (≡ₑstep ([merge] (deseq dehole)))
            (≡ₑsymm
              (CBρ
                (CBsig
                  (CBseq CBp CBq
                    (⊆-respect-distinct-left (∪ʳ (+S S base) ⊆-refl) BVsigS·p≠FVq))))
            (≡ₑtran {r = ρ⟨ []env , WAIT ⟩· (ρ⟨ [S]-env S , WAIT ⟩· p >> q)} {C = []}
              (≡ₑctxt {C = []} {C′ = cenv []env WAIT ∷ []}
                Crefl Crefl
                (≡ₑstep ([raise-signal] {p >> q} {S})))
            (≡ₑstep ([merge] dehole)))))

ex8 : ∀ S p q ->
             CB ((signl S  p) >> q) ->
      (ρ⟨ []env , WAIT ⟩· (signl S  p) >> q) ≡ₑ
      (ρ⟨ []env , WAIT ⟩·  signl S (p  >> q)) # []
ex8 S p q cb = ex8-worker S p q cb

{- rearranging signal forms -}
ex9 : ∀ S1 S2 p ->
     CB p ->
     signl S1 (signl S2 p) ≡ₑ signl S2 (signl S1 p) # []
ex9 S1 S2 p CBp =
  ≡ₑtran {r = ρ⟨ (Θ SigMap.[ S1 ↦ Signal.unknown ] [] []) , WAIT ⟩· (signl S2 p)}
         (≡ₑstep [raise-signal])
 (≡ₑtran {r = (ρ⟨ Θ SigMap.[ S1 ↦ Signal.unknown ] [] [] , WAIT ⟩·
              (ρ⟨ Θ SigMap.[ S2 ↦ Signal.unknown ] [] [] , WAIT ⟩· p))}
         (≡ₑctxt (dcenv dchole) (dcenv dchole) (≡ₑstep [raise-signal]))
 (≡ₑtran {r = (ρ⟨ (Θ SigMap.[ S1 ↦ Signal.unknown ] [] []) ←
               (Θ SigMap.[ S2 ↦ Signal.unknown ] [] []) , A-max WAIT WAIT ⟩·
               p)}
         (≡ₑstep ([merge] dehole))
 (≡ₑsymm (CBsig (CBsig CBp))
         (≡ₑtran {r = ρ⟨ (Θ SigMap.[ S2 ↦ Signal.unknown ] [] []) , WAIT ⟩· (signl S1 p)}
                 (≡ₑstep [raise-signal])
         (≡ₑtran {r = (ρ⟨ Θ SigMap.[ S2 ↦ Signal.unknown ] [] [] , WAIT ⟩·
                        (ρ⟨ Θ SigMap.[ S1 ↦ Signal.unknown ] [] [] , WAIT ⟩· p))}
                 (≡ₑctxt (dcenv dchole) (dcenv dchole) (≡ₑstep [raise-signal]))
         (≡ₑtran {r = (ρ⟨ (Θ SigMap.[ S2 ↦ Signal.unknown ] [] []) ←
                        (Θ SigMap.[ S1 ↦ Signal.unknown ] [] []) ,
                        A-max WAIT WAIT ⟩·
                          p)}
                 (≡ₑstep ([merge] dehole))
                 (map-order-irr S1 S2 WAIT p))))))) where

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

  map-order-irr : ∀ S1 S2 A p ->
       (ρ⟨
         Θ SigMap.[ S2 ↦ Signal.unknown ] [] [] ←
         Θ SigMap.[ S1 ↦ Signal.unknown ] [] []
         ,
         A ⟩· p)
        ≡ₑ
        (ρ⟨
         Θ SigMap.[ S1 ↦ Signal.unknown ] [] [] ←
         Θ SigMap.[ S2 ↦ Signal.unknown ] [] []
         ,
         A ⟩· p) # []
  map-order-irr S1 S2 A p rewrite map-order-irr' S1 S2 = ≡ₑrefl 

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

{- although true, can no longer prove
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

-}
