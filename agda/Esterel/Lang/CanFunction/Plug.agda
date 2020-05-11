module Esterel.Lang.CanFunction.Plug where

open import Data.Nat using (_+_ ; suc)
open import Function using (_∋_ ; _∘_ ; id ; _$_)
open import Data.Nat.Properties.Simple using ( +-comm ; +-assoc)
open import utility
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Lang.CanFunction
open import Esterel.Environment as Env
open import Esterel.Context
open import Esterel.Context.Properties
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List using ([] ; [_] ; _∷_ ; List ; _++_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; subst ; cong ; trans ; module ≡-Reasoning ; cong₂ ; subst₂ ; inspect)
open import Data.Empty
open import Esterel.Lang.Binding
open import Data.Maybe using ( nothing ; just )
open import Data.List.Any
open import Data.List.Any.Properties
  renaming (++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ )
open import Esterel.Lang.CanFunction.SetSigMonotonic

open ≡-Reasoning using (_≡⟨_⟩_ ; _≡⟨⟩_ ; _∎)

open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Data.FiniteMap
import Data.OrderedListMap as OMap
open import Data.Nat as Nat using (ℕ)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ ; _≟ₛₜ_)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)
open import Esterel.CompletionCode as Code renaming (CompletionCode to Code)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM
open ListSet Code._≟_
module NSet = ListSet Nat._≟_

canθₖ-plug : ∀ S' sigs → ∀ C p q
             → (Canₖq⊆Canₖp : ∀ θ k → k ∈ (Canₖ q θ) → k ∈ (Canₖ p θ))
             → (Canₛq⊆Canₛp : ∀ θ S → S ∈ (Canₛ q θ) → S ∈ (Canₛ p θ))
             → (∀ θ k → k ∈ (Canθₖ sigs S' (C ⟦ q ⟧c) θ) → k ∈ (Canθₖ sigs S' (C ⟦ p ⟧c) θ))

canθₛ-plug : ∀ S' sigs → ∀ C p q
             → (Canₛq⊆Canₛp : ∀ θ S → S ∈ (Canₛ q θ) → S ∈ (Canₛ p θ))
             → (Canₖq⊆Canₖp : ∀ θ k → k ∈ (Canₖ q θ) → k ∈ (Canₖ p θ))
             → (∀ θ k → k ∈ (Canθₛ sigs S' (C ⟦ q ⟧c) θ) → k ∈ (Canθₛ sigs S' (C ⟦ p ⟧c) θ))
canθₛₕ-plug : ∀ S' sigs → ∀ C p q
              → (Canₛₕq⊆Canₛₕp : ∀ θ → (Canₛₕ q θ) ⊆¹ (Canₛₕ p θ))
              → (Canₛq⊆Canₛp : ∀ θ k → k ∈ (Canₖ q θ) → k ∈ (Canₖ p θ))
              → (Canₖq⊆Canₖp : ∀ θ S → S ∈ (Canₛ q θ) → S ∈ (Canₛ p θ))
              → (∀ θ k → k ∈ (Canθₛₕ sigs S' (C ⟦ q ⟧c) θ) → k ∈ (Canθₛₕ sigs S' (C ⟦ p ⟧c) θ))



canₛₕ-plug : ∀ C p q
           → (Canₛₕq⊆Canₛₕp : ∀ θ → (Canₛₕ q θ) ⊆¹ (Canₛₕ p θ))
           → (∀ θ k → k ∈ (Canₖ q θ) → k ∈ (Canₖ p θ))
           → (Canₛq⊆Canₛp : ∀ θ → (Canₛ q θ) ⊆¹ (Canₛ p θ))
           → (∀ θ → (Canₛₕ (C ⟦ q ⟧c) θ) ⊆¹ (Canₛₕ (C ⟦ p ⟧c) θ))

canₖ-plug : ∀ C p q
            → (Canₖq⊆Canₖp : ∀ θ k → k ∈ (Canₖ q θ) → k ∈ (Canₖ p θ))
            → (Canₛq⊆Canₛp : ∀ θ S → S ∈ (Canₛ q θ) → S ∈ (Canₛ p θ))
            → (∀ θ k → k ∈ (Canₖ (C ⟦ q ⟧c) θ) → k ∈ (Canₖ (C ⟦ p ⟧c) θ))
canₛ-plug : ∀ C p q
            → (Canₛq⊆Canₛp : ∀ θ → (Canₛ q θ) ⊆¹ (Canₛ p θ))
            → (∀ θ k → k ∈ (Canₖ q θ) → k ∈ (Canₖ p θ))
            → (∀ θ → (Canₛ (C ⟦ q ⟧c) θ) ⊆¹ (Canₛ (C ⟦ p ⟧c) θ))

canθₖ-plug S' [] C p q Canₖq⊆Canₖp Canₛq⊆Canₛp = canₖ-plug C p q Canₖq⊆Canₖp Canₛq⊆Canₛp
canθₖ-plug S' (just Signal.present ∷ sigs) C p q Canₖq⊆Canₖp Canₛq⊆Canₛp θ = canθₖ-plug (suc S') sigs C p q Canₖq⊆Canₖp Canₛq⊆Canₛp (θ ← _)
canθₖ-plug S' (just Signal.absent ∷ sigs) C p q Canₖq⊆Canₖp Canₛq⊆Canₛp θ = canθₖ-plug (suc S') sigs C p q Canₖq⊆Canₖp Canₛq⊆Canₛp (θ ← _)
canθₖ-plug S' (nothing ∷ sigs) C p q Canₖq⊆Canₖp Canₛq⊆Canₛp = canθₖ-plug (suc S') sigs C p q Canₖq⊆Canₖp Canₛq⊆Canₛp
canθₖ-plug S' (just Signal.unknown ∷ sigs) C p q Canₖq⊆Canₖp Canₛq⊆Canₛp θ
  with any (Nat._≟_ S') (Canθₛ sigs (suc S') (C ⟦ p ⟧c) (θ ← ([S]-env (S' ₛ))))
     | any (Nat._≟_ S') (Canθₛ sigs (suc S') (C ⟦ q ⟧c) (θ ← ([S]-env (S' ₛ))))
canθₖ-plug S' (just Signal.unknown ∷ sigs) C p q Canₖq⊆Canₖp Canₛq⊆Canₛp θ | yes p₁ | (yes p₂) = canθₖ-plug (suc S') sigs C p q Canₖq⊆Canₖp Canₛq⊆Canₛp (θ ← _)
canθₖ-plug S' (just Signal.unknown ∷ sigs) C p q Canₖq⊆Canₖp Canₛq⊆Canₛp θ | yes p₁ | (no ¬p)
  with sig-←-monoʳ (S' ₛ) ([S]-env (S' ₛ)) θ (sig-∈-single (S' ₛ) Signal.unknown)
... | S'∈θ←[S]env
  rewrite ((θ ← [S]-env-absent (S' ₛ)) ≡ (set-sig{S' ₛ} (θ ← [S]-env (S' ₛ)) S'∈θ←[S]env Signal.absent)
            ∋
            (θ ← [S]-env-absent (S' ₛ))
             ≡⟨ cong (θ ←_) (sym (←-single-overwrite-sig (S' ₛ) Signal.unknown
                                    ([S]-env-absent (S' ₛ)) ((sig-∈-single (S' ₛ) Signal.absent)))) ⟩
             (θ ← (([S]-env (S' ₛ)) ← [S]-env-absent (S' ₛ)))
             ≡⟨ ←-assoc θ ([S]-env (S' ₛ)) ([S]-env-absent (S' ₛ)) ⟩
             ((θ ← ([S]-env (S' ₛ))) ← ([S]-env-absent (S' ₛ)))
             ≡⟨ sym (sig-set=← (θ ← [S]-env (S' ₛ)) (S' ₛ) Signal.absent  S'∈θ←[S]env) ⟩
             (set-sig{S' ₛ} (θ ← [S]-env (S' ₛ)) S'∈θ←[S]env Signal.absent) ∎)

  with canθₖ-set-sig-monotonic sigs (suc S') (C ⟦ q ⟧c) (S' ₛ) (θ ← [S]-env (S' ₛ))
                               S'∈θ←[S]env Signal.absent
                               (trans (sig-stats-←-right-irr' (S' ₛ) θ ([S]-env (S' ₛ)) (sig-∈-single (S' ₛ) Signal.unknown) S'∈θ←[S]env) (sig-stats-1map' (S' ₛ) Signal.unknown ((sig-∈-single (S' ₛ) Signal.unknown))))
                               (n∉map-suc-n-+ S' (SigM.Dom' sigs))
... | Canabsq⊂Canunq
   = λ k x → (canθₖ-plug (suc S') sigs C p q Canₖq⊆Canₖp Canₛq⊆Canₛp (θ ← _)) k (Canabsq⊂Canunq k x)
canθₖ-plug S' (just Signal.unknown ∷ sigs) C p q Canₖq⊆Canₖp Canₛq⊆Canₛp θ | no ¬p | (yes p₁)
  = ⊥-elim (¬p ((canθₛ-plug (suc S') sigs C p q Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)) _ p₁ ))
canθₖ-plug S' (just Signal.unknown ∷ sigs) C p q Canₖq⊆Canₖp Canₛq⊆Canₛp θ | no ¬p | (no ¬p₁) = canθₖ-plug (suc S') sigs C p q Canₖq⊆Canₖp Canₛq⊆Canₛp (θ ← _)

canθₛ-plug S' [] C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ = canₛ-plug C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ
canθₛ-plug S' (nothing ∷ sigs) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ = canθₛ-plug (suc S') sigs C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ
canθₛ-plug S' (just Signal.present ∷ sigs) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ = canθₛ-plug (suc S') sigs C p q Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)
canθₛ-plug S' (just Signal.absent ∷ sigs) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ = canθₛ-plug (suc S') sigs C p q Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)
canθₛ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ
  with any (Nat._≟_ S') (Canθₛ sigs (suc S') (C ⟦ p ⟧c) (θ ← ([S]-env (S' ₛ))))
     | any (Nat._≟_ S') (Canθₛ sigs (suc S') (C ⟦ q ⟧c) (θ ← ([S]-env (S' ₛ))))
canθₛ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ | yes p₁ | (yes p₂) = canθₛ-plug (suc S') sigs C p q Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)
canθₛ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ | yes p₁ | (no ¬p)
  with sig-←-monoʳ (S' ₛ) ([S]-env (S' ₛ)) θ (sig-∈-single (S' ₛ) Signal.unknown)
... | S'∈θ←[S]env
  rewrite ((θ ← [S]-env-absent (S' ₛ)) ≡ (set-sig{S' ₛ} (θ ← [S]-env (S' ₛ)) S'∈θ←[S]env Signal.absent)
            ∋
            (θ ← [S]-env-absent (S' ₛ))
             ≡⟨ cong (θ ←_) (sym (←-single-overwrite-sig (S' ₛ) Signal.unknown
                                    ([S]-env-absent (S' ₛ)) ((sig-∈-single (S' ₛ) Signal.absent)))) ⟩
             (θ ← (([S]-env (S' ₛ)) ← [S]-env-absent (S' ₛ)))
             ≡⟨ ←-assoc θ ([S]-env (S' ₛ)) ([S]-env-absent (S' ₛ)) ⟩
             ((θ ← ([S]-env (S' ₛ))) ← ([S]-env-absent (S' ₛ)))
             ≡⟨ sym (sig-set=← (θ ← [S]-env (S' ₛ)) (S' ₛ) Signal.absent  S'∈θ←[S]env) ⟩
             (set-sig{S' ₛ} (θ ← [S]-env (S' ₛ)) S'∈θ←[S]env Signal.absent) ∎)
   with canθₛ-set-sig-monotonic sigs (suc S') (C ⟦ q ⟧c) (S' ₛ) (θ ← [S]-env (S' ₛ))
                               S'∈θ←[S]env Signal.absent
                               (trans (sig-stats-←-right-irr' (S' ₛ) θ ([S]-env (S' ₛ)) (sig-∈-single (S' ₛ) Signal.unknown) S'∈θ←[S]env) (sig-stats-1map' (S' ₛ) Signal.unknown ((sig-∈-single (S' ₛ) Signal.unknown))))
                               (n∉map-suc-n-+ S' (SigM.Dom' sigs))
... | Canabsq⊂Canunq
   = λ k x → (canθₛ-plug (suc S') sigs C p q Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)) k (Canabsq⊂Canunq k x)

canθₛ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ | no ¬p | (yes p₁)
  = ⊥-elim (¬p ((canθₛ-plug (suc S') sigs) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _) _ p₁))
canθₛ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ | no ¬p | (no ¬p₁) = canθₛ-plug (suc S') sigs C p q Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)

canθₛₕ-plug S' [] C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ = canₛₕ-plug C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ
canθₛₕ-plug S' (nothing ∷ sigs) C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ = canθₛₕ-plug (suc S') sigs C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ
canθₛₕ-plug S' (just Signal.present ∷ sigs) C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ = canθₛₕ-plug (suc S') sigs C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)
canθₛₕ-plug S' (just Signal.absent ∷ sigs) C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ = canθₛₕ-plug (suc S') sigs C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)
canθₛₕ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ
  with any (Nat._≟_ S') (Canθₛ sigs (suc S') (C ⟦ p ⟧c) (θ ← ([S]-env (S' ₛ))))
     | any (Nat._≟_ S') (Canθₛ sigs (suc S') (C ⟦ q ⟧c) (θ ← ([S]-env (S' ₛ))))
canθₛₕ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ | yes p₁ | (yes p₂) =  canθₛₕ-plug (suc S') sigs C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)
canθₛₕ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp Canₛq⊆Canₛp θ | yes p₁ | (no ¬p)
  with sig-←-monoʳ (S' ₛ) ([S]-env (S' ₛ)) θ (sig-∈-single (S' ₛ) Signal.unknown)
... | S'∈θ←[S]env
  rewrite ((θ ← [S]-env-absent (S' ₛ)) ≡ (set-sig{S' ₛ} (θ ← [S]-env (S' ₛ)) S'∈θ←[S]env Signal.absent)
            ∋
            (θ ← [S]-env-absent (S' ₛ))
             ≡⟨ cong (θ ←_) (sym (←-single-overwrite-sig (S' ₛ) Signal.unknown
                                    ([S]-env-absent (S' ₛ)) ((sig-∈-single (S' ₛ) Signal.absent)))) ⟩
             (θ ← (([S]-env (S' ₛ)) ← [S]-env-absent (S' ₛ)))
             ≡⟨ ←-assoc θ ([S]-env (S' ₛ)) ([S]-env-absent (S' ₛ)) ⟩
             ((θ ← ([S]-env (S' ₛ))) ← ([S]-env-absent (S' ₛ)))
             ≡⟨ sym (sig-set=← (θ ← [S]-env (S' ₛ)) (S' ₛ) Signal.absent  S'∈θ←[S]env) ⟩
             (set-sig{S' ₛ} (θ ← [S]-env (S' ₛ)) S'∈θ←[S]env Signal.absent) ∎)
                with canθₛₕ-set-sig-monotonic sigs (suc S') (C ⟦ q ⟧c) (S' ₛ) (θ ← [S]-env (S' ₛ))
                               S'∈θ←[S]env Signal.absent
                               (trans (sig-stats-←-right-irr' (S' ₛ) θ ([S]-env (S' ₛ)) (sig-∈-single (S' ₛ) Signal.unknown) S'∈θ←[S]env) (sig-stats-1map' (S' ₛ) Signal.unknown ((sig-∈-single (S' ₛ) Signal.unknown))))
                               (n∉map-suc-n-+ S' (SigM.Dom' sigs))
... |  Canabsq⊂Canunq
   = λ k x → (canθₛₕ-plug (suc S') sigs C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp Canₛq⊆Canₛp (θ ← _)) k (Canabsq⊂Canunq k x)

canθₛₕ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ | no ¬p | (yes p₁)
  = ⊥-elim (¬p (canθₛ-plug (suc S') sigs C p q Canₖq⊆Canₖp Canₛq⊆Canₛp (θ ← _) _ p₁))
canθₛₕ-plug S' (just Signal.unknown ∷ sigs) C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp θ | no ¬p | (no ¬p₁) = canθₛₕ-plug (suc S') sigs C p q Canₛₕq⊆Canₛₕp Canₛq⊆Canₛp Canₖq⊆Canₖp (θ ← _)


canₖ-plug [] p q Canₖq⊆Canₖp _ = Canₖq⊆Canₖp
canₖ-plug (ceval (epar₁ q) ∷ C) p q₁ Canₖq⊆Canₖp ⊂s θ = map-mono² Code._⊔_ (canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ) (λ x y → y)
canₖ-plug (ceval (epar₂ p) ∷ C) p₁ q Canₖq⊆Canₖp ⊂s θ = map-mono²{xs = Canₖ p θ} Code._⊔_ (λ x y → y) (canₖ-plug C p₁ q Canₖq⊆Canₖp ⊂s θ)
canₖ-plug (ceval (eloopˢ q) ∷ C) p q₁ Canₖq⊆Canₖp ⊂s θ = canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ
canₖ-plug (ceval (eseq q) ∷ C) p q₁ Canₖq⊆Canₖp ⊂s θ with any (Code.nothin Code.≟_) (Canₖ (C ⟦ p ⟧c) θ) | any (Code.nothin Code.≟_) (Canₖ (C ⟦ q₁ ⟧c) θ)
... | yes 0∈CanC⟦p⟧ | yes 0∈CanC⟦q⟧ = codesub++both ((codesub- Code.nothin (canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ))) (λ x y → y)
... | yes 0∈CanC⟦p⟧ | no  0∉CanC⟦q⟧ = λ k x → ++ˡ (set-remove-not-removed{Code.nothin}{k} (λ {refl → 0∉CanC⟦q⟧ x}) (canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ _ x))
... | no  0∉CanC⟦p⟧ | yes 0∈CanC⟦q⟧ = ⊥-elim (0∉CanC⟦p⟧ (canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ _ 0∈CanC⟦q⟧))
... | no  0∉CanC⟦p⟧ | no  0∉CanC⟦q⟧ = canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ
canₖ-plug (ceval (esuspend S) ∷ C) p q Canₖq⊆Canₖp ⊂s = canₖ-plug C p q Canₖq⊆Canₖp ⊂s
canₖ-plug (ceval etrap ∷ C) p q Canₖq⊆Canₖp ⊂s =   λ θ →  map-mono Code.↓* (canₖ-plug C p q Canₖq⊆Canₖp ⊂s θ)
canₖ-plug (csignl S ∷ C) p q Canₖq⊆Canₖp ⊂s θ = canθₖ-plug 0 (sig ([S]-env S)) C p q Canₖq⊆Canₖp ⊂s θ
canₖ-plug (cpresent₁ S q ∷ C) p q₁ Canₖq⊆Canₖp ⊂s θ with Sig∈ S θ
... | no  S∉Domθ = codesub++both (canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ) (λ x y → y)
... | yes S∈Domθ with (Signal.present ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ
... | no  _ with (Signal.absent ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = λ k z → z
... | no  _ = codesub++both (canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ) (λ x y → y)
canₖ-plug (cpresent₂ S p₁ ∷ C) p q Canₖq⊆Canₖp ⊂s θ with Sig∈ S θ
... | no  S∉Domθ = codesub++both{a = Canₖ p₁ θ} (λ x y → y) (canₖ-plug C p q Canₖq⊆Canₖp ⊂s θ)
... | yes S∈Domθ with (Signal.present ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = λ x y → y
... | no  _ with (Signal.absent ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = canₖ-plug C p q Canₖq⊆Canₖp ⊂s θ
... | no  _ = codesub++both{a = Canₖ p₁ θ} (λ x y → y) (canₖ-plug C p q Canₖq⊆Canₖp ⊂s θ)
canₖ-plug (cloop ∷ C) p q Canₖq⊆Canₖp ⊂s = (canₖ-plug C p q Canₖq⊆Canₖp ⊂s)
canₖ-plug (cloopˢ₂ p ∷ C) p₁ q Canₖq⊆Canₖp ⊂s θ = λ k z → z 
canₖ-plug (cseq₂ p ∷ C) p₁ q Canₖq⊆Canₖp ⊂s θ with any (Code.nothin Code.≟_) (Canₖ p θ)
... | yes 0∈Canp = codesub++both{a = set-remove (Canₖ p θ) Code.nothin } (λ x y → y) (canₖ-plug C p₁ q Canₖq⊆Canₖp ⊂s θ)
... | no  0∉Canp = λ x y → y
canₖ-plug (cshared s e ∷ C) p q Canₖq⊆Canₖp ⊂s = (canₖ-plug C p q Canₖq⊆Canₖp ⊂s)
canₖ-plug (cvar x e ∷ C) p q Canₖq⊆Canₖp ⊂s = (canₖ-plug C p q Canₖq⊆Canₖp ⊂s)
canₖ-plug (cif₁ x q ∷ C) p q₁ Canₖq⊆Canₖp ⊂s θ = codesub++both (canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂s θ) (λ x y → y)
canₖ-plug (cif₂ x p ∷ C) p₁ q Canₖq⊆Canₖp ⊂s θ = codesub++both{a = Canₖ p θ} (λ x y → y) (canₖ-plug C p₁ q Canₖq⊆Canₖp ⊂s θ)
canₖ-plug (cenv θ₁ A ∷ C) p q Canₖq⊆Canₖp ⊂s θ = canθₖ-plug 0 (sig θ₁) C p q Canₖq⊆Canₖp ⊂s θ

canₛ-plug [] p q Canₛq⊆Canₛp Canₖq⊆Canₖp = Canₛq⊆Canₛp
canₛ-plug (ceval (epar₁ q) ∷ C) p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ = ∪¹-respect-⊆¹-left (canₛ-plug C p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
canₛ-plug (ceval (epar₂ p) ∷ C) p₁ q Canₛq⊆Canₛp Canₖq⊆Canₖp θ = ∪¹-respect-⊆¹-right (Canₛ p θ) (canₛ-plug C p₁ q Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
canₛ-plug (ceval (eloopˢ q) ∷ C) p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ = canₛ-plug C p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ
canₛ-plug (ceval (eseq q) ∷ C) p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ with any (Code.nothin Code.≟_) (Canₖ (C ⟦ p ⟧c) θ) | any (Code.nothin Code.≟_) (Canₖ (C ⟦ q₁ ⟧c) θ)
... | yes 0∈CanC⟦p⟧ | yes 0∈CanC⟦q⟧ = ∪¹-respect-⊆¹-left (canₛ-plug C p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
... | yes 0∈CanC⟦p⟧ | no  0∉CanC⟦q⟧ = λ S x → (++ˡ (canₛ-plug C p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ S x))
... | no  0∉CanC⟦p⟧ | yes 0∈CanC⟦q⟧ =  ⊥-elim (0∉CanC⟦p⟧ (canₖ-plug C p q₁ Canₖq⊆Canₖp Canₛq⊆Canₛp θ _ 0∈CanC⟦q⟧))
... | no  0∉CanC⟦p⟧ | no  0∉CanC⟦q⟧ = (canₛ-plug C p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ)

--  set-subtract-merge : ∀ {xs ys z} → z ∈ set-subtract xs ys → (z ∈ xs) × (z ∉ ys)

canₛ-plug (ceval (esuspend S) ∷ C) p q Canₛq⊆Canₛp Canₖq⊆Canₖp = (canₛ-plug C p q Canₛq⊆Canₛp Canₖq⊆Canₖp)
canₛ-plug (ceval etrap ∷ C) p q Canₛq⊆Canₛp Canₖq⊆Canₖp = (canₛ-plug C p q Canₛq⊆Canₛp Canₖq⊆Canₖp)
canₛ-plug (csignl (S ₛ) ∷ C) p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ S' S'∈CanC⟦q⟧
   = NSet.set-remove-not-removed ((¬ S ≡ S') ∋ NSet.set-remove-not-eq{S'}{S}{Canθₛ (sig ([S]-env (S ₛ))) 0 (C ⟦ q ⟧c) θ} S'∈CanC⟦q⟧)
                                  ((canθₛ-plug 0 (sig ([S]-env (S ₛ))) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ) S' ( (NSet.set-remove-mono-∈ S S'∈CanC⟦q⟧) ))


canₛ-plug (cpresent₁ S q ∷ C) p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ with Sig∈ S θ
... | no  S∉Domθ = ∪¹-respect-⊆¹-left (canₛ-plug C p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
... | yes S∈Domθ with (Signal.present ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = (canₛ-plug C p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
... | no  _ with (Signal.absent ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = λ k z → z
... | no  _ = ∪¹-respect-⊆¹-left (canₛ-plug C p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
canₛ-plug (cpresent₂ S p₁ ∷ C) p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ with Sig∈ S θ
... | no  S∉Domθ = ∪¹-respect-⊆¹-right (Canₛ p₁ θ) (canₛ-plug C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
... | yes S∈Domθ with (Signal.present ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = λ x y → y
... | no  _ with (Signal.absent ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = (canₛ-plug C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
... | no  _ = ∪¹-respect-⊆¹-right (Canₛ p₁ θ) (canₛ-plug C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
canₛ-plug (cloop ∷ C) p q Canₛq⊆Canₛp Canₖq⊆Canₖp = (canₛ-plug C p q Canₛq⊆Canₛp Canₖq⊆Canₖp)
canₛ-plug (cloopˢ₂ p ∷ C) p₁ q Canₛq⊆Canₛp Canₖq⊆Canₖp θ = λ x z → z
canₛ-plug (cseq₂ p ∷ C) p₁ q Canₛq⊆Canₛp Canₖq⊆Canₖp θ with any (Code.nothin Code.≟_) (Canₖ p θ)
... | yes 0∈Canp = ∪¹-respect-⊆¹-right (Canₛ p θ) (canₛ-plug C p₁ q Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
... | no  0∉Canp = λ x y → y
canₛ-plug (cshared s e ∷ C) p q Canₛq⊆Canₛp Canₖq⊆Canₖp = (canₛ-plug C p q Canₛq⊆Canₛp Canₖq⊆Canₖp)
canₛ-plug (cvar x e ∷ C) p q Canₛq⊆Canₛp Canₖq⊆Canₖp = (canₛ-plug C p q Canₛq⊆Canₛp Canₖq⊆Canₖp)
canₛ-plug (cif₁ x q ∷ C) p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ = ∪¹-respect-⊆¹-left (canₛ-plug C p q₁ Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
canₛ-plug (cif₂ x p ∷ C) p₁ q Canₛq⊆Canₛp Canₖq⊆Canₖp θ = ∪¹-respect-⊆¹-right (Canₛ p θ) (canₛ-plug C p₁ q Canₛq⊆Canₛp Canₖq⊆Canₖp θ)
canₛ-plug (cenv θ₁ A ∷ C) p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ =   ⊆¹-respect-|¹ (fst $ Dom θ₁) (canθₛ-plug 0 (sig θ₁) C p q Canₛq⊆Canₛp Canₖq⊆Canₖp θ)

canₛₕ-plug [] p q Canₛₕq⊆Canₛₕp Canₖₕq⊆Canₖₕp ⊂S = Canₛₕq⊆Canₛₕp
canₛₕ-plug (ceval (epar₁ q) ∷ C) p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ = ∪¹-respect-⊆¹-left (canₛₕ-plug C p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
canₛₕ-plug (ceval (epar₂ p) ∷ C) p₁ q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ = ∪¹-respect-⊆¹-right (Canₛₕ p θ) (canₛₕ-plug C p₁ q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
canₛₕ-plug (ceval (eloopˢ q) ∷ C) p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ = canₛₕ-plug C p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ
canₛₕ-plug (ceval (eseq q) ∷ C) p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ with any (Code.nothin Code.≟_) (Canₖ (C ⟦ p ⟧c) θ) | any (Code.nothin Code.≟_) (Canₖ (C ⟦ q₁ ⟧c) θ)
... | yes 0∈CanC⟦p⟧ | yes 0∈CanC⟦q⟧ = ∪¹-respect-⊆¹-left (canₛₕ-plug C p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
... | yes 0∈CanC⟦p⟧ | no  0∉CanC⟦q⟧ = λ S x → (++ˡ (canₛₕ-plug C p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ S x))
... | no  0∉CanC⟦p⟧ | yes 0∈CanC⟦q⟧ =  ⊥-elim (0∉CanC⟦p⟧ (canₖ-plug C p q₁ Canₖq⊆Canₖp ⊂S θ _ 0∈CanC⟦q⟧))
... | no  0∉CanC⟦p⟧ | no  0∉CanC⟦q⟧ = (canₛₕ-plug C p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)

canₛₕ-plug (ceval (esuspend S) ∷ C) p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S = (canₛₕ-plug C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S)
canₛₕ-plug (ceval etrap ∷ C) p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S = (canₛₕ-plug C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S)
canₛₕ-plug (csignl S ∷ C) p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ = canθₛₕ-plug 0 (sig ([S]-env S)) C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ
canₛₕ-plug (cpresent₁ S q ∷ C) p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ with Sig∈ S θ
... | no  S∉Domθ = ∪¹-respect-⊆¹-left (canₛₕ-plug C p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
... | yes S∈Domθ with (Signal.present ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = (canₛₕ-plug C p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
... | no  _ with (Signal.absent ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = λ k z → z
... | no  _ = ∪¹-respect-⊆¹-left (canₛₕ-plug C p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
canₛₕ-plug (cpresent₂ S p₁ ∷ C) p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ with Sig∈ S θ
... | no  S∉Domθ = ∪¹-respect-⊆¹-right (Canₛₕ p₁ θ) (canₛₕ-plug C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
... | yes S∈Domθ with (Signal.present ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = λ x y → y
... | no  _ with (Signal.absent ≟ₛₜ (sig-stats{S} θ S∈Domθ))
... | yes _ = (canₛₕ-plug C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
... | no  _ = ∪¹-respect-⊆¹-right (Canₛₕ p₁ θ) (canₛₕ-plug C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
canₛₕ-plug (cloop ∷ C) p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S = (canₛₕ-plug C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S)
canₛₕ-plug (cloopˢ₂ p ∷ C) p₁ q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ = λ x z → z
canₛₕ-plug (cseq₂ p ∷ C) p₁ q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ with any (Code.nothin Code.≟_) (Canₖ p θ)
... | yes 0∈Canp = ∪¹-respect-⊆¹-right (Canₛₕ p θ) (canₛₕ-plug C p₁ q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
... | no  0∉Canp = λ x y → y
canₛₕ-plug (cshared (s ₛₕ) e ∷ C) p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ s' s'∈CanC⟦q⟧
   = NSet.set-remove-not-removed ((¬ s ≡ s') ∋ NSet.set-remove-not-eq{s'}{s}{Canₛₕ (C ⟦ q ⟧c) θ} s'∈CanC⟦q⟧) (canₛₕ-plug C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ s' (NSet.set-remove-mono-∈ s s'∈CanC⟦q⟧))
canₛₕ-plug (cvar x e ∷ C) p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S = (canₛₕ-plug C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S)
canₛₕ-plug (cif₁ x q ∷ C) p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ = ∪¹-respect-⊆¹-left (canₛₕ-plug C p q₁ Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
canₛₕ-plug (cif₂ x p ∷ C) p₁ q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ = ∪¹-respect-⊆¹-right (Canₛₕ p θ) (canₛₕ-plug C p₁ q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)
canₛₕ-plug (cenv θ₁ A ∷ C) p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ =  ⊆¹-respect-|¹ (snd $ Dom θ₁) (canθₛₕ-plug 0 (sig θ₁) C p q Canₛₕq⊆Canₛₕp Canₖq⊆Canₖp ⊂S θ)

canθₖ-plugE : ∀ S' sigs → ∀ E p q
              → (Canₖq⊆Canₖp : ∀ θ k → k ∈ (Canₖ q θ) → k ∈ (Canₖ p θ))
              → (Canₛq⊆Canₛp : ∀ θ S → S ∈ (Canₛ q θ) → S ∈ (Canₛ p θ))
              → (∀ θ k → k ∈ (Canθₖ sigs S' (E ⟦ q ⟧e) θ) → k ∈ (Canθₖ sigs S' (E ⟦ p ⟧e) θ))
canθₖ-plugE S' sigs E p q
  with canθₖ-plug S' sigs (Data.List.map ceval E) p q
... | r rewrite unplugc (⟦⟧e-to-⟦⟧c (Erefl{E}{q}))
              | unplugc (⟦⟧e-to-⟦⟧c (Erefl{E}{p}))
  = r

canθₛ-plugE : ∀ S' sigs → ∀ E p q
              → (Canₛq⊆Canₛp : ∀ θ S → S ∈ (Canₛ q θ) → S ∈ (Canₛ p θ))
              → (Canₖq⊆Canₖp : ∀ θ k → k ∈ (Canₖ q θ) → k ∈ (Canₖ p θ))
              → (∀ θ k → k ∈ (Canθₛ sigs S' (E ⟦ q ⟧e) θ) → k ∈ (Canθₛ sigs S' (E ⟦ p ⟧e) θ))
canθₛ-plugE S' sigs E p q
  with canθₛ-plug S' sigs (Data.List.map ceval E) p q
... | r rewrite unplugc (⟦⟧e-to-⟦⟧c (Erefl{E}{q}))
              | unplugc (⟦⟧e-to-⟦⟧c (Erefl{E}{p}))
  = r


canθₛₕ-plugE : ∀ S' sigs → ∀ E p q
              → (Canₛₕq⊆Canₛₕp : ∀ θ → (Canₛₕ q θ) ⊆¹ (Canₛₕ p θ))
              → (Canₛq⊆Canₛp : ∀ θ k → k ∈ (Canₖ q θ) → k ∈ (Canₖ p θ))
              → (Canₖq⊆Canₖp : ∀ θ S → S ∈ (Canₛ q θ) → S ∈ (Canₛ p θ))
              → (∀ θ k → k ∈ (Canθₛₕ sigs S' (E ⟦ q ⟧e) θ) → k ∈ (Canθₛₕ sigs S' (E ⟦ p ⟧e) θ))
canθₛₕ-plugE S' sigs E p q
  with canθₛₕ-plug S' sigs (Data.List.map ceval E) p q
... | r rewrite unplugc (⟦⟧e-to-⟦⟧c (Erefl{E}{q}))
              | unplugc (⟦⟧e-to-⟦⟧c (Erefl{E}{p}))
  = r
