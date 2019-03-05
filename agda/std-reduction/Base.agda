module std-reduction.Base where

open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open EvaluationContext1
open import Esterel.Lang
open import Esterel.Environment as Env
  using (Env)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)
open import Esterel.Lang.CanFunction
  using (Canₛ ; Canₛₕ)

open import Data.List
  using (List; _∷_ ; [] ; mapMaybe)
open import Data.List.Any
  using (any)
open import blocked
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_ ; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; sym)
open _≡_
import Data.Nat as Nat
open import Relation.Nullary using (yes ; no ; ¬_)
open import Function using (_∘_ ; id ; _$_)
open import Data.Maybe
  using (Maybe)
open Maybe
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Data.Bool
  using (if_then_else_)


blocked-or-done : Env → Term → Set
blocked-or-done θ p = (done p) ⊎ (blocked θ p)

mutual
  set-all-absent : (θ : Env) → (List (∃[ S ] Env.isSig∈ S θ)) → Env
  set-all-absent θ [] = θ
  set-all-absent θ ((S , S∈) ∷ Ss)
    = Env.set-sig{S} (set-all-absent θ Ss) (set-all-absent∈ θ S Ss S∈) Signal.absent

  set-all-absent∈ : ∀ θ S Ss → Env.isSig∈ S θ → Env.isSig∈ S (set-all-absent θ Ss)
  set-all-absent∈ θ S [] S∈ = S∈
  set-all-absent∈ θ S (x ∷ Ss) S∈
    = Env.sig-set-mono'{S = S}{S' = (proj₁ x)}{θ = set-all-absent θ Ss}{S'∈ = S'∈2} S∈2
   where
     S∈2 = (set-all-absent∈ θ S Ss S∈)
     S'∈2 = (set-all-absent∈ θ (proj₁ x) Ss (proj₂ x))
  

mutual
  set-all-ready : (θ : Env) → (List (∃[ s ] Env.isShr∈ s θ)) → Env
  set-all-ready θ [] = θ
  set-all-ready θ ((s , s∈) ∷ ss)
    = Env.set-shr {s} θ2 s∈2 SharedVar.ready (Env.shr-vals{s} θ s∈)
      where
        s∈2 = (set-all-ready∈ θ s ss s∈)
        θ2 = (set-all-ready θ ss)

  set-all-ready∈ : ∀ θ s ss → Env.isShr∈ s θ → Env.isShr∈ s (set-all-ready θ ss)
  set-all-ready∈ θ s [] s∈ = s∈
  set-all-ready∈ θ s (x ∷ ss) s∈
    = Env.shr-set-mono' {s = s} {s' = proj₁ x} {θ = set-all-ready θ ss}
        {s'∈ = set-all-ready∈ θ (proj₁ x) ss (proj₂ x)} (set-all-ready∈ θ s ss s∈)

shr-val-same-after-all-ready : ∀ s θ ss →
                               (s∈  : Env.isShr∈ s θ) →
                               (s∈2  : Env.isShr∈ s (set-all-ready θ ss)) →
                               (Env.shr-vals {s} θ s∈) ≡ (Env.shr-vals {s} (set-all-ready θ ss) s∈2)
shr-val-same-after-all-ready s θ [] s∈ s∈2 =  Env.shr-vals-∈-irr{s}{θ} s∈ s∈2
shr-val-same-after-all-ready s θ ((s' , s'∈) ∷ ss) s∈ s∈2 with (SharedVar._≟_ s' s)
... | yes p rewrite p | Env.shr∈-eq{s}{θ} s∈ s'∈
   = sym (proj₂ (Env.shr-putget{s}{(set-all-ready θ ss)}{SharedVar.ready}{(Env.shr-vals {s} θ s'∈)} (set-all-ready∈ θ s ss s∈) s∈2))
... | no ¬s'≡s
  = sym
     (proj₂
       (Env.shr-putputget{θ = (set-all-ready θ ss)}{v1l = Env.shr-stats{s} (set-all-ready θ ss) ((set-all-ready∈ θ s ss s∈))}
                         (¬s'≡s ∘ sym)
                         (set-all-ready∈ θ s ss s∈)
                         (set-all-ready∈ θ s' ss s'∈)
                         s∈2
                         refl
                         (sym (shr-val-same-after-all-ready s θ ss s∈ (set-all-ready∈ θ s ss s∈))) ))
-- 


can-set-absent' : (θ : Env) → Term →
                  List (∃[ S ] (Σ[ S∈ ∈ (Env.isSig∈ S θ) ] (Env.sig-stats{S} θ S∈ ≡ Signal.unknown)))
can-set-absent' θ p = mapMaybe id $ Env.SigDomMap θ get-res
  where
    get-res : (S : Signal) → Env.isSig∈ S θ → Maybe (∃[ S ] (Σ[ S∈ ∈ (Env.isSig∈ S θ) ] (Env.sig-stats{S} θ S∈ ≡ Signal.unknown)))
    get-res S S∈ with any (Nat._≟_ (Signal.unwrap S)) (Canₛ p θ) | Signal._≟ₛₜ_ (Env.sig-stats{S} θ S∈) Signal.unknown
    ... | no _ | yes eq = just $ S , (S∈ , eq) 
    ... | _ | _ = nothing

can-set-absent : (θ : Env) → Term → List (∃[ S ] Env.isSig∈ S θ)
can-set-absent θ p
   = Data.List.map (λ x → proj₁ x , proj₁ (proj₂ x)) 
                   (can-set-absent' θ p)


CanSetToReady : Env → Set
CanSetToReady θ = (∃[ s ] (Σ[ S∈ ∈ (Env.isShr∈ s θ) ] (Env.shr-stats{s} θ S∈ ≡ SharedVar.old ⊎ Env.shr-stats{s} θ S∈ ≡ SharedVar.new)))

can-set-ready' : (θ : Env) → Term → List (CanSetToReady θ)
can-set-ready' θ p = mapMaybe id $ Env.ShrDomMap θ get-res
  where
    get-res : (s : SharedVar) → Env.isShr∈ s θ → Maybe (CanSetToReady θ) 
    get-res s s∈ with any (Nat._≟_ (SharedVar.unwrap s)) (Canₛₕ p θ)
                    | SharedVar._≟ₛₜ_ (Env.shr-stats{s} θ s∈) SharedVar.old
                    | SharedVar._≟ₛₜ_ (Env.shr-stats{s} θ s∈) SharedVar.new
    ... | no _ | yes eq |  _   = just $ s , (s∈ , inj₁ eq)
    ... | no _ | no _ | yes eq = just $ s , (s∈ , inj₂ eq)
    ... | _ | yes _ | yes _ = nothing
    ... | _ | yes _ | no _ = nothing
    ... | _ | no _ | yes _ = nothing
    ... | _ | no _ | no _ = nothing


can-set-ready :  (θ : Env) → Term → List (∃[ s ] Env.isShr∈ s θ)
can-set-ready θ p = Data.List.map (λ x → proj₁ x , proj₁ (proj₂ x)) (can-set-ready' θ p)


data left-most : Env → EvaluationContext → Set where
  lhole : ∀{θ} → left-most θ []
  lseq : ∀{θ E q} → left-most θ E → left-most θ ((eseq q) ∷ E)
  lloopˢ : ∀{θ E q} → left-most θ E → left-most θ ((eloopˢ q) ∷ E) 
  lparl : ∀{θ E q} → left-most θ E → left-most θ ((epar₁ q) ∷ E)
  lparrdone : ∀{θ E p} → done p → left-most θ E → left-most θ ((epar₂ p) ∷ E)
  lparrblocked : ∀{θ E p} → blocked θ p → left-most θ E → left-most θ ((epar₂ p) ∷ E)
  lsuspend : ∀{θ E S} → left-most θ E → left-most θ ((esuspend S) ∷ E)
  ltrap : ∀{θ E} → left-most θ E → left-most θ (etrap ∷ E)
