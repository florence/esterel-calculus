module _ where

open import utility
open import sn-calculus
  using (all-ready ; bound-ready)

open import Data.Product using (∃ ; Σ ; _,_ ; _×_ ; _,′_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (sym ; inspect ; Reveal_·_is_ ; trans)
open import Data.Empty
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Context
open import Esterel.Environment as Env
open import Esterel.Lang.CanFunction
  using (Canₖ ; module CodeSet ; Canₛ ; Canₛₕ ; Canθₛ ; Canθₛₕ)
open import Esterel.Lang.CanFunction.Base
  using (can-shr-var-irr)
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Signal as Signal
  using (Signal ; _ₛ) renaming (_≟ₛₜ_ to _≟ₛₜₛ_)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar ; _ₛₕ) renaming (_≟ₛₜ_ to _≟ₛₜₛₕ_)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar ; _ᵥ)

open import Esterel.Lang.CanFunction using (Canₖ)

open import Data.Product using (_,_)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; trans ; sym)
import Data.FiniteMap
open import Data.List
  using (List ; [] ; _∷_ ; [_] ; _++_ ; map ; concatMap ; filter)
open import Data.List.Any using (Any ; any ; here ; there)
open import Data.List.All using (All ; [] ; _∷_)
open import Data.OrderedListMap

open all-ready
open bound-ready


data blocked-s : Env → s/l → Set where
   bbshr-old : ∀{θ s} →
     (s∈ : Env.isShr∈ s θ) →
     Env.shr-stats{s} θ s∈ ≡ SharedVar.old →
     blocked-s θ (shr-ref s)
   bbshr-new : ∀{θ s} →
     (s∈ : Env.isShr∈ s θ) →
     Env.shr-stats{s} θ s∈ ≡ SharedVar.new →
     blocked-s θ (shr-ref s)

-- Note: θ and e are in the opposite order of all-ready definition.
-- We directly used Any here as a synonym. Should all-ready be the same?
blocked-e : Env → Expr → Set
blocked-e θ (plus operators) = Any (blocked-s θ) operators

data blocked : Env → Term → Set where
  bsig-exists : ∀{θ p q} S S∈ → (sig-stats{S} θ S∈ ≡ Signal.unknown) →
                ------------------------
                blocked θ (present S ∣⇒ p ∣⇒ q)
  bpar-both  : ∀{θ p q} → blocked θ p → blocked θ q → blocked θ (p ∥ q)
  bpar-left  : ∀{θ p q} → blocked θ p → done q → blocked θ (p ∥ q)
  bpar-right : ∀{θ p q} → done p → blocked θ q → blocked θ (p ∥ q)
  bseq       : ∀{θ p q} → blocked θ p → blocked θ (p >> q)
  bloopˢ     : ∀{θ p q} → blocked θ p → blocked θ (loopˢ p q)
  bsusp      : ∀{θ p S} → blocked θ p → blocked θ (suspend p S)
  btrap      : ∀{θ p}   → blocked θ p → blocked θ (trap p)
  bshared    : ∀{θ s e p} → blocked-e θ e → blocked θ (shared s ≔ e in: p)
  bsset      : ∀{θ s e} → blocked-e θ e → blocked θ (s ⇐ e)
  bvar       : ∀{θ x e p} → blocked-e θ e → blocked θ (var x ≔ e in: p)
  bxset      : ∀{θ x e} → blocked-e θ e → blocked θ (x ≔ e)


data manifests-as-non-constructive : Env → Term → Set where
  mnc : ∀{p θ} → (blocked-p : blocked θ p)
              -- absent rule cannot fire: unknown signals might be emitted at some point
              → (θS≡unknown→S∈can-p-θ :
                 ∀ S →
                  (S∈Domθ        : Signal.unwrap S ∈ fst (Dom θ)) →
                  (θS≡unknown    : sig-stats {S} θ S∈Domθ ≡ Signal.unknown) →
                  Signal.unwrap S ∈ Canθₛ (sig θ) 0 p []env)
              -- readyness rule cannot fire: unready variables might become ready
              → (θs≡old⊎θs≡new→s∈can-p-θ :
                 ∀ s →
                  (s∈Domθ        : SharedVar.unwrap s ∈ snd (Dom θ)) →
                  (θs≡old⊎θs≡new : shr-stats {s} θ s∈Domθ ≡ SharedVar.old ⊎
                                   shr-stats {s} θ s∈Domθ ≡ SharedVar.new) →
                  SharedVar.unwrap s ∈ Canθₛₕ (sig θ) 0 p []env)
              → manifests-as-non-constructive θ p


halted-blocked-disjoint : ∀ {θ p} → halted p → blocked θ p → ⊥
halted-blocked-disjoint hnothin   ()
halted-blocked-disjoint (hexit n) ()

paused-blocked-disjoint : ∀ {θ p} → paused p → blocked θ p → ⊥
paused-blocked-disjoint ppause ()
paused-blocked-disjoint (pseq p/paused) (bseq p/blocked) =
  paused-blocked-disjoint p/paused p/blocked
paused-blocked-disjoint (ploopˢ p/paused) (bloopˢ p/blocked) =
  paused-blocked-disjoint p/paused p/blocked
paused-blocked-disjoint (ppar p/paused q/paused) (bpar-both  p/blocked q/blocked) =
  paused-blocked-disjoint q/paused q/blocked
paused-blocked-disjoint (ppar p/paused q/paused) (bpar-left  p/blocked q/done) =
  paused-blocked-disjoint p/paused p/blocked
paused-blocked-disjoint (ppar p/paused q/paused) (bpar-right p/done q/blocked) =
  paused-blocked-disjoint q/paused q/blocked
paused-blocked-disjoint (psuspend p/paused) (bsusp p/blocked) =
  paused-blocked-disjoint p/paused p/blocked
paused-blocked-disjoint (ptrap p/paused) (btrap p/blocked) =
  paused-blocked-disjoint p/paused p/blocked

done-blocked-disjoint : ∀ {θ p} → done p → blocked θ p → ⊥
done-blocked-disjoint (dhalted p/halted) p/blocked = halted-blocked-disjoint p/halted p/blocked
done-blocked-disjoint (dpaused p/paused) p/blocked = paused-blocked-disjoint p/paused p/blocked


-- An expression cannot be both all-ready and blocked-e, i.e.
-- all-ready and blocked-e characterize disjoint subsets of e.
all-ready-blocked-disjoint : ∀ {e θ} → ¬ (all-ready e θ × blocked-e θ e)
all-ready-blocked-disjoint {θ = θ}
  (aplus (brshr {s = s} s∈ θs≡ready ∷ e/all-ready) ,
   here (bbshr-old {s = .s} s∈' θs≡old))
  with trans (sym θs≡ready) (trans (Env.shr-stats-∈-irr {s} {θ} s∈ s∈') θs≡old)
... | ()
all-ready-blocked-disjoint {θ = θ}
  (aplus (brshr {s = s} s∈ θs≡ready ∷ e/all-ready) ,
   here (bbshr-new {s = .s} s∈' θs≡new))
  with trans (sym θs≡ready) (trans (Env.shr-stats-∈-irr {s} {θ} s∈ s∈') θs≡new)
... | ()
all-ready-blocked-disjoint {θ = θ}
  (aplus (px ∷ e/all-ready) ,
   there e/blocked) =
  all-ready-blocked-disjoint (aplus e/all-ready ,′ e/blocked)


-- A subexpression in the hole in a blocked program must be either blocked or done.
blocked-⟦⟧e : ∀ {θ p p' E} → blocked θ p → p ≐ E ⟦ p' ⟧e → blocked θ p' ⊎ done p'
blocked-⟦⟧e p/blocked dehole = inj₁ p/blocked
blocked-⟦⟧e (bseq p/blocked)  (deseq p≐E⟦p'⟧)     = blocked-⟦⟧e p/blocked p≐E⟦p'⟧
blocked-⟦⟧e (bloopˢ p/blocked) (deloopˢ p≐E⟦p'⟧)    = blocked-⟦⟧e p/blocked p≐E⟦p'⟧
blocked-⟦⟧e (bsusp p/blocked) (desuspend p≐E⟦p'⟧) = blocked-⟦⟧e p/blocked p≐E⟦p'⟧
blocked-⟦⟧e (btrap p/blocked) (detrap p≐E⟦p'⟧)    = blocked-⟦⟧e p/blocked p≐E⟦p'⟧
blocked-⟦⟧e (bpar-both  p/blocked q/blocked) (depar₁ p≐E⟦p'⟧) =
  blocked-⟦⟧e p/blocked p≐E⟦p'⟧
blocked-⟦⟧e (bpar-left  p/blocked q/done)    (depar₁ p≐E⟦p'⟧) =
  blocked-⟦⟧e p/blocked p≐E⟦p'⟧
blocked-⟦⟧e (bpar-right p/done    q/blocked) (depar₁ p≐E⟦p'⟧) =
  inj₂ (done-⟦⟧e p/done p≐E⟦p'⟧)
blocked-⟦⟧e (bpar-both  p/blocked q/blocked) (depar₂ q≐E⟦p'⟧) =
  blocked-⟦⟧e q/blocked q≐E⟦p'⟧
blocked-⟦⟧e (bpar-left  p/blocked q/done)    (depar₂ q≐E⟦p'⟧) =
  inj₂ (done-⟦⟧e q/done q≐E⟦p'⟧)
blocked-⟦⟧e (bpar-right p/done    q/blocked) (depar₂ q≐E⟦p'⟧) =
  blocked-⟦⟧e q/blocked q≐E⟦p'⟧

blocked-el-dec : ∀ θ l -> Dec (Any (blocked-s θ) l)
blocked-el-dec θ [] = no (λ ())
blocked-el-dec θ (num n ∷ l) with blocked-el-dec θ l
blocked-el-dec θ (num n ∷ l) | yes p = yes (there p)
blocked-el-dec θ (num n ∷ l) | no ¬p = no (λ { (here ()) ; (there x) → ¬p x } )
blocked-el-dec θ (seq-ref x ∷ l) with blocked-el-dec θ l
blocked-el-dec θ (seq-ref x ∷ l) | yes p = yes (there p)
blocked-el-dec θ (seq-ref x ∷ l) | no ¬p = no (λ { (here ()) ; (there x) → ¬p x })
blocked-el-dec θ (shr-ref s ∷ l) with blocked-el-dec θ l
blocked-el-dec θ (shr-ref s ∷ l) | yes p = yes (there p)
blocked-el-dec θ (shr-ref s ∷ l) | no ¬p with Env.Shr∈ s θ
blocked-el-dec θ (shr-ref s ∷ l) | no ¬p | yes s∈θ with Env.shr-stats{s} θ s∈θ | inspect (Env.shr-stats {s} θ) s∈θ
blocked-el-dec θ (shr-ref s ∷ l) | no ¬p | yes s∈θ | SharedVar.ready | Reveal_·_is_.[ eq ] =
  no (λ { (here (bbshr-old s∈θ₂ eq₂)) → lookup-s-eq θ s s∈θ s∈θ₂ eq eq₂ (λ ()) ;
          (here (bbshr-new s∈θ₂ eq₂)) → lookup-s-eq θ s s∈θ s∈θ₂ eq eq₂ (λ ()) ;
          (there x) → ¬p x })
blocked-el-dec θ (shr-ref s ∷ l) | no ¬p | yes s∈θ | SharedVar.new   | Reveal_·_is_.[ eq ] = yes (here (bbshr-new s∈θ eq))
blocked-el-dec θ (shr-ref s ∷ l) | no ¬p | yes s∈θ | SharedVar.old   | Reveal_·_is_.[ eq ] = yes (here (bbshr-old s∈θ eq))
blocked-el-dec θ (shr-ref s ∷ l) | no ¬p | no ¬s∈θ =
  no (λ { (here (bbshr-old s∈ x)) → ¬s∈θ s∈ ;
          (here (bbshr-new s∈ x)) → ¬s∈θ s∈ ;
          (there x) → ¬p x })

blocked-e-dec : ∀ θ e -> Dec (blocked-e θ e)
blocked-e-dec θ (plus l) = blocked-el-dec θ l


blocked-dec : ∀ θ p -> Dec (blocked θ p)
blocked-dec θ nothin = no (λ ())
blocked-dec θ pause = no (λ ())
blocked-dec θ (signl S p) = no (λ ())
blocked-dec θ (present S ∣⇒ p ∣⇒ q) with Sig∈ S θ
blocked-dec θ (present S ∣⇒ p ∣⇒ q) | yes SigS∈θ
   with Env.sig-stats{S} θ SigS∈θ | inspect (Env.sig-stats{S} θ) SigS∈θ 
blocked-dec θ (present S ∣⇒ p ∣⇒ q) | yes SigS∈θ₁ | Signal.present | Reveal_·_is_.[ eq₁ ] =
  no (λ { (bsig-exists .S SigS∈θ₂ eq₂) → lookup-S-eq θ S SigS∈θ₁ SigS∈θ₂ eq₁ eq₂ (λ ()) })
blocked-dec θ (present S ∣⇒ p ∣⇒ q) | yes SigS∈θ₁ | Signal.absent | Reveal_·_is_.[ eq₁ ] =
  no (λ { (bsig-exists .S SigS∈θ₂ eq₂) → lookup-S-eq θ S SigS∈θ₁ SigS∈θ₂ eq₁ eq₂ (λ ()) } )
blocked-dec θ (present S ∣⇒ p ∣⇒ q) | yes SigS∈θ | Signal.unknown | Reveal_·_is_.[ eq ] =
  yes (bsig-exists S SigS∈θ eq)
blocked-dec θ (present S ∣⇒ p ∣⇒ q) | no ¬SigS∈θ =
  no (λ { (bsig-exists .S S∈ _) → ¬SigS∈θ S∈ })
blocked-dec θ (emit S) = no (λ ())
blocked-dec θ (p ∥ q) with blocked-dec θ p | blocked-dec θ q
blocked-dec θ (p ∥ q) | yes blockedp | yes blockedq =
  yes (bpar-both blockedp blockedq)
blocked-dec θ (p ∥ q) | yes blockedp | no ¬blockedq with done-dec q
blocked-dec θ (p ∥ q) | yes blockedp | no ¬blockedq | yes donep =
  yes (bpar-left blockedp donep)
blocked-dec θ (p ∥ q) | yes blockedp | no ¬blockedq | no ¬donep =
  no (λ { (bpar-both  _ x) → ¬blockedq x ;
          (bpar-left  _ x) → ¬donep x ;
          (bpar-right _ x) → ¬blockedq x })
blocked-dec θ (p ∥ q) | no ¬blockedp | yes blockedq with done-dec p
blocked-dec θ (p ∥ q) | no ¬blockedp | yes blockedq | yes donep =
  yes (bpar-right donep blockedq)
blocked-dec θ (p ∥ q) | no ¬blockedp | yes blockedq | no ¬donep =
  no (λ { (bpar-both  x _) → ¬blockedp x ;
          (bpar-left  x _) → ¬blockedp x ;
          (bpar-right x _) → ¬donep x })
blocked-dec θ (p ∥ q) | no ¬blockedp | no ¬blockedq =
  no (λ { (bpar-both  _ x) → ¬blockedq x ;
          (bpar-left  x _) → ¬blockedp x ;
          (bpar-right _ x) → ¬blockedq x })
blocked-dec θ (loop p) = no (λ ())
blocked-dec θ (p >> q) with blocked-dec θ p
blocked-dec θ (p >> q) | yes blockedp = yes (bseq blockedp)
blocked-dec θ (p >> q) | no ¬blockedp = no (λ { (bseq x) → ¬blockedp x })
blocked-dec θ (loopˢ p q) with blocked-dec θ p
blocked-dec θ (loopˢ p q) | yes blockedp = yes (bloopˢ blockedp)
blocked-dec θ (loopˢ p q) | no ¬blockedp = no (λ { (bloopˢ x) → ¬blockedp x })
blocked-dec θ (suspend p S) with blocked-dec θ p
blocked-dec θ (suspend p S) | yes blockedp = yes (bsusp blockedp)
blocked-dec θ (suspend p S) | no ¬blockedp = no (λ { (bsusp x) → ¬blockedp x })
blocked-dec θ (trap p) with blocked-dec θ p
blocked-dec θ (trap p) | yes blockedp = yes (btrap blockedp)
blocked-dec θ (trap p) | no ¬blockedp = no (λ { (btrap x) → ¬blockedp x })
blocked-dec θ (exit x) = no (λ ())
blocked-dec θ (shared s ≔ e in: p) with blocked-e-dec θ e
blocked-dec θ (shared s ≔ e in: p) | yes blockede = yes (bshared blockede)
blocked-dec θ (shared s ≔ e in: p) | no ¬blockede = no (λ { (bshared x) → ¬blockede x })
blocked-dec θ (s ⇐ e) with blocked-e-dec θ e
blocked-dec θ (s ⇐ e) | yes p = yes (bsset p)
blocked-dec θ (s ⇐ e) | no ¬p = no (λ { (bsset x) → ¬p x })
blocked-dec θ (var x ≔ e in: p) with blocked-e-dec θ e
blocked-dec θ (var x ≔ e in: p₁) | yes p = yes (bvar p)
blocked-dec θ (var x ≔ e in: p) | no ¬p = no (λ { (bvar x₁) → ¬p x₁ })
blocked-dec θ (x ≔ e) with blocked-e-dec θ e
blocked-dec θ (x ≔ e) | yes p = yes (bxset p)
blocked-dec θ (x ≔ e) | no ¬p = no (λ { (bxset x₁) → ¬p x₁ })
blocked-dec θ (if x ∣⇒ p ∣⇒ p₁) = no (λ ())
blocked-dec θ (ρ θ₁ · p) = no (λ ()) 
