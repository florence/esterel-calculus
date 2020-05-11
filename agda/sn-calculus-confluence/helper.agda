module sn-calculus-confluence.helper where

open import Data.List.All
open import Function
  using (_∘_)
open import Data.List.Any using (Any ; here ; there)
open import Data.Nat using (_+_)
open import utility
open import Esterel.Lang
open import Esterel.Lang.Properties
open import Esterel.Environment as Env
open import Esterel.Context
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import sn-calculus
open import context-properties
open import Esterel.Lang.Binding
open import Data.List.Any.Properties
  renaming ( ++⁺ˡ to ++ˡ ; ++⁺ʳ to ++ʳ )

open import Data.FiniteMap
import Data.OrderedListMap as OMap
open import Data.Nat as Nat using (ℕ)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar

set-dist' : ∀{key value inject} → ∀{inject-injective : ∀{k1 : key} → ∀{k2 : key} → (inject k1) ≡ (inject k2) → k1 ≡ k2}
            → ∀{A : Map {key} inject inject-injective value} → ∀{B : Map {key} inject inject-injective value}
            → distinct' (keys {key} inject inject-injective {value} A) (keys {key} inject inject-injective {value}  B)
            → (union {key} inject inject-injective {value} A B) ≡ (union  {key} inject inject-injective {value} B A)
set-dist'{key}{value}{inject}{inject-injective}{A}{B} d = OMap.U-comm key inject value {A} {B} d


set-dist : ∀{θ θ'} → distinct (Dom θ) (Dom θ') → (θ ← θ') ≡ (θ' ← θ)
set-dist {Θ sig₁ shr₁ var₁} {Θ sig₂ shr₂ var₂} (a , b , c)
    rewrite  set-dist'{inject-injective = Signal.unwrap-injective}{sig₁}{sig₂} a
           | set-dist'{inject-injective = SharedVar.unwrap-injective}{shr₁}{shr₂} b
           | set-dist'{inject-injective = SeqVar.unwrap-injective}{var₁}{var₂} c = refl


done≠rho : ∀{p E θ q} → done p → (p ≐ E ⟦ (ρ θ · q) ⟧e) → ⊥
done≠rho (dhalted hnothin) ()
done≠rho (dhalted (hexit n)) ()
done≠rho (dpaused p/paused) p≐E⟦ρθq⟧ with paused-⟦⟧e p/paused p≐E⟦ρθq⟧
... | ()

plug≡ : ∀{r q E w} → r ≐ E ⟦ w ⟧e → q ≐ E ⟦ w ⟧e  → r ≡ q
plug≡ r≐E⟦w⟧ q≐E⟦w⟧ = trans (sym (unplug r≐E⟦w⟧)) (unplug q≐E⟦w⟧)

RE-split : ∀{p θ p' E E' q}
           → p ≐ E ⟦ ρ θ · p' ⟧e
           → p ≐ E' ⟦ q ⟧e
           → E a~ E'
           → ∃ (λ d → ∃ (λ Eout → d ≐ E ⟦ p' ⟧e × d ≐ Eout ⟦ q ⟧e × E' ~ Eout × Eout a~ E ))
RE-split {.(ρ _ · _)} dehole dehole ()
RE-split {.(_ ∥ _)} (depar₁ eq1) dehole ()
RE-split {.(_ >> _)} (deseq eq1) dehole ()
RE-split {.(trap _)} (detrap eq1) dehole ()
RE-split {.(_ ∥ _)} (depar₂ eq1) dehole ()
RE-split {.(suspend _ _)} (desuspend eq1) dehole ()
RE-split {(pin ∥ qin)}{θ}{p'}{((epar₁ _) ∷ E)}{(epar₂ _) ∷ E'} (depar₁ eq1) (depar₂ eq2) par2
   = (t ∥ qin) , (epar₂ t) ∷ E' , (depar₁ (plug refl) , depar₂ eq2 , parl (~ref E') , par) where t = (E ⟦ p' ⟧e)
RE-split {(pin ∥ qin)}{θ}{p'}{((epar₂ _) ∷ E)}{(epar₁ _) ∷ E'} (depar₂ eq1) (depar₁ eq2) par
   = (pin ∥ t) , ((epar₁ t) ∷ E' , (depar₂ (plug refl) , depar₁ eq2 , parr (~ref E') , par2)) where t = (E ⟦ p' ⟧e)
RE-split {(pin ∥ qin)} (depar₁ eq1) (depar₁ eq2) (parr neg) with RE-split eq1 eq2 neg
... | (d , Eout , (eqd , eqo , ~ , a~)) = d ∥ qin , (epar₁ qin) ∷ Eout , (depar₁ eqd , depar₁ eqo , parr ~ , parr a~)
RE-split {(pin ∥ qin)} (depar₂ eq1) (depar₂ eq2) (parl neg) with RE-split eq1 eq2 neg
... | (d , Eout , (eqd , eqo , ~ , a~)) = pin ∥ d , (epar₂ pin) ∷ Eout , (depar₂ eqd , depar₂ eqo , parl ~ , parl a~)
RE-split {(loopˢ _ q)} (deloopˢ eq1) (deloopˢ eq2) (loopˢ neg) with RE-split eq1 eq2 neg
... | (d , Eout , (eqd , eqo , ~ , a~)) = (loopˢ d q) , (eloopˢ q) ∷ Eout , (deloopˢ eqd , deloopˢ eqo , loopˢ ~ , loopˢ a~)
RE-split {(._ >> q)} (deseq eq1) (deseq eq2) (seq neg) with RE-split eq1 eq2 neg
... | (d , Eout , (eqd , eqo , ~ , a~)) = (d >> q) , (eseq q) ∷ Eout , (deseq eqd , deseq eqo , seq ~ , seq a~)
RE-split {(suspend ._ S)} (desuspend eq1) (desuspend eq2) (susp neg) with RE-split eq1 eq2 neg
... | (d , Eout , (eqd , eqo , ~ , a~)) = (suspend d S) , ((esuspend S) ∷ Eout) , (desuspend eqd , desuspend eqo , susp ~ , susp a~)
RE-split {.(trap _)} (detrap eq1) (detrap eq2) (trp neg) with RE-split eq1 eq2 neg
... | (d , Eout , (eqd , eqo , ~ , a~)) = (trap d) , (etrap ∷ Eout) , (detrap eqd , detrap eqo , trp ~ , trp a~)


ready-maint : ∀{θ e} → (S : Signal) → (S∈ : (Env.isSig∈ S θ)) → (stat : Signal.Status) → all-ready e θ
                     → all-ready e (Env.set-sig{S} θ S∈ stat)
ready-maint {θ} {.(plus [])} S S∈ stat (aplus []) = aplus []
ready-maint {θ} {.(plus (num _ ∷ _))} S S∈ stat (aplus (brnum ∷ x₁)) with ready-maint S S∈ stat (aplus x₁)
... | (aplus r) = aplus (brnum ∷ r)
ready-maint {θ} {.(plus (seq-ref _ ∷ _))} S S∈ stat (aplus (brseq x₁ ∷ x₂)) with ready-maint S S∈ stat (aplus x₂)
... | (aplus r) = aplus (brseq x₁ ∷ r)
ready-maint {θ} {.(plus (shr-ref _ ∷ _))} S S∈ stat (aplus (brshr s∈ x ∷ x₁)) with ready-maint S S∈ stat (aplus x₁)
... | (aplus r) = aplus (brshr s∈ x ∷ r)

ready-irr : ∀{θ e} → (S : Signal) → (S∈ : (Env.isSig∈ S θ)) → (stat : Signal.Status)
                   → (e' : all-ready e θ)
                   → (e'' : all-ready e (Env.set-sig{S} θ S∈ stat))
                   → δ e' ≡ δ e''

ready-irr {θ} {.(plus [])} S S∈ stat (aplus []) (aplus []) = refl
ready-irr {θ} {.(plus (num _ ∷ _))} S S∈ stat (aplus (brnum ∷ x₁)) (aplus (brnum ∷ x₂))
 rewrite ready-irr S S∈ stat (aplus x₁) (aplus x₂) = refl
ready-irr {θ@(Θ Ss ss xs)} {.(plus (seq-ref _ ∷ _))} S S∈ stat (aplus (brseq{_}{x} x₁ ∷ x₂)) (aplus (brseq x₃ ∷ x₄))
 rewrite ready-irr S S∈ stat (aplus x₂) (aplus x₄) | seq∈-eq'{x}{xs} x₁ x₃ = refl
ready-irr {θ@(Θ Ss ss xs)} {.(plus (shr-ref _ ∷ _))} S S∈ stat (aplus (brshr{_}{s} s∈ x ∷ x₁)) (aplus (brshr s∈₁ x₂ ∷ x₃))
 rewrite ready-irr S S∈ stat (aplus x₁) (aplus x₃) | shr∈-eq'{s}{ss} s∈ s∈₁ = refl

ready-maint/irr : ∀{θ e} → (S : Signal) → (S∈ : (Env.isSig∈ S θ)) → (stat : Signal.Status)
                         → (e' : all-ready e θ)
                         → Σ[ e'' ∈ all-ready e (Env.set-sig{S} θ S∈ stat) ] δ e' ≡ δ e''
ready-maint/irr {θ}{e} S S∈ stat e' with ready-maint{θ}{e} S S∈ stat e'
... | e'' = e'' , (ready-irr{θ}{e} S S∈ stat e' e'')

ready-maint/x : ∀{θ e} → (x : SeqVar) → (x∈ : (Env.isVar∈ x θ)) → (n : ℕ) → all-ready e θ
                       → all-ready e (Env.set-var{x} θ x∈ n)
ready-maint/x {θ} {.(plus [])} x x∈ n (aplus []) = aplus []
ready-maint/x {θ} {.(plus (num _ ∷ _))} x₁ x∈ n (aplus (brnum ∷ x₂)) with ready-maint/x x₁ x∈ n (aplus x₂)
... | (aplus r) = aplus (brnum ∷ r)
ready-maint/x {θ} {.(plus (seq-ref _ ∷ _))} x₁ x∈ n (aplus (brseq{x = x2} x₂ ∷ x₃)) with ready-maint/x x₁ x∈ n (aplus x₃)
... | (aplus r) = aplus ((brseq (seq-set-mono'{x2}{x₁}{θ}{n}{x∈} x₂)) ∷ r)
ready-maint/x {θ} {.(plus (shr-ref _ ∷ _))} x₁ x∈ n (aplus (brshr s∈ x ∷ x₂))  with ready-maint/x x₁ x∈ n (aplus x₂)
... | (aplus r) = aplus (brshr s∈ x ∷ r)

ready-maint-s : ∀{θ e} → (s : SharedVar) → (n : ℕ) → (s∈ : Env.isShr∈ s θ) → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready) → (e' : all-ready e θ)
                       → all-ready e (Env.set-shr{s = s} θ s∈ SharedVar.new n)
ready-maint-s {e = .(plus [])} s n s∈ ¬≡ (aplus []) = aplus []
ready-maint-s {e = .(plus (num _ ∷ _))} s n₁ s∈ ¬≡ (aplus (brnum ∷ x₁)) with ready-maint-s s n₁ s∈ ¬≡ (aplus x₁)
... | aplus rec  = aplus (brnum ∷ rec)
ready-maint-s {e = .(plus (seq-ref _ ∷ _))} s n s∈ ¬≡ (aplus (brseq x₁ ∷ x₂)) with ready-maint-s s n s∈ ¬≡ (aplus x₂)
... | aplus rec = aplus (brseq x₁ ∷ rec)
ready-maint-s{θ} {e = (plus (shr-ref s ∷ ._))} s₁ n s∈ ¬≡ (aplus (brshr s∈₁ x ∷ x₁)) with ready-maint-s s₁ n s∈ ¬≡ (aplus x₁) | s SharedVar.≟ s₁
... | aplus rec | yes refl with shr-stats-∈-irr{s}{θ} s∈ s∈₁
... | eq rewrite eq = ⊥-elim (¬≡ x)
ready-maint-s{θ = θ} {e = (plus (shr-ref s ∷ ._))} s₁ n s∈ ¬≡ (aplus (brshr s∈₁ x ∷ x₁)) | aplus rec | no ¬s≡s₁
 with shr-putputget{θ = θ}{v2l = SharedVar.new}{n} ¬s≡s₁ s∈₁ s∈ (shr-set-mono'{s}{s₁}{θ}{n = n}{s∈} s∈₁) x refl
... | (eq1 , eq2) = aplus (brshr ((shr-set-mono'{s}{s₁}{θ}{n = n}{s∈} s∈₁)) eq1 ∷ rec)

ready-irr-on-irr-s-helper : ∀{θ e} → (s : SharedVar) → (n : ℕ) → (s∈ : Env.isShr∈ s θ) → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready) → (e' : all-ready e θ)
                            → (e'' : all-ready e (Env.set-shr{s = s} θ s∈ SharedVar.new n)) →  δ e' ≡ δ e''
ready-irr-on-irr-s-helper {θ} {.(plus [])} s n s∈ ¬≡ (aplus []) (aplus []) = refl
ready-irr-on-irr-s-helper {θ} {.(plus (num _ ∷ _))} s n s∈ ¬≡ (aplus (brnum ∷ x₁)) (aplus (brnum ∷ x'))
  rewrite ready-irr-on-irr-s-helper s n s∈ ¬≡ (aplus x₁) (aplus x') = refl
ready-irr-on-irr-s-helper {θ@(Θ Ss ss xs)} {(plus (seq-ref x ∷ _))} s n s∈ ¬≡ (aplus (brseq x₁ ∷ x₂)) (aplus (brseq x₃ ∷ x'))
  rewrite ready-irr-on-irr-s-helper s n s∈ ¬≡ (aplus x₂) (aplus x') | seq∈-eq'{x}{xs} x₁ x₃ = refl
ready-irr-on-irr-s-helper {θ@(Θ Ss ss xs)} {(plus (shr-ref sₑ ∷ _))} s n s∈ ¬≡ (aplus (brshr s∈₁ x ∷ x₁)) (aplus (brshr s∈₂ x₂ ∷ x'))
  with sₑ SharedVar.≟ s
... | yes sₑ≡s rewrite sₑ≡s | shr∈-eq'{s}{ss} s∈ s∈₁ = ⊥-elim (¬≡ x)
... | no ¬sₑ≡s with shr-putputget{θ = θ}{v2l = SharedVar.new}{n} ¬sₑ≡s s∈₁ s∈ s∈₂ x refl
... | (eq1 , eq2) rewrite ready-irr-on-irr-s-helper s n s∈ ¬≡ (aplus x₁) (aplus x') | eq2 = refl

ready-irr-on-irr-s : ∀{θ e} → (s : SharedVar) → (n : ℕ) → (s∈ : Env.isShr∈ s θ) → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready) → (e' : all-ready e θ)
                     → Σ[ e'' ∈ all-ready e (Env.set-shr{s = s} θ s∈ SharedVar.new n) ] δ e' ≡ δ e''
ready-irr-on-irr-s s n s∈ ¬≡ e' = e'' , (ready-irr-on-irr-s-helper s n s∈ ¬≡ e' e'')
  where e'' = ready-maint-s s n s∈ ¬≡ e'

-- copied and pasted form above
-- TODO: maybe someday abstract over SharedVar.new/SharedVar.ready to sharedvar-status
ready-maint-s/ready : ∀{θ e} → (s : SharedVar) → (n : ℕ) → (s∈ : Env.isShr∈ s θ) → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready) → (e' : all-ready e θ)
                       → all-ready e (Env.set-shr{s = s} θ s∈ SharedVar.ready n)
ready-maint-s/ready {e = .(plus [])} s n s∈ ¬≡ (aplus []) = aplus []
ready-maint-s/ready {e = .(plus (num _ ∷ _))} s n₁ s∈ ¬≡ (aplus (brnum ∷ x₁)) with ready-maint-s/ready s n₁ s∈ ¬≡ (aplus x₁)
... | aplus rec  = aplus (brnum ∷ rec)
ready-maint-s/ready {e = .(plus (seq-ref _ ∷ _))} s n s∈ ¬≡ (aplus (brseq x₁ ∷ x₂)) with ready-maint-s/ready s n s∈ ¬≡ (aplus x₂)
... | aplus rec = aplus (brseq x₁ ∷ rec)
ready-maint-s/ready{θ} {e = (plus (shr-ref s ∷ ._))} s₁ n s∈ ¬≡ (aplus (brshr s∈₁ x ∷ x₁)) with ready-maint-s/ready s₁ n s∈ ¬≡ (aplus x₁) | s SharedVar.≟ s₁
... | aplus rec | yes refl with shr-stats-∈-irr{s}{θ} s∈ s∈₁
... | eq rewrite eq = ⊥-elim (¬≡ x)
ready-maint-s/ready{θ = θ} {e = (plus (shr-ref s ∷ ._))} s₁ n s∈ ¬≡ (aplus (brshr s∈₁ x ∷ x₁)) | aplus rec | no ¬s≡s₁
 with shr-putputget{θ = θ}{v2l = SharedVar.ready}{n} ¬s≡s₁ s∈₁ s∈ (shr-set-mono'{s}{s₁}{θ}{n = n}{s∈} s∈₁) x refl
... | (eq1 , eq2) = aplus (brshr ((shr-set-mono'{s}{s₁}{θ}{n = n}{s∈} s∈₁)) eq1 ∷ rec)

ready-irr-on-irr-s-helper/ready : ∀{θ e} → (s : SharedVar) → (n : ℕ) → (s∈ : Env.isShr∈ s θ) → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready) → (e' : all-ready e θ)
                            → (e'' : all-ready e (Env.set-shr{s = s} θ s∈ SharedVar.ready n)) →  δ e' ≡ δ e''
ready-irr-on-irr-s-helper/ready {θ} {.(plus [])} s n s∈ ¬≡ (aplus []) (aplus []) = refl
ready-irr-on-irr-s-helper/ready {θ} {.(plus (num _ ∷ _))} s n s∈ ¬≡ (aplus (brnum ∷ x₁)) (aplus (brnum ∷ x'))
  rewrite ready-irr-on-irr-s-helper/ready s n s∈ ¬≡ (aplus x₁) (aplus x') = refl
ready-irr-on-irr-s-helper/ready {θ@(Θ Ss ss xs)} {(plus (seq-ref x ∷ _))} s n s∈ ¬≡ (aplus (brseq x₁ ∷ x₂)) (aplus (brseq x₃ ∷ x'))
  rewrite ready-irr-on-irr-s-helper/ready s n s∈ ¬≡ (aplus x₂) (aplus x') | seq∈-eq'{x}{xs} x₁ x₃ = refl
ready-irr-on-irr-s-helper/ready {θ@(Θ Ss ss xs)} {(plus (shr-ref sₑ ∷ _))} s n s∈ ¬≡ (aplus (brshr s∈₁ x ∷ x₁)) (aplus (brshr s∈₂ x₂ ∷ x'))
  with sₑ SharedVar.≟ s
... | yes sₑ≡s rewrite sₑ≡s | shr∈-eq'{s}{ss} s∈ s∈₁ = ⊥-elim (¬≡ x)
... | no ¬sₑ≡s with shr-putputget{θ = θ}{v2l = SharedVar.ready}{n} ¬sₑ≡s s∈₁ s∈ s∈₂ x refl
... | (eq1 , eq2) rewrite ready-irr-on-irr-s-helper/ready s n s∈ ¬≡ (aplus x₁) (aplus x') | eq2 = refl

ready-irr-on-irr-s/ready : ∀{θ e} → (s : SharedVar) → (n : ℕ) → (s∈ : Env.isShr∈ s θ) → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready) → (e' : all-ready e θ)
                     → Σ[ e'' ∈ all-ready e (Env.set-shr{s = s} θ s∈ SharedVar.ready n) ] δ e' ≡ δ e''
ready-irr-on-irr-s/ready s n s∈ ¬≡ e' = e'' , (ready-irr-on-irr-s-helper/ready s n s∈ ¬≡ e' e'')
  where e'' = ready-maint-s/ready s n s∈ ¬≡ e'

ready-irr-on-irr-x-help : ∀{θ e} x n → (x∈ : Env.isVar∈ x θ) → (e' : all-ready e θ) → (SeqVar.unwrap x) ∉ (Xs (FVₑ e))
                          → (e'' : all-ready e (Env.set-var{x = x} θ x∈ n))
                          →  δ e' ≡ δ e''
ready-irr-on-irr-x-help x n x∈ (aplus []) x∉FV (aplus []) = refl
ready-irr-on-irr-x-help x₁ n x∈ (aplus (brnum ∷ a)) x∉FV (aplus (brnum ∷ b)) rewrite ready-irr-on-irr-x-help x₁ n x∈ (aplus a) x∉FV (aplus b) = refl
ready-irr-on-irr-x-help{θ}{e} x₁ n x∈ (aplus (brseq{x = x} x₂ ∷ a)) x∉FV (aplus (brseq x₃ ∷ b))
    with x SeqVar.≟ x₁
... | yes refl = ⊥-elim (x∉FV (here refl))
... | no  ¬x≡x₁ rewrite seq-putputget{θ = θ} ¬x≡x₁ x₂ x∈ x₃ refl
                      | ready-irr-on-irr-x-help x₁ n x∈ (aplus a) (λ x → x∉FV (there x)) (aplus b) = refl
ready-irr-on-irr-x-help{θ} x₁ n x∈ (aplus (brshr{s = s} s∈ x ∷ a)) x∉FV (aplus (brshr s∈₁ x₂ ∷ b))
  rewrite ready-irr-on-irr-x-help x₁ n x∈ (aplus a) x∉FV (aplus b)
        | shr∈-eq'{s = s}{θ = (shr θ)} s∈ s∈₁
  = refl

ready-maint-x : ∀{θ e} x n → (x∈ : Env.isVar∈ x θ) → (e' : all-ready e θ) → (SeqVar.unwrap x) ∉ (Xs (FVₑ e))
                → all-ready e (Env.set-var{x = x} θ x∈ n)
ready-maint-x x n x∈ (aplus []) x∉FV = aplus []
ready-maint-x x₁ n₁ x∈ (aplus (brnum ∷ a)) x∉FV with ready-maint-x x₁ n₁ x∈ (aplus a) x∉FV
... | (aplus r) = aplus (brnum ∷ r)
ready-maint-x{θ} x₁ n x∈ (aplus (brseq{x = x} x₂ ∷ a)) x∉FV with ready-maint-x x₁ n x∈ (aplus a) (λ x₃ → x∉FV (there x₃))
... | (aplus r) = aplus ((brseq ((seq-set-mono'{x}{x₁}{θ}{n}{x∈} x₂))) ∷ r)
ready-maint-x x₁ n x∈ (aplus (brshr s∈ x ∷ a)) x∉FV  with ready-maint-x x₁ n x∈ (aplus a) x∉FV
... | (aplus r) = aplus ((brshr s∈ x) ∷ r)

ready-irr-on-irr-x : ∀{θ e} x n → (x∈ : Env.isVar∈ x θ) → (e' : all-ready e θ) → (SeqVar.unwrap x) ∉ (Xs (FVₑ e))
                     → Σ[ e'' ∈ all-ready e (Env.set-var{x = x} θ x∈ n) ] δ e' ≡ δ e''
ready-irr-on-irr-x x n x∈ e' x∉FV = _ , ready-irr-on-irr-x-help x n x∈ e' x∉FV (ready-maint-x x n x∈ e' x∉FV)

ready-maint-θˡ : ∀{θ e} θ' → (e' : all-ready e θ) → (distinct (Dom θ') (FVₑ e)) → (all-ready e (θ ← θ'))
ready-maint-θˡ θ' (aplus []) Domθ'≠FVe = aplus []
ready-maint-θˡ θ' (aplus (brnum ∷ x₁)) Domθ'≠FVe with ready-maint-θˡ θ' (aplus x₁) Domθ'≠FVe
... | (aplus f) = (aplus (brnum ∷ f))
ready-maint-θˡ{θ} θ' (aplus (brseq{x = x} x₁ ∷ x₂)) Domθ'≠FVe  with ready-maint-θˡ θ' (aplus x₂) ((proj₁ Domθ'≠FVe) , (proj₁ (proj₂ Domθ'≠FVe)) , dist':: (proj₂ (proj₂ Domθ'≠FVe)))
... | (aplus f) = aplus (brseq (Env.seq-←-monoˡ x θ θ' x₁) ∷ f)
ready-maint-θˡ{θ} θ' (aplus (brshr{s = s} s∈ s≡ ∷ x₁)) Domθ'≠FVe  with ready-maint-θˡ θ' (aplus x₁) (((proj₁ Domθ'≠FVe) ,  dist':: (proj₁ (proj₂ Domθ'≠FVe)) , (proj₂ (proj₂ Domθ'≠FVe))))
    | shr-←-irr-get{θ}{θ'}{s} s∈ (λ x → (proj₁ (proj₂ Domθ'≠FVe)) _ x (here refl))
... | (aplus f) | (s∈2 , eq) rewrite eq = aplus ((brshr s∈2 s≡) ∷ f)
ready-irr-on-irr-θˡ-help : ∀{θ e} θ' → (e' : all-ready e θ) → (distinct (Dom θ') (FVₑ e))
                     → (e'' : (all-ready e (θ ← θ'))) → δ e' ≡ δ e''
ready-irr-on-irr-θˡ-help θ' (aplus []) Domθ'≠FVe (aplus []) = refl
ready-irr-on-irr-θˡ-help θ' (aplus (brnum ∷ x₁)) Domθ'≠FVe (aplus (brnum ∷ x₂))
   rewrite ready-irr-on-irr-θˡ-help θ' (aplus x₁) Domθ'≠FVe (aplus x₂)
   = refl
ready-irr-on-irr-θˡ-help{θ} θ' (aplus (brseq{x = x} x₁ ∷ x₂)) Domθ'≠FVe (aplus (brseq x₃ ∷ x₄))
   rewrite ready-irr-on-irr-θˡ-help θ' (aplus x₂) ((proj₁ Domθ'≠FVe) , (proj₁ (proj₂ Domθ'≠FVe)) , dist':: (proj₂ (proj₂ Domθ'≠FVe))) (aplus x₄)
         | seq-←-irr-get'{θ}{θ'}{x} x₁ (λ x → (proj₂ (proj₂ Domθ'≠FVe)) _ x (here refl)) x₃
   = refl
ready-irr-on-irr-θˡ-help{θ} θ' (aplus (brshr{s = s} s∈ x ∷ x₁)) Domθ'≠FVe (aplus (brshr s∈₁ x₂ ∷ x₃))
    rewrite ready-irr-on-irr-θˡ-help θ' (aplus x₁) ((proj₁ Domθ'≠FVe) , dist':: (proj₁ (proj₂ Domθ'≠FVe)) , (proj₂ (proj₂ Domθ'≠FVe))) (aplus x₃)
          | shr-←-irr-get/vals'{θ}{θ'}{s} s∈ (λ x → (proj₁ (proj₂ Domθ'≠FVe)) _ x (here refl)) s∈₁
    = refl

ready-irr-on-irr-θˡ : ∀{θ e} θ' → (e' : all-ready e θ) → (distinct (Dom θ') (FVₑ e))
                     → Σ[ e'' ∈ (all-ready e (θ ← θ')) ] δ e' ≡ δ e''
ready-irr-on-irr-θˡ θ' e' Domθ'≠FVe = _ , ready-irr-on-irr-θˡ-help θ' e' Domθ'≠FVe (ready-maint-θˡ θ' e' Domθ'≠FVe)

ready-maint-θʳ : ∀ {θ' e} θ → (e' : all-ready e θ') → all-ready e (θ ← θ')
ready-maint-θʳ θ (aplus []) = aplus []
ready-maint-θʳ θ (aplus (brnum ∷ bound-readys))
  with ready-maint-θʳ θ (aplus bound-readys)
... | aplus bound-readys' = aplus (brnum ∷ bound-readys')
ready-maint-θʳ {θ'} θ (aplus (brseq {x = x} x∈Domθ' ∷ bound-readys))
  with ready-maint-θʳ θ (aplus bound-readys)
... | aplus bound-readys' = aplus (brseq (seq-←-monoʳ x θ' θ x∈Domθ') ∷ bound-readys')
ready-maint-θʳ {θ'} θ (aplus (brshr {s = s} s∈Domθ' θ's≡ready ∷ bound-readys))
  with ready-maint-θʳ θ (aplus bound-readys)
... | aplus bound-readys' =
  aplus (brshr (shr-←-monoʳ s θ' θ s∈Domθ')
               (trans
                 (shr-stats-←-right-irr' s θ θ' s∈Domθ'
                   (shr-←-monoʳ s θ' θ s∈Domθ'))
                 θ's≡ready) ∷
         bound-readys')

ready-irr-on-irr-θʳ-help : ∀ {θ' e} θ →
  (e' : all-ready e θ') →
  (e'' : all-ready e (θ ← θ')) →
  δ e' ≡ δ e''
ready-irr-on-irr-θʳ-help {θ'} θ (aplus []) (aplus []) = refl
ready-irr-on-irr-θʳ-help {θ'} θ (aplus (brnum ∷ bound-readys')) (aplus (brnum ∷ bound-readys''))
  with ready-irr-on-irr-θʳ-help θ (aplus bound-readys') (aplus bound-readys'')
... | δe'≡δe'' rewrite δe'≡δe'' = refl
ready-irr-on-irr-θʳ-help {θ'} θ
  (aplus (brseq {x = x}  x∈Domθ' ∷ bound-readys'))
  (aplus (brseq {x = .x} x∈Domθ←θ' ∷ bound-readys''))
  with ready-irr-on-irr-θʳ-help θ (aplus bound-readys') (aplus bound-readys'')
... | δe'≡δe'' rewrite δe'≡δe'' | var-vals-←-right-irr' x θ θ' x∈Domθ' x∈Domθ←θ' = refl
ready-irr-on-irr-θʳ-help {θ'} θ
  (aplus (brshr {s = s}  s∈Domθ'   θ's≡ready     ∷ bound-readys'))
  (aplus (brshr {s = .s} s∈Domθ←θ' ⟨θ←θ'⟩s≡ready ∷ bound-readys''))
  with ready-irr-on-irr-θʳ-help θ (aplus bound-readys') (aplus bound-readys'')
... | δe'≡δe'' rewrite δe'≡δe'' | shr-vals-←-right-irr' s θ θ' s∈Domθ' s∈Domθ←θ' = refl

ready-irr-on-irr-θʳ : ∀ {θ' e} θ →
  (e' : all-ready e θ') →
  Σ[ e'' ∈ all-ready e (θ ← θ') ] δ e' ≡ δ e''
ready-irr-on-irr-θʳ θ e' = _ , ready-irr-on-irr-θʳ-help θ e' (ready-maint-θʳ θ e')

CBE⟦p⟧=>CBp : ∀{BV FV E p} → CorrectBinding (E ⟦ p ⟧e) BV FV → ∃ (λ BV → ∃ (λ FV → (CorrectBinding p BV FV)))
CBE⟦p⟧=>CBp{BV}{FV} {E = []} CB = BV , FV , CB
CBE⟦p⟧=>CBp {E = epar₁ q ∷ E} (CBpar CB CB₁ x x₁ x₂ x₃) = CBE⟦p⟧=>CBp{E = E} CB
CBE⟦p⟧=>CBp {E = epar₂ p ∷ E} (CBpar CB CB₁ x x₁ x₂ x₃) = CBE⟦p⟧=>CBp{E = E} CB₁
CBE⟦p⟧=>CBp {E = eloopˢ q ∷ E} (CBloopˢ CB CB₁ x _) = CBE⟦p⟧=>CBp{E = E} CB
CBE⟦p⟧=>CBp {E = eseq q ∷ E} (CBseq CB CB₁ x) = CBE⟦p⟧=>CBp{E = E} CB
CBE⟦p⟧=>CBp {E = esuspend S ∷ E} (CBsusp CB x) = CBE⟦p⟧=>CBp{E = E} CB
CBE⟦p⟧=>CBp {E = etrap ∷ E} (CBtrap CB) = CBE⟦p⟧=>CBp{E = E} CB

CBE⟦p⟧=>CBp' : ∀{BV FV E p p'} → p ≐ E ⟦ p' ⟧e →  CorrectBinding (p) BV FV → ∃ (λ BV → ∃ (λ FV → (CorrectBinding p' BV FV)))
CBE⟦p⟧=>CBp'{E = E}{p' = p'} peq cb = CBE⟦p⟧=>CBp{E = E}{p = p'} (subst (λ x → CorrectBinding x _ _) (sym (unplug peq)) cb)
-- , (BV⊆S , BV⊆s , BV⊆x)

CBp⊆CBE⟦p⟧ : ∀{BVp FVp BVE FVE} → (E : EvaluationContext ) → (p : Term) → CorrectBinding p BVp FVp → CorrectBinding (E ⟦ p ⟧e) BVE FVE → (FVp ⊆ FVE × BVp ⊆ BVE)

CBp⊆CBE⟦p⟧ [] p CBp CBE with binding-is-function CBp CBE
... | (e1 , e2) rewrite e1 | e2 = (((λ x z → z) , (λ x z → z) , (λ x z → z))) , (((λ x z → z) , (λ x z → z) , (λ x z → z)))
CBp⊆CBE⟦p⟧ (epar₁ q ∷ E) p CBp (CBpar CBE CBE₁ x x₁ x₂ x₃) with CBp⊆CBE⟦p⟧ E p CBp CBE
... | (FV⊆S , FV⊆s , FV⊆x) , (BV⊆S , BV⊆s , BV⊆x) = ((λ x y → ++ˡ (FV⊆S x y)) , ((λ x y → ++ˡ (FV⊆s x y))) , ((λ x y → ++ˡ (FV⊆x x y)))) , (((λ x y → ++ˡ (BV⊆S x y))) , ((λ x y → ++ˡ (BV⊆s x y))) , ((λ x y → ++ˡ (BV⊆x x y))))

CBp⊆CBE⟦p⟧ (epar₂ p ∷ E) p₁ CBp (CBpar{BVp = BVp}{FVp = FVp} CBE CBE₁ x x₁ x₂ x₃) with CBp⊆CBE⟦p⟧ E p₁ CBp CBE₁
... | (FV⊆S , FV⊆s , FV⊆x) , (BV⊆S , BV⊆s , BV⊆x)
   = ((λ x z → ++ʳ (proj₁ FVp) (FV⊆S x z)) , (λ x → (++ʳ (proj₁ (proj₂ FVp))) ∘ (FV⊆s x)) , ((λ x → (++ʳ (proj₂ (proj₂ FVp))) ∘ (FV⊆x x))))
   , ((λ x z → ++ʳ (proj₁ BVp) (BV⊆S x z)) , (λ x → (++ʳ (proj₁ (proj₂ BVp))) ∘ (BV⊆s x)) , ((λ x → (++ʳ (proj₂ (proj₂ BVp))) ∘ (BV⊆x x))))
CBp⊆CBE⟦p⟧ (eloopˢ q ∷ E) p CBp (CBloopˢ CBE CBE₁ x _) with CBp⊆CBE⟦p⟧ E p CBp CBE
... | (FV⊆S , FV⊆s , FV⊆x) , (BV⊆S , BV⊆s , BV⊆x) = ((λ x y → ++ˡ (FV⊆S x y)) , ((λ x → ++ˡ ∘ (FV⊆s x)) ) , get FV⊆x) , (get BV⊆S , get BV⊆s , get BV⊆x)
   where
   get : ∀{a b c} → a ⊆¹ b → a ⊆¹ (b ++ c)
   get f = λ x y → ++ˡ (f x y)
CBp⊆CBE⟦p⟧ (eseq q ∷ E) p CBp (CBseq CBE CBE₁ x) with CBp⊆CBE⟦p⟧ E p CBp CBE
... | (FV⊆S , FV⊆s , FV⊆x) , (BV⊆S , BV⊆s , BV⊆x) = ((λ x y → ++ˡ (FV⊆S x y)) , ((λ x → ++ˡ ∘ (FV⊆s x)) ) , get FV⊆x) , (get BV⊆S , get BV⊆s , get BV⊆x)
   where
   get : ∀{a b c} → a ⊆¹ b → a ⊆¹ (b ++ c)
   get f = λ x y → ++ˡ (f x y)
   --(λ x₁ x₂ → {!there x₂!})
CBp⊆CBE⟦p⟧ (esuspend S ∷ E) p CBp (CBsusp CBE x) with CBp⊆CBE⟦p⟧ E p CBp CBE
... | (FV⊆S , FV⊆s , FV⊆x) , BV⊆ = (((λ x y → there (FV⊆S x y)) , FV⊆s , FV⊆x)) , BV⊆
CBp⊆CBE⟦p⟧ (etrap ∷ E) p CBp (CBtrap CBE) = CBp⊆CBE⟦p⟧ E p CBp CBE


CBp⊆CBE⟦p⟧' : ∀{BVp FVp BVE FVE} E p p' → p ≐ E ⟦ p' ⟧e → CorrectBinding p' BVp FVp → CorrectBinding p BVE FVE → (FVp ⊆ FVE × BVp ⊆ BVE)
CBp⊆CBE⟦p⟧' E p p' peq cbp' cbp = CBp⊆CBE⟦p⟧ E p' cbp' (subst (λ x → CorrectBinding x _ _) (sym (unplug peq)) cbp)

inspecting-cb-distinct-double-unplug : ∀{p q Ep Eq p' q' BV FV} → CorrectBinding (p ∥ q) BV FV
                            → p ≐ Ep ⟦ p' ⟧e → q ≐ Eq ⟦ q' ⟧e
                            →
                            Σ (Term × VarList × VarList)
                              λ {(o , BVo , FVo)
                                → CorrectBinding o BVo FVo
                                × o ≡ (p' ∥ q')}
inspecting-cb-distinct-double-unplug{p' = p'}{q'} (CBpar CBp CBq BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq) p=Ep⟦p'⟧ q=Eq⟦q'⟧
     with CBE⟦p⟧=>CBp' p=Ep⟦p'⟧ CBp | CBE⟦p⟧=>CBp' q=Eq⟦q'⟧ CBq
... | (BVp' , FVp' , CBp') | (BVq' , FVq' , CBq')
   with CBp⊆CBE⟦p⟧' _ _ _ p=Ep⟦p'⟧ CBp' CBp | CBp⊆CBE⟦p⟧' _ _ _ q=Eq⟦q'⟧ CBq' CBq
... | (FVp'⊆FVp , BVp'⊆BVp) | (FVq'⊆FVq , BVq'⊆BVq)
  = (_ , _ , _) , CBpar CBp' CBq' (⊆-rep-dist-both BVp'⊆BVp BVq'⊆BVq BVp≠BVq) (⊆-rep-dist-both FVp'⊆FVp BVq'⊆BVq FVp≠BVq) (⊆-rep-dist-both BVp'⊆BVp FVq'⊆FVq BVp≠FVq) (⊆¹-rep-dist-both (proj₂ (proj₂ FVp'⊆FVp)) (proj₂ (proj₂ FVq'⊆FVq)) Xp≠Xq) , refl
  where
    ⊆¹-rep-dist-both : ∀{a b c d} → a ⊆¹ b →  c ⊆¹ d → distinct' b d → distinct' a c
    ⊆¹-rep-dist-both sub1 sub2 dist = λ z z₁ z₂ → dist z (sub1 z z₁) (sub2 z z₂)
    ⊆-rep-dist-both : ∀{a b c d} → a ⊆ b →  c ⊆ d → distinct b d → distinct a c
    ⊆-rep-dist-both a b c = (⊆¹-rep-dist-both , ⊆¹-rep-dist-both , ⊆¹-rep-dist-both) # a # b # c
