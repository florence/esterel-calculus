module sn-calculus-confluence.potpot where

open import utility
open import sn-calculus
open import context-properties
  using (->pot-view)

open import Esterel.Lang
open import Esterel.Lang.CanFunction
  using (Can ; Canₛ ; Canₛₕ ; Canθ ; Canθₛ ; Canθₛₕ)
open import Esterel.Lang.CanFunction.Properties
  using ( canθₛ-set-sig-monotonic-absence-lemma ; canθₛₕ-set-sig-monotonic-absence-lemma
        ; canθ-shr-var-irr
        )
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
open import Esterel.CompletionCode as Code
  using () renaming (CompletionCode to Code)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)

open import Data.Bool
  using (Bool ; true ; false ; if_then_else_)
open import Data.Empty
  using (⊥ ; ⊥-elim)
open import Data.List
  using (List ; [] ; _∷_ ; [_])
open import Data.List.Any
  using (Any ; here ; there ; any)
open import Data.Maybe
  using (Maybe ; just ; nothing)
open import Data.Nat
  using (ℕ ; _≟_ ; zero ; suc ; _+_)
open import Data.Nat.Properties.Simple
  using ( +-comm ; +-assoc)
open import Data.Product
  using (Σ ; Σ-syntax ; _,_ ; proj₁ ; proj₂ ; _,′_ ; _×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Function
  using (_∘_ ; id ; _∋_)
open import Relation.Nullary
  using (¬_ ; Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; subst ; module ≡-Reasoning)

open ->pot-view
open ≡-Reasoning
  using (begin_ ; _∎ ; _≡⟨_⟩_ ; _≡⟨⟩_)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

pot-pot-conf-rec : ∀{p θ ql θl qr θr eql eqr}
                 → {ρθ·psn⟶₁ρθl·ql  :  (ρ θ · p) sn⟶₁ (ρ θl · ql)}
                 → {ρθ·psn⟶₁ρθr·qr  :  (ρ θ · p) sn⟶₁ (ρ θr · qr)}
                 → ->pot-view  ρθ·psn⟶₁ρθl·ql  eql
                 → ->pot-view  ρθ·psn⟶₁ρθr·qr  eqr
                 → (ρ θl · ql ≡ ρ θr · qr)
                   ⊎
                   Σ[ θo ∈ Env ]
                   (ρ θl · ql) sn⟶₁ (ρ θo · p) ×
                   (ρ θr · qr) sn⟶₁ (ρ θo · p)


pot-pot-conf-rec {p} {θ} {.p} {θl} {.p} {θr} {_} {_}
                 {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
                 {.(rabsence {θ} {p} {S'} S'∈ θS'≡unknown S'∉can-p-θ)}
                 (vabsence S S∈ θS≡unknown S∉can-p-θ)
                 (vabsence S' S'∈ θS'≡unknown S'∉can-p-θ)
  with S Signal.≟ S'
... | yes refl = inj₁ refl
... | no S≢S' =
  inj₂
  (_ ,
   subst (λ sig* → ρ θl · p sn⟶₁ ρ (Θ sig* (Env.shr θl) (Env.var θl)) · p)
     (SigMap.put-comm {_} {Env.sig θ} {S} {S'} {Signal.absent} {Signal.absent} S≢S')
     (rabsence {θl} {p} {S'} S'∈Domθl θlS'≡unknown
       (λ S'∈can-p-θl →
         S'∉can-p-θ
           (canθₛ-set-sig-monotonic-absence-lemma (Env.sig θ) 0 p S Env.[]env
             S∈ θS≡unknown (Signal.unwrap S') S'∈can-p-θl))) ,′
   rabsence {θr} {p} {S} S∈Domθr θrS≡unknown
     (λ S∈can-p-θr →
       S∉can-p-θ
         (canθₛ-set-sig-monotonic-absence-lemma (Env.sig θ) 0 p S' Env.[]env
             S'∈ θS'≡unknown (Signal.unwrap S) S∈can-p-θr)))
  where
    S∈Domθr      = Env.sig-set-mono' {S}  {S'} {θ} {Signal.absent} {S'∈} S∈
    S'∈Domθl     = Env.sig-set-mono' {S'} {S}  {θ} {Signal.absent} {S∈}  S'∈
    θrS≡unknown  = SigMap.putputget {_} {Env.sig θ} {S}  {S'} {Signal.unknown} {Signal.absent}
                      S≢S'         S∈  S∈Domθr  θS≡unknown
    θlS'≡unknown = SigMap.putputget {_} {Env.sig θ} {S'} {S}  {Signal.unknown} {Signal.absent}
                     (S≢S' ∘ sym) S'∈ S'∈Domθl θS'≡unknown


pot-pot-conf-rec {p} {θ} {.p} {θl} {.p} {θr} {_} {_}
                 {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
                 {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
                 (vabsence S S∈ θS≡unknown S∉can-p-θ)
                 (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ) =
  inj₂
  (_ ,
   rreadyness {θl} {p} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-p-θl →
       s∉can-p-θ
         (canθₛₕ-set-sig-monotonic-absence-lemma (Env.sig θ) 0 p S Env.[]env
           S∈ θS≡unknown (SharedVar.unwrap s) s∈can-p-θl)) ,′
   rabsence {θr} {p} {S} S∈ θS≡unknown
     (λ S∈can-p-θr →
       S∉can-p-θ
         (subst (Signal.unwrap S ∈_)
           (cong proj₁ (canθ-shr-var-irr (Env.sig θ) 0 p Env.[]env Env.[]env refl))
           S∈can-p-θr)))


pot-pot-conf-rec {p} {θ} {.p} {θl} {.p} {θr} {_} {_}
                 {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
                 {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
                 (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
                 (vabsence S S∈ θS≡unknown S∉can-p-θ) =
  inj₂
  (_ ,
   rabsence {θl} {p} {S} S∈ θS≡unknown
     (λ S∈can-p-θl →
       S∉can-p-θ
         (subst (Signal.unwrap S ∈_)
           (cong proj₁ (canθ-shr-var-irr (Env.sig θ) 0 p Env.[]env Env.[]env refl))
           S∈can-p-θl)) ,′
   rreadyness {θr} {p} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-p-θr →
       s∉can-p-θ
         (canθₛₕ-set-sig-monotonic-absence-lemma (Env.sig θ) 0 p S Env.[]env
           S∈ θS≡unknown (SharedVar.unwrap s) s∈can-p-θr)))


pot-pot-conf-rec {p} {θ} {.p} {θl} {.p} {θr} {_} {_}
                 {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
                 {.(rreadyness {θ} {p} {s'} s'∈ θs'≡old⊎θs'≡new s'∉can-p-θ)}
                 (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
                 (vreadyness s' s'∈ θs'≡old⊎θs'≡new s'∉can-p-θ)
  with s SharedVar.≟ s'
... | yes refl rewrite Env.shr-vals-∈-irr {s'} {θ} s∈ s'∈ = inj₁ refl
... | no s≢s' =
  inj₂
  (_ ,
   subst (λ shr* → ρ θl · p sn⟶₁ ρ (Θ (Env.sig θl) shr* (Env.var θl)) · p)
     (cong Env.shr
       (begin
           Env.set-shr {s'} θl s'∈Domθl SharedVar.ready
             (Env.shr-vals {s'} θl s'∈Domθl)
        ≡⟨ cong (Env.set-shr {s'} θl s'∈Domθl SharedVar.ready ∘ proj₂) θls'≡θs' ⟩
           Env.set-shr {s'} θl s'∈Domθl SharedVar.ready θs'
        ≡⟨ cong (λ shr* → Θ (Env.sig θ) shr* (Env.var θ))
             (ShrMap.put-comm {_} {Env.shr θ} {s} {s'}
               {SharedVar.ready , θs} {SharedVar.ready , θs'} s≢s') ⟩
           Env.set-shr {s} θr s∈Domθr SharedVar.ready θs
        ≡⟨ cong (Env.set-shr {s} θr s∈Domθr SharedVar.ready ∘ proj₂) (sym θrs≡θs) ⟩
           Env.set-shr {s} θr s∈Domθr SharedVar.ready
             (Env.shr-vals {s} θr s∈Domθr)
        ∎))
     (rreadyness {θl} {p} {s'} s'∈Domθl
       (Data.Sum.map
         (trans (cong proj₁ θls'≡θs'))
         (trans (cong proj₁ θls'≡θs'))
         θs'≡old⊎θs'≡new)
       (λ s'∈can-p-θl →
         s'∉can-p-θ
           (subst (SharedVar.unwrap s' ∈_)
             (cong (proj₂ ∘ proj₂) (canθ-shr-var-irr (Env.sig θ) 0 p Env.[]env Env.[]env refl))
             s'∈can-p-θl))) ,′
   rreadyness {θr} {p} {s} s∈Domθr
     (Data.Sum.map
       (trans (cong proj₁ θrs≡θs))
       (trans (cong proj₁ θrs≡θs))
       θs≡old⊎θs≡new)
     (λ s∈can-p-θr →
       s∉can-p-θ
         (subst (SharedVar.unwrap s ∈_)
           (cong (proj₂ ∘ proj₂) (canθ-shr-var-irr (Env.sig θ) 0 p Env.[]env Env.[]env refl))
           s∈can-p-θr)))
  where
    θs       = Env.shr-vals {s} θ s∈
    θs'      = Env.shr-vals {s'} θ s'∈
    s∈Domθr  = Env.shr-set-mono' {s}  {s'} {θ} {SharedVar.ready} {θs'} {s'∈} s∈
    s'∈Domθl = Env.shr-set-mono' {s'} {s}  {θ} {SharedVar.ready} {θs}  {s∈}  s'∈
    θrs≡θs   = ShrMap.putputget {_} {Env.shr θ} {s}  {s'} {_} {SharedVar.ready ,′ θs'}
                      s≢s'         s∈  s∈Domθr  refl
    θls'≡θs' = ShrMap.putputget {_} {Env.shr θ} {s'}  {s} {_} {SharedVar.ready ,′ θs}
                     (s≢s' ∘ sym) s'∈ s'∈Domθl  refl
