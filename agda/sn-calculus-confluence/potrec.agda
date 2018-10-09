module sn-calculus-confluence.potrec where

open import utility
open import sn-calculus
open import context-properties
  using (->pot-view ; ->E-view)
open import sn-calculus-confluence.helper

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
open import Esterel.Lang.PotentialFunction
open import Esterel.Lang.PotentialFunction.Properties
  using (canθₛ-subset ; canθₛₕ-subset ; canθₛ-membership ; canθₛₕ-membership
       ; canθₛ-mergeˡ ; canθₛₕ-mergeˡ
       ; canθ-is-present ; canθ-is-absent
       ; canθₛₕ-emit ; canθₛ-emit
       ; term-raise ; canₛ-raise ; canₛₕ-raise
       ; term-nothin ; canₛ-term-nothin ; canₛₕ-term-nothin
       ; canₛ-if-true ; canₛ-if-false ; canₛₕ-if-true ; canₛₕ-if-false
       ; canₛ-capture-emit-signal ; canₛₕ-capture-set-shared)

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
open ->E-view

open term-nothin
open term-raise
open ≡-Reasoning
  using (begin_ ; _∎ ; _≡⟨_⟩_ ; _≡⟨⟩_)

open import Data.OrderedListMap Signal Signal.unwrap Signal.Status as SigM
open import Data.OrderedListMap SharedVar SharedVar.unwrap (Σ SharedVar.Status (λ _ → ℕ)) as ShrM
open import Data.OrderedListMap SeqVar SeqVar.unwrap ℕ as SeqM

ρ-pot-conf-rec : ∀{p θ ql θl qr θr p≡ql E pin qin FV₀ BV₀}
                 → {ρθ·psn⟶₁ρθl·ql : (ρ θ · p) sn⟶₁ (ρ θl · ql)}
                 → {ρθ·psn⟶₁ρθr·qr : (ρ θ · p) sn⟶₁ (ρ θr · qr)}
                 → {p≐E⟦pin⟧      : p ≐ E ⟦ pin ⟧e}
                 → {qr≐E⟦qin⟧     : qr ≐ E ⟦ qin ⟧e}
                 → CorrectBinding (ρ θ · p) FV₀ BV₀
                 → ->pot-view ρθ·psn⟶₁ρθl·ql p≡ql
                 → ->E-view   ρθ·psn⟶₁ρθr·qr p≐E⟦pin⟧ qr≐E⟦qin⟧
                 →
                  (ρ θl · ql sn⟶₁ ρ θr · qr) ⊎
                  (Σ[ s ∈ Term ]
                   Σ[ θo ∈ Env.Env ]
                      (ρ θl · ql) sn⟶₁ (ρ θo · s)
                    × (ρ θr · qr) sn⟶₁ (ρ θo · s))


ρ-pot-conf-rec {p} {θ} {ql} {θl} {.(E ⟦ qin ⟧e)} {θr} {_} {E} {.(ρ θin · qin)} {qin} {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)} {.(rmerge {θ} {θin} p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧}
               (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vmerge {.θ} {θin} {.p} {.qin} {.E})
  with Env.Sig∈ S θin
... | yes S∈Domθin
  rewrite SigMap.update-union-union S Signal.absent (Env.sig θ) (Env.sig θin) S∈ S∈Domθin
  = inj₁ (ρ θl · ql sn⟶₁ ρ (θl ← θin) · E ⟦ qin  ⟧e ∋ rmerge {θl} {θin} p≐E⟦pin⟧)
... | no S∉Domθin
  with Env.sig-←-irr-get {θ} {θin} {S} S∈ S∉Domθin -- θr ≡ (θ ← θin)
... | S∈Domθ←θin , θS≡⟨θ←θin⟩S
  = inj₂
    (_ , _ ,
     subst (λ θ* → ρ θl · ql sn⟶₁ ρ θ* · E ⟦ qin ⟧e)
       ((Env.set-sig {S} θ S∈ Signal.absent) ← θin ≡
        Env.set-sig {S} (θ ← θin) S∈Domθ←θin Signal.absent ∋
        cong (λ sig* → Θ sig* (Env.shr (θ ← θin)) (Env.var (θ ← θin)))
          (SigMap.put-union-comm S Signal.absent (Env.sig θ) (Env.sig θin) S∉Domθin))
       (ρ θl · ql sn⟶₁ ρ (θl ← θin) · E ⟦ qin ⟧e ∋
        rmerge {θl} {θin} p≐E⟦pin⟧) ,′
     (ρ (θ ← θin) · E ⟦ qin ⟧e sn⟶₁ ρ (Env.set-sig {S} (θ ← θin) S∈Domθ←θin Signal.absent) · E ⟦ qin ⟧e ∋
      (rabsence {θr} {_} {S} S∈Domθ←θin (trans (sym θS≡⟨θ←θin⟩S) θS≡unknown)
        (λ S∈can-E⟦qin⟧-θ←θin →
          S∉can-p-θ
            (canθₛ-mergeˡ (Env.sig θ) Env.[]env cbp p≐E⟦pin⟧
              S S∉Domθin S∈can-E⟦qin⟧-θ←θin)))))


ρ-pot-conf-rec {p} {θ} {ql} {θl} {.(E ⟦ qin ⟧e)} {θr} {_} {E} {.(ρ θin · qin)} {qin} {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)} {.(rmerge p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧}
               (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vmerge {.θ} {θin} {.p} {.qin} {.E})
  with Env.Shr∈ s θin
... | yes s∈Domθin
  rewrite ShrMap.update-union-union s (SharedVar.ready , Env.shr-vals {s} θ s∈) (Env.shr θ) (Env.shr θin) s∈ s∈Domθin
  = inj₁ (rmerge {θl} {θin} p≐E⟦pin⟧)
... | no s∉Domθin
  with Env.shr-←-irr-get {θ} {θin} {s} s∈ s∉Domθin
... | s∈Domθ←θin , θs≡⟨θ←θin⟩s
  = inj₂
    (_ , _ ,
     subst (λ θ* → ρ θl · ql sn⟶₁ ρ θ* · E ⟦ qin ⟧e)
       (cong (λ shr* → Θ (Env.sig (θ ← θin)) shr* (Env.var (θ ← θin)))
         (trans
           (cong (λ shrval* →
                   ShrMap.union
                     (ShrMap.update (Env.shr θ) s (SharedVar.ready , proj₂ shrval*))
                     (Env.shr θin))
             (ShrMap.U-∉-irr-get-help-m {_} {Env.shr θ} {Env.shr θin} {s}
                                        s∈ s∉Domθin s∈Domθ←θin ))
           (ShrMap.put-union-comm s (SharedVar.ready , Env.shr-vals {s} (θ ← θin) s∈Domθ←θin)
                                  (Env.shr θ) (Env.shr θin) s∉Domθin)))
       (rmerge {θl} {θin} p≐E⟦pin⟧) ,′
     rreadyness {θr} {_} {s} s∈Domθ←θin
       (Data.Sum.map (trans (sym θs≡⟨θ←θin⟩s)) (trans (sym θs≡⟨θ←θin⟩s))
                     θs≡old⊎θs≡new)
       (λ s∈can-E⟦qin⟧-θ←θin →
         s∉can-p-θ
           (canθₛₕ-mergeˡ (Env.sig θ) Env.[]env cbp p≐E⟦pin⟧
             s s∉Domθin s∈can-E⟦qin⟧-θ←θin)))


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ qin ⟧e)} {.θ} {_} {E}
               {.(present _ ∣⇒ qin ∣⇒ _)} {qin} {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(ris-present {θ} {S'} S'∈ θS'≡present p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧}
               (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vis-present {.θ} {S'} {S∈ = S'∈} {θS'≡present} {.p≐E⟦pin⟧})
  with S' Signal.≟ S
... | yes refl =
  ((Signal.unknown ≡ Signal.present → _) ∋ λ ())
  (trans (trans (sym θS≡unknown) (Env.sig-stats-∈-irr {S} {θ} S∈ S'∈)) θS'≡present)
... | no S'≠S =
  inj₂
  (_ , _ ,
   ris-present {θl} {S'}
     (Env.sig-set-mono' {S'} {S} {θ} {_} {S∈} S'∈)
     (Env.sig-putputget {S'} {S} {θ} S'≠S S'∈ S∈ _ θS'≡present)
     p≐E⟦pin⟧ ,′
   rabsence {θ} {_} {S} S∈ θS≡unknown
     (λ S∈can-E⟦qin⟧-θ →
      S∉can-p-θ
       (subst (Signal.unwrap S ∈_)
         (cong proj₁ (sym (canθ-is-present (Env.sig θ) S'∈ Env.[]env p≐E⟦pin⟧ θS'≡present)) )
         S∈can-E⟦qin⟧-θ)))


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ qin ⟧e)} {.θ} {_} {E}
               {.(present _ ∣⇒ _ ∣⇒ qin)} {qin} {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(ris-absent {θ} {S'} S'∈ θS'≡absent p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧}
               (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vis-absent {.θ} {S'} {S∈ = S'∈} {θS'≡absent} {.p≐E⟦pin⟧})
  with S' Signal.≟ S
... | yes refl =
  ((Signal.unknown ≡ Signal.absent → _) ∋ λ ())
  (trans (trans (sym θS≡unknown) (Env.sig-stats-∈-irr {S} {θ} S∈ S'∈)) θS'≡absent)
... | no S'≠S =
  inj₂
  (_ , _ ,
   ris-absent {θl} {S'}
     (Env.sig-set-mono' {S'} {S} {θ} {_} {S∈} S'∈)
     (Env.sig-putputget {S'} {S} {θ} S'≠S S'∈ S∈ _ θS'≡absent)
     p≐E⟦pin⟧ ,′
   rabsence {θ} {_} {S} S∈ θS≡unknown
     (λ S∈can-E⟦qin⟧-θ →
      S∉can-p-θ
       (subst (Signal.unwrap S ∈_)
         (cong proj₁ (sym (canθ-is-absent (Env.sig θ) S'∈ Env.[]env p≐E⟦pin⟧ θS'≡absent)))
         S∈can-E⟦qin⟧-θ)))


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ qin ⟧e)} {.θ} {_} {E}
               {.(present _ ∣⇒ qin ∣⇒ _)} {qin} {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(ris-present {θ} {S'} S'∈ θS'≡present p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧}
               (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vis-present {.θ} {S'} {S∈ = S'∈} {θS'≡present} {.p≐E⟦pin⟧}) =
  inj₂
  (_ , _ ,
   ris-present {θl} {S'} S'∈ θS'≡present p≐E⟦pin⟧ ,′
   rreadyness {θ} {_} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-E⟦qin⟧-θ →
       s∉can-p-θ
         (subst (SharedVar.unwrap s ∈_)
           (cong (proj₂ ∘ proj₂)
             (sym (canθ-is-present (Env.sig θ) S'∈ Env.[]env p≐E⟦pin⟧ θS'≡present)))
           s∈can-E⟦qin⟧-θ)))


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ qin ⟧e)} {.θ} {_} {E}
               {.(present _ ∣⇒ _ ∣⇒ qin)} {qin} {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(ris-absent {θ} {S'} S'∈ θS'≡absent p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧}
               (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vis-absent {.θ} {S'} {S∈ = S'∈} {θS'≡absent} {.p≐E⟦pin⟧}) =
  inj₂
  (_ , _ ,
   ris-absent {θl} {S'} S'∈ θS'≡absent p≐E⟦pin⟧ ,′
   rreadyness {θ} {_} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-E⟦qin⟧-θ →
       s∉can-p-θ
         (subst (SharedVar.unwrap s ∈_)
           (cong (proj₂ ∘ proj₂)
             (sym (canθ-is-absent (Env.sig θ) S'∈ Env.[]env p≐E⟦pin⟧ θS'≡absent)))
           s∈can-E⟦qin⟧-θ)))


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ nothin ⟧e)} {θr} {_} {E}
               {.(emit S')} {.nothin} {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(remit {θ} {p} {S'} S'∈ θS'≢absent p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧}
               (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vemit {.θ} {.p} {S'} {.E} {S'∈} {θS'≢absent} {.p≐E⟦pin⟧}) =
  inj₂
  (_ , _ ,
   remit {θl} {_} {S'} S'∈ θS'≢absent p≐E⟦pin⟧ ,′
   rreadyness {θr} {_} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-E⟦nothin⟧-θr →
       s∉can-p-θ
         (canθₛₕ-emit θ S'∈ Env.[]env p≐E⟦pin⟧
           θS'≢absent
           (canθₛ-membership (Env.sig θ) 0 p Env.[]env S'
             (λ θ* → canₛ-capture-emit-signal θ* p≐E⟦pin⟧))
           s s∈can-E⟦nothin⟧-θr)))


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ nothin ⟧e)} {θr} {_} {E}
               {.(emit S')} {.nothin} {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(remit {θ} {p} {S'} S'∈ θS'≢absent p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧}
               (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vemit {.θ} {.p} {S'} {.E} {S'∈} {θS'≢absent} {.p≐E⟦pin⟧})
  with S' Signal.≟ S
... | yes refl =
  ⊥-elim
    (S∉can-p-θ
      (canθₛ-membership (Env.sig θ) 0 p Env.[]env S'
        (λ θ* → canₛ-capture-emit-signal θ* p≐E⟦pin⟧)))
... | no S'≢S =
  inj₂
  (_ , _ ,
   remit {θl} {_} {S'}
     (SigMap.insert-mono {_} {S'} {Env.sig θ} {S} {Signal.absent} S'∈)
     (θS'≢absent ∘
      trans
        (sym (SigMap.putputget {_} {Env.sig θ} {S'} {S}
               {_} {Signal.absent} S'≢S S'∈ S'∈Domθl refl)))
     p≐E⟦pin⟧ ,′
   subst (λ sig* → ρ θr · E ⟦ nothin ⟧e sn⟶₁ ρ (Θ sig* (Env.shr θ) (Env.var θ)) · E ⟦ nothin ⟧e)
     (SigMap.put-comm {_} {Env.sig θ} {_} {_} {Signal.present} {Signal.absent} S'≢S)
     (rabsence {θr} {_} {S}
       S∈Domθr
       (SigMap.putputget {_} {Env.sig θ} {S} {S'} {_} {Signal.present}
        (S'≢S ∘ sym) S∈ S∈Domθr θS≡unknown)
       (λ S''∈can-E⟦nothin⟧-θr →
         S∉can-p-θ
           (canθₛ-emit θ S'∈ Env.[]env p≐E⟦pin⟧
             θS'≢absent
             (canθₛ-membership (Env.sig θ) 0 p Env.[]env S'
               (λ θ* → canₛ-capture-emit-signal θ* p≐E⟦pin⟧))
             S S''∈can-E⟦nothin⟧-θr))))
  where S∈Domθr = SigMap.insert-mono {_} {S} {Env.sig θ} {S'} {Signal.present} S∈
        S'∈Domθl = SigMap.insert-mono {_} {S'} {Env.sig θ} {S} {Signal.absent} S'∈

ρ-pot-conf-rec {p} {θ} {.p} {θl}
               {.(E ⟦ ρ (Θ SigMap.empty ShrMap.[ s' ↦ (SharedVar.old , δ e') ] VarMap.empty) · p' ⟧e)}
               {.θ} {_} {E}
               {.(shared s' ≔ e in: p')}
               {.(ρ (Θ SigMap.empty ShrMap.[ s' ↦ (SharedVar.old , δ e') ] VarMap.empty) · p')}
               {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(rraise-shared e' p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vraise-shared {.θ} {.p} {s'} {e} {p'} {.E} {e'} {.p≐E⟦pin⟧})
  with ready-maint/irr S S∈ Signal.absent e'
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ δe* →
           (ρ θl · p) sn⟶₁
           (ρ θl · E ⟦ ρ ([s,δe]-env s' δe*) · p' ⟧e))
     (sym δe'≡δe'')
     (rraise-shared e'' p≐E⟦pin⟧) ,′
   rabsence {θ} {_} {S} S∈ θS≡unknown
     (λ S∈can-E⟦ρΘp'⟧-θ →
       S∉can-p-θ
         (canθₛ-subset (Env.sig θ) 0 (E ⟦ ρ ([s,δe]-env s' (δ e')) · p' ⟧e) p Env.[]env
           (λ θ* S* → canₛ-raise θ* (tshared (δ e') s' e p') p≐E⟦pin⟧ S*)
           S S∈can-E⟦ρΘp'⟧-θ)))


ρ-pot-conf-rec {p} {θ} {.p} {θl}
               {.(E ⟦ ρ (Θ SigMap.empty ShrMap.[ s' ↦ (SharedVar.old , δ e') ] VarMap.empty) · p' ⟧e)}
               {.θ} {_} {E}
               {.(shared s' ≔ e in: p')}
               {.(ρ (Θ SigMap.empty ShrMap.[ s' ↦ (SharedVar.old , δ e') ] VarMap.empty) · p')}
               {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(rraise-shared e' p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vraise-shared {.θ} {.p} {s'} {e} {p'} {.E} {e'} {.p≐E⟦pin⟧})
  with ready-irr-on-irr-s/ready {θ} {e} s (Env.shr-vals {s} θ s∈) s∈ (θs≢ready θs≡old⊎θs≡new)
         e'
  where θs≢ready : typeof θs≡old⊎θs≡new → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready)
        θs≢ready (inj₁ θs≡old) θs≡ready with trans (sym θs≡old) θs≡ready
        ... | ()
        θs≢ready (inj₂ θs≡new) θs≡ready with trans (sym θs≡new) θs≡ready
        ... | ()
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ δe* →
           (ρ θl · p) sn⟶₁
           (ρ θl · E ⟦ ρ ([s,δe]-env s' δe*) · p' ⟧e))
     (sym δe'≡δe'')
     (rraise-shared e'' p≐E⟦pin⟧) ,′
   rreadyness {θ} {_} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-E⟦ρΘp'⟧-θ →
       s∉can-p-θ
         (canθₛₕ-subset (Env.sig θ) 0
           (E ⟦ ρ ([s,δe]-env s' (δ e')) · p' ⟧e) p Env.[]env
           (λ θ* S* → canₛ-raise θ* (tshared (δ e') s' e p') p≐E⟦pin⟧ S*)
           (λ θ* s* → canₛₕ-raise θ* (tshared (δ e') s' e p') p≐E⟦pin⟧ s*)
           s s∈can-E⟦ρΘp'⟧-θ)))


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ nothin ⟧e)} {θr} {_} {E}
               {.(s' ⇐ e)} {.nothin} {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(rset-shared-value-old {θ} {p} {s'} e' s'∈ θs'≡old p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vset-shared-value-old {.θ} {.p} {s'} {e} {.E} {e'} {s'∈} {θs'≡old})
  with ready-maint/irr S S∈ Signal.absent e'
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ δe* →
            ρ θl · p sn⟶₁
            ρ (θl-set-shr δe*) · E ⟦ nothin ⟧e)
     (sym δe'≡δe'')
     (rset-shared-value-old {θl} {_} {s'} e'' s'∈ θs'≡old p≐E⟦pin⟧) ,′
   rabsence {θr} {_} {S} S∈ θS≡unknown
     (λ S∈can-E⟦nothin⟧-θr →
       S∉can-p-θ
         (canθₛ-subset (Env.sig θ) 0 (E ⟦ nothin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-term-nothin θ* θ* refl (tset-shr s' e) p≐E⟦pin⟧ S*)
           S S∈can-E⟦nothin⟧-θr)))
  where
    θl-set-shr : ℕ → Env
    θl-set-shr n = Env.set-shr {s'} θl s'∈ SharedVar.new n


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ nothin ⟧e)} {θr} {_} {E}
               {.(s' ⇐ e)} {.nothin} {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(rset-shared-value-old {θ} {p} {s'} e' s'∈ θs'≡old p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vset-shared-value-old {.θ} {.p} {s'} {e} {.E} {e'} {s'∈} {θs'≡old})
  with s SharedVar.≟ s'
... | yes refl =
  ⊥-elim
    (s∉can-p-θ
      (canθₛₕ-membership (Env.sig θ) 0 p Env.[]env s
        (λ θ* → canₛₕ-capture-set-shared θ* p≐E⟦pin⟧)))
... | no  s≢s'
  with ready-irr-on-irr-s/ready {θ} {e} s (Env.shr-vals {s} θ s∈) s∈ (θs≢ready θs≡old⊎θs≡new)
         e'
  where θs≢ready : typeof θs≡old⊎θs≡new → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready)
        θs≢ready (inj₁ θs≡old) θs≡ready with trans (sym θs≡old) θs≡ready
        ... | ()
        θs≢ready (inj₂ θs≡new) θs≡ready with trans (sym θs≡new) θs≡ready
        ... | ()
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ shr* →
           ρ θl · p sn⟶₁
           ρ (Θ (Env.sig θl) shr* (Env.var θl)) ·
             E ⟦ nothin ⟧e)
   (cong Env.shr
     (begin
       Env.set-shr {s'} θl s'∈Domθl SharedVar.new (δ e'')
         ≡⟨ cong (Env.set-shr {s'} θl s'∈Domθl SharedVar.new) (sym δe'≡δe'') ⟩
       Env.set-shr {s'} θl s'∈Domθl SharedVar.new (δ e')
         ≡⟨ cong (λ sig* → Θ (Env.sig θ) sig* (Env.var θ))
              (ShrMap.put-comm {_} {Env.shr θ} {_} {_}
                {SharedVar.ready ,′ θs}
                {SharedVar.new ,′ δ e'}
                s≢s') ⟩
       Env.set-shr {s} θr s∈Domθr SharedVar.ready θs
         ≡⟨ cong (Env.set-shr {s} θr s∈Domθr SharedVar.ready ∘ proj₂) (sym θrs≡θs) ⟩
       Env.set-shr {s} θr s∈Domθr SharedVar.ready
         (Env.shr-vals {s} θr s∈Domθr)                  ∎))
   (rset-shared-value-old {θl} {_} {s'} e'' s'∈Domθl
     (trans (cong proj₁ θls'≡θs') θs'≡old) p≐E⟦pin⟧) ,′
   rreadyness {θr} {_} {s} s∈Domθr
     (Data.Sum.map (trans (cong proj₁ θrs≡θs)) (trans (cong proj₁ θrs≡θs))
       θs≡old⊎θs≡new)
     (λ s∈can-E⟦nothin⟧-θr →
       s∉can-p-θ
         (canθₛₕ-subset (Env.sig θ) 0 (E ⟦ nothin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-term-nothin θ* θ* refl (tset-shr s' e) p≐E⟦pin⟧ S*)
           (λ θ* s* → canₛₕ-term-nothin θ* θ* refl (tset-shr s' e) p≐E⟦pin⟧ s*)
           s s∈can-E⟦nothin⟧-θr)))
  where
    θs = Env.shr-vals {s} θ s∈
    s∈Domθr = Env.shr-set-mono' {s} {s'} {θ} {SharedVar.new} {δ e'} {s'∈} s∈
    θrs≡θs = ShrMap.putputget {_} {Env.shr θ} {_} {_} {_} {SharedVar.new ,′ δ e'}
               s≢s' s∈ s∈Domθr refl
    s'∈Domθl = Env.shr-set-mono' {s'} {s} {θ} {SharedVar.ready} {θs} {s∈} s'∈
    θls'≡θs' = ShrMap.putputget {_} {Env.shr θ} {_} {_} {_} {SharedVar.ready ,′ θs}
                (s≢s' ∘ sym) s'∈ s'∈Domθl refl


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ nothin ⟧e)} {θr} {_} {E}
               {.(s' ⇐ e)} {.nothin} {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(rset-shared-value-new {θ} {p} {s'} e' s'∈ θs'≡new p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vset-shared-value-new {.θ} {.p} {s'} {e} {.E} {e'} {s'∈} {θs'≡new})
  with ready-maint/irr S S∈ Signal.absent e'
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ δe* →
            ρ θl · p sn⟶₁
            ρ (θl-set-shr δe*) · E ⟦ nothin ⟧e)
     (cong
       (Env.shr-vals {s'} θ s'∈ +_)
       (sym δe'≡δe''))
     (rset-shared-value-new {θl} {_} {s'} e'' s'∈ θs'≡new p≐E⟦pin⟧) ,′
   rabsence {θr} {_} {S} S∈ θS≡unknown
     (λ S∈can-E⟦nothin⟧-θr →
       S∉can-p-θ
         (canθₛ-subset (Env.sig θ) 0 (E ⟦ nothin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-term-nothin θ* θ* refl (tset-shr s' e) p≐E⟦pin⟧ S*)
           S S∈can-E⟦nothin⟧-θr)))
  where
    θl-set-shr : ℕ → Env
    θl-set-shr n = Env.set-shr {s'} θl s'∈ SharedVar.new n


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ nothin ⟧e)} {θr} {_} {E}
               {.(s' ⇐ e)} {.nothin} {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(rset-shared-value-new {θ} {p} {s'} e' s'∈ θs'≡new p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vset-shared-value-new {.θ} {.p} {s'} {e} {.E} {e'} {s'∈} {θs'≡new})
  with s SharedVar.≟ s'
... | yes refl =
  ⊥-elim
    (s∉can-p-θ
      (canθₛₕ-membership (Env.sig θ) 0 p Env.[]env s
        (λ θ* → canₛₕ-capture-set-shared θ* p≐E⟦pin⟧)))
... | no  s≢s'
  with ready-irr-on-irr-s/ready {θ} {e} s (Env.shr-vals {s} θ s∈) s∈ (θs≢ready θs≡old⊎θs≡new)
         e'
  where θs≢ready : typeof θs≡old⊎θs≡new → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready)
        θs≢ready (inj₁ θs≡old) θs≡ready with trans (sym θs≡old) θs≡ready
        ... | ()
        θs≢ready (inj₂ θs≡new) θs≡ready with trans (sym θs≡new) θs≡ready
        ... | ()
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ shr* →
           ρ θl · p sn⟶₁
           ρ (Θ (Env.sig θl) shr* (Env.var θl)) ·
             E ⟦ nothin ⟧e)
   (cong Env.shr
     (begin
       Env.set-shr {s'} θl s'∈Domθl SharedVar.new (Env.shr-vals {s'} θl s'∈Domθl + δ e'')
         ≡⟨ cong
             (λ v* → Env.set-shr {s'} θl s'∈Domθl SharedVar.new (v* + δ e''))
             (cong proj₂ θls'≡θs') ⟩
       Env.set-shr {s'} θl s'∈Domθl SharedVar.new (θs' + δ e'')
         ≡⟨ cong (λ v* → Env.set-shr {s'} θl s'∈Domθl SharedVar.new
                   (θs' + v*))
                   (sym δe'≡δe'') ⟩
       Env.set-shr {s'} θl s'∈Domθl SharedVar.new (θs' + δ e')
         ≡⟨ cong (λ sig* → Θ (Env.sig θ) sig* (Env.var θ))
              (ShrMap.put-comm {_} {Env.shr θ} {_} {_}
                {SharedVar.ready ,′ θs}
                {SharedVar.new ,′ θs' + δ e'}
                s≢s') ⟩
       Env.set-shr {s} θr s∈Domθr SharedVar.ready θs
         ≡⟨ cong (Env.set-shr {s} θr s∈Domθr SharedVar.ready ∘ proj₂) (sym θrs≡θs) ⟩
       Env.set-shr {s} θr s∈Domθr SharedVar.ready
         (Env.shr-vals {s} θr s∈Domθr)                  ∎))
   (rset-shared-value-new {θl} {_} {s'} e'' s'∈Domθl
     (trans (cong proj₁ θls'≡θs') θs'≡new) p≐E⟦pin⟧) ,′
   rreadyness {θr} {_} {s} s∈Domθr
     (Data.Sum.map (trans (cong proj₁ θrs≡θs)) (trans (cong proj₁ θrs≡θs))
       θs≡old⊎θs≡new)
     (λ s∈can-E⟦nothin⟧-θr →
       s∉can-p-θ
         (canθₛₕ-subset (Env.sig θ) 0 (E ⟦ nothin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-term-nothin θ* θ* refl (tset-shr s' e) p≐E⟦pin⟧ S*)
           (λ θ* s* → canₛₕ-term-nothin θ* θ* refl (tset-shr s' e) p≐E⟦pin⟧ s*)
           s s∈can-E⟦nothin⟧-θr)))
  where
    θs' = Env.shr-vals {s'} θ s'∈
    θs = Env.shr-vals {s} θ s∈
    s∈Domθr = Env.shr-set-mono' {s} {s'} {θ} {SharedVar.new} {θs' + δ e'} {s'∈} s∈
    θrs≡θs = ShrMap.putputget {_} {Env.shr θ} {_} {_} {_} {SharedVar.new ,′ θs' + δ e'}
               s≢s' s∈ s∈Domθr refl
    s'∈Domθl = Env.shr-set-mono' {s'} {s} {θ} {SharedVar.ready} {θs} {s∈} s'∈
    θls'≡θs' = ShrMap.putputget {_} {Env.shr θ} {_} {_} {_} {SharedVar.ready ,′ θs}
                (s≢s' ∘ sym) s'∈ s'∈Domθl refl


ρ-pot-conf-rec {p} {θ} {.p} {θl}
               {.(E ⟦ ρ (Θ SigMap.empty ShrMap.empty VarMap.[ x ↦ δ e' ]) · p' ⟧e)}
               {.θ} {_} {E}
               {.(var x ≔ e in: p')}
               {.(ρ (Θ SigMap.empty ShrMap.empty VarMap.[ x ↦ δ e' ]) · p')}
               {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(rraise-var {θ} {p} {x} {p'} {e} e' p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vraise-var {.θ} {.p} {x} {p'} {e} {.E} {e'} {.p≐E⟦pin⟧})
  with ready-maint/irr S S∈ Signal.absent e'
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ δe* →
           (ρ θl · p) sn⟶₁
           (ρ θl · E ⟦ ρ ([x,δe]-env x δe*) · p' ⟧e))
    (sym δe'≡δe'')
    (rraise-var {θl} {_} {x} {p'} {e} e'' p≐E⟦pin⟧) ,′
   rabsence {θ} {_} {S} S∈ θS≡unknown
     (λ S∈can-E⟦ρΘp'⟧-θ →
       S∉can-p-θ
         (canθₛ-subset (Env.sig θ) 0 (E ⟦ ρ [x,δe]-env x (δ e') · p' ⟧e) p Env.[]env
           (λ θ* S* → canₛ-raise θ* (tvar (δ e') x e p') p≐E⟦pin⟧ S*)
           S S∈can-E⟦ρΘp'⟧-θ)))


ρ-pot-conf-rec {p} {θ} {.p} {θl}
               {.(E ⟦ ρ (Θ SigMap.empty ShrMap.empty VarMap.[ x ↦ δ e' ]) · p' ⟧e)}
               {.θ} {_} {E}
               {.(var x ≔ e in: p')}
               {.(ρ (Θ SigMap.empty ShrMap.empty VarMap.[ x ↦ δ e' ]) · p')}
               {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(rraise-var {θ} {p} {x} {p'} {e} e' p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vraise-var {.θ} {.p} {x} {p'} {e} {.E} {e'} {.p≐E⟦pin⟧})
  with ready-irr-on-irr-s/ready {θ} {e} s (Env.shr-vals {s} θ s∈) s∈ (θs≢ready θs≡old⊎θs≡new)
         e'
  where θs≢ready : typeof θs≡old⊎θs≡new → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready)
        θs≢ready (inj₁ θs≡old) θs≡ready with trans (sym θs≡old) θs≡ready
        ... | ()
        θs≢ready (inj₂ θs≡new) θs≡ready with trans (sym θs≡new) θs≡ready
        ... | ()
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ δe* →
           (ρ θl · p) sn⟶₁
           (ρ θl · E ⟦ ρ ([x,δe]-env x δe*) · p' ⟧e))
    (sym δe'≡δe'')
    (rraise-var {θl} {_} {x} {p'} {e} e'' p≐E⟦pin⟧) ,′
   rreadyness {θ} {_} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-E⟦ρΘp'⟧-θ →
       s∉can-p-θ
         (canθₛₕ-subset (Env.sig θ) 0 (E ⟦ ρ [x,δe]-env x (δ e') · p' ⟧e) p Env.[]env
           (λ θ* S* → canₛ-raise θ* (tvar (δ e') x e p') p≐E⟦pin⟧ S*)
           (λ θ* s* → canₛₕ-raise θ* (tvar (δ e') x e p') p≐E⟦pin⟧ s*)
           s s∈can-E⟦ρΘp'⟧-θ)))


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ nothin ⟧e)} {θr}
               {_} {E} {.(x ≔ e)} {.nothin} {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(rset-var {θ} {p} {x} {e} x∈ e' p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vset-var {.θ} {.p} {x} {e} {.E} {x∈} {e'} {.p≐E⟦pin⟧})
  with ready-maint/irr S S∈ Signal.absent e'
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ δe* →
            ρ θl · p sn⟶₁
            ρ (θl-set-var δe*) · E ⟦ nothin ⟧e)
     (sym δe'≡δe'')
   (rset-var {θl} {_} {x} {e} x∈ e'' p≐E⟦pin⟧) ,′
   rabsence {θr} {_} {S} S∈ θS≡unknown
     (λ S∈can-E⟦nothin⟧-θ' →
       S∉can-p-θ
         (canθₛ-subset (Env.sig θ) 0 (E ⟦ nothin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-term-nothin θ* θ* refl (tset-var x e) p≐E⟦pin⟧ S*)
           S S∈can-E⟦nothin⟧-θ')))
  where
    θl-set-var : ℕ → Env
    θl-set-var n = Env.set-var {x} θl x∈ n


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ nothin ⟧e)} {θr}
               {_} {E} {.(x ≔ e)} {.nothin} {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(rset-var {θ} {p} {x} {e} x∈ e' p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vset-var {.θ} {.p} {x} {e} {.E} {x∈} {e'} {.p≐E⟦pin⟧})
  with ready-irr-on-irr-s/ready {θ} {e} s (Env.shr-vals {s} θ s∈) s∈ (θs≢ready θs≡old⊎θs≡new)
         e'
  where θs≢ready : typeof θs≡old⊎θs≡new → ¬ (Env.shr-stats {s} θ s∈ ≡ SharedVar.ready)
        θs≢ready (inj₁ θs≡old) θs≡ready with trans (sym θs≡old) θs≡ready
        ... | ()
        θs≢ready (inj₂ θs≡new) θs≡ready with trans (sym θs≡new) θs≡ready
        ... | ()
... | e'' , δe'≡δe'' =
  inj₂
  (_ , _ ,
   subst (λ δe* →
            ρ θl · p sn⟶₁
            ρ (θl-set-var δe*) · E ⟦ nothin ⟧e)
     (sym δe'≡δe'')
   (rset-var {θl} {_} {x} {e} x∈ e'' p≐E⟦pin⟧) ,′
   rreadyness {θr} {_} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-E⟦nothin⟧-θ' →
       s∉can-p-θ
         (canθₛₕ-subset (Env.sig θ) 0 (E ⟦ nothin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-term-nothin θ* θ* refl (tset-var x e) p≐E⟦pin⟧ S*)
           (λ θ* s* → canₛₕ-term-nothin θ* θ* refl (tset-var x e) p≐E⟦pin⟧ s*)
           s s∈can-E⟦nothin⟧-θ')))
  where
    θl-set-var : ℕ → Env
    θl-set-var n = Env.set-var {x} θl x∈ n


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ qin ⟧e)} {.θ} {_} {E}
               {.(if x ∣⇒ th ∣⇒ qin)} {qin} {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(rif-false {x = x} x∈ θx≡zero p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vif-false {.θ} {.p} {th} {.qin} {x} {.E} {x∈} {θx≡zero} {.p≐E⟦pin⟧}) =
  inj₂
  (_ , _ ,
   rif-false {x = x} x∈ θx≡zero p≐E⟦pin⟧ ,′
   rabsence {θ} {_} {S} S∈ θS≡unknown
     (λ S∈can-E⟦qin⟧ →
       S∉can-p-θ
         (canθₛ-subset (Env.sig θ) 0 (E ⟦ qin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-if-false θ* p≐E⟦pin⟧ S*)
           S S∈can-E⟦qin⟧)))

ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ qin ⟧e)} {.θ} {_} {E}
               {.(if x ∣⇒ th ∣⇒ qin)} {qin} {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(rif-false {x = x} x∈ θx≡zero p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vif-false {.θ} {.p} {th} {.qin} {x} {.E} {x∈} {θx≡zero} {.p≐E⟦pin⟧}) =
  inj₂
  (_ , _ ,
   rif-false {x = x} x∈ θx≡zero p≐E⟦pin⟧ ,′
   rreadyness {θ} {_} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-E⟦qin⟧ →
       s∉can-p-θ
        (canθₛₕ-subset (Env.sig θ) 0 (E ⟦ qin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-if-false θ* p≐E⟦pin⟧ S*)
           (λ θ* s* → canₛₕ-if-false θ* p≐E⟦pin⟧ s*)
           s s∈can-E⟦qin⟧)))


ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ qin ⟧e)} {.θ} {_} {E}
               {.(if x ∣⇒ qin ∣⇒ els)} {qin} {_} {_}
               {.(rabsence {θ} {p} {S} S∈ θS≡unknown S∉can-p-θ)}
               {.(rif-true {x = x} {E} {n} x∈ θx≡suc p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vabsence S S∈ θS≡unknown S∉can-p-θ)
               (vif-true {.θ} {.p} {.qin} {els} {x} {.E} {n} {x∈} {θx≡suc} {.p≐E⟦pin⟧}) =
  inj₂
  (_ , _ ,
   rif-true {x = x} x∈ θx≡suc p≐E⟦pin⟧ ,′
   rabsence {θ} {_} {S} S∈ θS≡unknown
     (λ S∈can-E⟦qin⟧ →
       S∉can-p-θ
         (canθₛ-subset (Env.sig θ) 0 (E ⟦ qin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-if-true θ* p≐E⟦pin⟧ S*)
           S  S∈can-E⟦qin⟧)))

ρ-pot-conf-rec {p} {θ} {.p} {θl} {.(E ⟦ qin ⟧e)} {.θ} {_} {E}
               {.(if x ∣⇒ qin ∣⇒ els)} {qin} {_} {_}
               {.(rreadyness {θ} {p} {s} s∈ θs≡old⊎θs≡new s∉can-p-θ)}
               {.(rif-true {x = x} {E} {n} x∈ θx≡suc p≐E⟦pin⟧)}
               {p≐E⟦pin⟧} {qr≐E⟦qin⟧} (CBρ cbp)
               (vreadyness s s∈ θs≡old⊎θs≡new s∉can-p-θ)
               (vif-true {.θ} {.p} {.qin} {els} {x} {.E} {n} {x∈} {θx≡suc} {.p≐E⟦pin⟧}) =
  inj₂
  (_ , _ ,
   rif-true {x = x} x∈ θx≡suc p≐E⟦pin⟧ ,′
   rreadyness {θ} {_} {s} s∈ θs≡old⊎θs≡new
     (λ s∈can-E⟦qin⟧ →
       s∉can-p-θ
         (canθₛₕ-subset (Env.sig θ) 0 (E ⟦ qin ⟧e) p Env.[]env
           (λ θ* S* → canₛ-if-true θ* p≐E⟦pin⟧ S*)
           (λ θ* s* → canₛₕ-if-true θ* p≐E⟦pin⟧ s*)
           s s∈can-E⟦qin⟧)))
