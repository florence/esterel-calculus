module _ where

open import Data.Nat using (_+_)
open import Data.Nat.Properties.Simple using ( +-comm ; +-assoc)
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
open import Data.Maybe using ( just )
open import Function using (_$_)

open import Data.FiniteMap
import Data.OrderedListMap as OMap
open import Data.Nat as Nat using (ℕ)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar

open import sn-calculus-confluence.helper
open import sn-calculus-confluence.rec
open import sn-calculus-confluence.potrec
open import sn-calculus-confluence.potpot

ρ-conf : ∀{p FV BV ql qr θ qi A} → CorrectBinding p FV BV → p sn⟶₁ ql → p sn⟶₁ qr → p ≡ (ρ⟨ θ , A ⟩· qi)
         → ql ≡ qr
         ⊎ (∃ (λ o → ql sn⟶₁ o × qr sn⟶₁ o))
         ⊎ ql sn⟶₁ qr
         ⊎ qr sn⟶₁ ql
ρ-conf {(ρ⟨ θ , .A ⟩· qi)}{ql = ql}{qr = qr}{A = A} cb redl redr refl with ρ-stays-ρ-sn⟶₁ redl | ρ-stays-ρ-sn⟶₁ redr
... | (θl , qlin , Al , refl) | (θr , qrin , Ar , refl) with get-view redl | get-view redr
ρ-conf {(ρ⟨ θ , .A ⟩· qi)}{ql = ql}{qr = qr}{A = A} cb redl redr refl | (θl , qlin , Al , refl) | (θr , qrin , Ar , refl) | inj₁ (_ , _ , _ , _ , _ , viewl) | inj₁ (_ , _ , _ , _ , _ , viewr)
   with E-view-main-bind viewl viewr
... | inj₁ (e= , q= , θ= , A=) rewrite e= | q= | θ= | A= = inj₁ refl
... | inj₂ ~a with ρ-conf-rec cb _ _ ~a redl redr _ _ viewl viewr
... | (θo , Ao , so , _ , _ , _ , _ , _ , _ , redol , redor , _) = inj₂ $ inj₁ ((ρ⟨ θo , Ao ⟩· so) , redol , redor)
ρ-conf {(ρ⟨ θ  , .A ⟩· qi)}{ql = ql}{qr = qr}{A = A} cb redl redr refl | (θl , qlin , Al , refl) | (θr , qrin , Ar , refl) | inj₁ (_ , _ , _ , _ , _ , viewl) | inj₂ (_ , _ , viewr)
  with ρ-pot-conf-rec cb viewr viewl
... | inj₁ redo = inj₂ (inj₂ (inj₂ redo))
... | inj₂ (s , env , Ao , redol , redor) = inj₂ $ inj₁ (ρ⟨ env , Ao ⟩· s , redor , redol)
ρ-conf {(ρ⟨ θ  , .A ⟩· qi)}{ql = ql}{qr = qr}{A = A} cb redl redr refl | (θl , qlin , Al , refl) | (θr , qrin , Ar , refl) | inj₂ (_ , _ , viewl) | inj₁ (_ , _ , _ , _ , _ , viewr)
    with ρ-pot-conf-rec cb viewl viewr
... | inj₁ redo = inj₂ (inj₂ (inj₁ redo))
... | inj₂ (s , env , Ao , redol , redor) = inj₂ $ inj₁ ((ρ⟨ env , Ao ⟩· s) , redol , redor)
ρ-conf {(ρ⟨ θ  , .A ⟩· qi)}{ql = ql}{qr = qr}{A = A} cb redl redr refl | (θl , qlin , Al , refl) | (θr , qrin , Ar , refl) | inj₂ (_ , _ , viewl) | inj₂ (_ , _ , viewr)
    with pot-pot-conf-rec viewl viewr
... | inj₁ eq = inj₁ eq
... | inj₂ (env , redol , redor) = inj₂ $ inj₁ (ρ⟨ env , A ⟩· qi , redol , redor)

R-confluent : ∀{p q r BV FV} → CorrectBinding p BV FV → p sn⟶₁ q → p sn⟶₁ r
                                   → q ≡ r
                                   ⊎ (∃ (λ s → q sn⟶₁ s × r sn⟶₁ s))
                                   ⊎ q sn⟶₁ r
                                   ⊎ r sn⟶₁ q
R-confluent {.(_ ∥ _)} cb (rpar-done-right p'' q'') (rpar-done-right p' q') = inj₁ ( value-max-unique{d1 = (dhalted p'')}{d2 = q''}{d3 = (dhalted p')}{d4 = q'} )
R-confluent {.(_ ∥ _)} cb (rpar-done-right p'' q'') (rpar-done-left p' q') = inj₁ ( value-max-unique{d1 = (dhalted p'')}{d2 = q''}{d3 = p'}{d4 = (dhalted q')} )
R-confluent {.(_ ∥ _)} cb (rpar-done-left p'' q'') (rpar-done-right p' q') = inj₁ (value-max-unique{d1 = (p'')}{d2 =(dhalted q'')}{d3 = (dhalted p')}{d4 = (q')})
R-confluent {.(_ ∥ _)} cb (rpar-done-left p'' q'') (rpar-done-left p' q') = inj₁ (value-max-unique{d1 = p''}{d2 = (dhalted q'')}{d3 = p'}{d4 = (dhalted q')})
R-confluent {.(loop _)} cb rloop-unroll rloop-unroll = inj₁ refl
R-confluent {.(nothin >> _)} cb rseq-done rseq-done = inj₁ refl
R-confluent {.(exit _ >> _)} cb rseq-exit rseq-exit = inj₁ refl
R-confluent {.(loopˢ (exit _) _)} cb rloopˢ-exit rloopˢ-exit = inj₁ refl
R-confluent {.(suspend nothin _)} cb (rsuspend-done hnothin) (rsuspend-done hnothin) = inj₁ refl
R-confluent {.(suspend (exit n) _)} cb (rsuspend-done (hexit n)) (rsuspend-done (hexit .n)) = inj₁ refl
R-confluent {.(trap nothin)} cb (rtrap-done hnothin) (rtrap-done hnothin) = inj₁ refl
R-confluent {.(trap (exit n))} cb (rtrap-done (hexit n)) (rtrap-done (hexit .n)) = inj₁ refl
R-confluent {.(signl _ _)} cb rraise-signal rraise-signal = inj₁ refl
R-confluent {p@(ρ⟨ _ , _ ⟩· _)} cb redl redr = ρ-conf cb redl redr refl
