module _ where

{- NOTE: To run move to adga directory or figure out how `agda -I` works -}

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
import Relation.Binary.PropositionalEquality as Prop
open import Data.Empty
open import calculus
open import context-properties
open import Esterel.Lang.Binding
open import Data.Maybe using (just ; nothing)
open import Esterel.Variable.Signal as Signal using (Signal ; _ₛ)
open import Esterel.Variable.Sequential as SeqVar using (SeqVar ; _ᵥ)
open import Esterel.Variable.Shared as ShVar using (SharedVar ; _ₛₕ)
open import Data.List.Any

S : Signal
S = 0 ₛ

start : Term
start = signl S ((emit S) >> (present S ∣⇒ pause ∣⇒ nothin))
step1 = ρ (Θ [ (just Signal.unknown) ] [] []) · ((emit S) >> (present S ∣⇒ pause ∣⇒ nothin))
step2 = ρ (Θ [ (just Signal.present) ] [] []) · (nothin >> (present S ∣⇒ pause ∣⇒ nothin))
step3 = ρ (Θ [ (just Signal.present) ] [] []) · (present S ∣⇒ pause ∣⇒ nothin)
end : Term
end   = ρ (Θ [ (just Signal.present) ] [] []) · pause

red : start ⟶* end
red = rstep{start}{step1}
          (⟶-inclusion (rraise-signal{((emit S) >> (present S ∣⇒ pause ∣⇒ nothin))}{S}) )
          (rstep {step1} {step2}
                 (⟶-inclusion (remit (Data.List.Any.Any.here Prop.refl)
                                      (deseq{p = (emit S)}{q = (present S ∣⇒ pause ∣⇒ nothin)} (dehole{emit S}))))
                 (rstep {step2} {step3}
                        (rcontext (cenv (Θ (just Signal.present ∷ []) [] []) ∷ [])
                           (dcenv dchole) rseq-done)
                        (rstep {step3} {end}
                        (rcontext [] dchole
                                    (ris-present (Data.List.Any.Any.here Prop.refl) Prop.refl dehole)) rrefl)))
