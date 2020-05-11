module Esterel.Lang where

open import Esterel.Environment as Env
  using (Env)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)

open import Data.List
  using (List)
open import Data.Nat as Nat
  using (ℕ)

data s/l : Set where
  num : ℕ → s/l
  seq-ref : (x : SeqVar) → s/l
  shr-ref : (s : SharedVar) → s/l

data Expr : Set where
  plus : List s/l → Expr

data Term : Set where
  nothin         : Term
  pause          : Term
  signl          : (S : Signal) → (p : Term) → Term
  present_∣⇒_∣⇒_ : (S : Signal) → (p : Term) → (q : Term) → Term
  emit           : (S : Signal) → Term
  _∥_            : (p : Term) → (q : Term) → Term
  loop           : (p : Term) → Term
  loopˢ          : (p : Term) → (q : Term) → Term
  _>>_           : (p : Term) → (q : Term) → Term
  suspend        : (p : Term) → (S : Signal) → Term
  trap           : (p : Term) → Term
  exit           : ℕ → Term
  shared_≔_in:_  : (s : SharedVar) → (e : Expr) → (p : Term) → Term
  _⇐_            : (s : SharedVar) → (e : Expr) → Term
  var_≔_in:_     : (x : SeqVar) → (e : Expr) → (p : Term) → Term
  _≔_            : (x : SeqVar) → (e : Expr) → Term
  if_∣⇒_∣⇒_      : (x : SeqVar) → (p : Term) → (q : Term) → Term
  ρ_·_           : (θ : Env) → (p : Term) → Term

infix  20 _⇐_
infix  20 _≔_
infix  17 if_∣⇒_∣⇒_
infixr 15 _>>_
infixr 13 _∥_
infix  11 present_∣⇒_∣⇒_
infix  10 shared_≔_in:_
infix  10 var_≔_in:_
infix   6 ρ_·_
