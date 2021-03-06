module sn-calculus where

open import utility

open import Esterel.Lang
open import Esterel.Lang.Binding
open import Esterel.Lang.Properties
open import Esterel.Lang.CanFunction
  using (Canθₛ ; Canθₛₕ ; [S]-env)
open import Esterel.Environment as Env
  using (Env ; Θ ; _←_ ; sig ; []env ; module SigMap ; module ShrMap ; module VarMap)
open import Esterel.Context
  using (EvaluationContext ; EvaluationContext1 ; _⟦_⟧e ; _≐_⟦_⟧e ;
         Context ; Context1 ; _⟦_⟧c ; _≐_⟦_⟧c)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar
  using (SeqVar)
open import Esterel.Context.Properties

open import Relation.Nullary
  using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; sym)
open import Data.Empty
  using (⊥ ; ⊥-elim)
import Data.FiniteMap
open import Data.List
  using (List ; _∷_ ; [])
open import Data.List.All as All
  using (All ; _∷_ ; [])
open import Data.Nat
  using (ℕ ; zero ; suc ; _+_)
open import Data.Product
  using (Σ-syntax ; Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; _,′_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)

open _≐_⟦_⟧e
open _≐_⟦_⟧c

open EvaluationContext1
open Context1

infix 4 _sn⟶₁_
infix 4 _sn⟶_
infix 4 _sn⟶*_

-- The environment created by rraise-signal rule
-- [S]-env, is defined in Esterel.Lang.CanFunction
-- It's simply Θ SigMap.[ S ↦ Signal.unknown ] ShrMap.empty VarMap.empty

-- The environment created by rraise-shared rule
[s,δe]-env : (s : SharedVar) → (v : ℕ) → Env
[s,δe]-env s δe' =
  Θ SigMap.empty
    ShrMap.[ s ↦ (SharedVar.old ,′ δe') ]
    VarMap.empty

-- The environment created by rraise-var rule
[x,δe]-env : (x : SeqVar) → (v : ℕ) → Env
[x,δe]-env x δe' =
  Θ SigMap.empty ShrMap.empty VarMap.[ x ↦ δe' ]

[s,δe-new]-env : (s : SharedVar) → (v : ℕ) → Env
[s,δe-new]-env s δe' =
  Θ SigMap.empty
    ShrMap.[ s ↦ (SharedVar.new ,′ δe') ]
    VarMap.empty



data bound-ready : Env → s/l → Set where
  brnum : ∀{θ n} → bound-ready θ (num n)
  brseq : ∀{θ x} → (Env.isVar∈ x θ) → bound-ready θ (seq-ref x)
  brshr : ∀{θ s} →
    (s∈ : (Env.isShr∈ s θ)) →
    Env.shr-stats{s} θ s∈ ≡ SharedVar.ready →
    bound-ready θ (shr-ref s)

data all-ready : Expr → Env → Set where
  aplus : ∀{θ operators} → All (bound-ready θ) operators → all-ready (plus operators) θ

δ : ∀{e θ} → all-ready e θ → ℕ
δ {(plus [])}              {θ} (aplus [])                 = 0
δ {(plus (num n     ∷ _))} {θ} (aplus (brnum      ∷ ops)) = n + δ (aplus ops)
δ {(plus (seq-ref x ∷ _))} {θ} (aplus (brseq x∈   ∷ ops)) = Env.var-vals{x} θ x∈ + δ (aplus ops)
δ {(plus (shr-ref s ∷ _))} {θ} (aplus (brshr s∈ _ ∷ ops)) = Env.shr-vals{s} θ s∈ + δ (aplus ops)

δ-e-irr : ∀{e θ} →  (e' : all-ready e θ) → (e'' : all-ready e θ) → δ e' ≡ δ e''
δ-e-irr {plus []} (aplus []) (aplus []) = refl
δ-e-irr {plus ((num n) ∷ x₁)} (aplus (brnum ∷ x₂)) (aplus (brnum ∷ x₃))
   = cong (_+_ n)  (δ-e-irr (aplus x₂) (aplus x₃))
δ-e-irr {plus ((seq-ref x) ∷ x₁)}{θ} (aplus (brseq x₂ ∷ x₃)) (aplus (brseq x₄ ∷ x₅))
  with Env.var-vals-∈-irr{x}{θ} x₂ x₄
... | k rewrite sym k =  (cong (_+_ (Env.var-vals{x} θ x₂)) (δ-e-irr (aplus x₃) (aplus x₅)))
δ-e-irr {plus ((shr-ref s) ∷ x₁)}{θ} (aplus (brshr s∈ x ∷ x₂)) (aplus (brshr s∈₁ x₃ ∷ x₄))
   with Env.shr-vals-∈-irr{s}{θ} s∈ s∈₁
... | k rewrite sym k = cong (_+_ (Env.shr-vals{s} θ s∈)) (δ-e-irr (aplus x₂) (aplus x₄))


{-
  In the current formalization, for reduction rules involving evaluation
  contexts, we will write them in the following form to enable pattern
  matching on p:

  (r ≐ E ⟦ p ⟧e) → (something r sn⟶₁ something E ⟦ p'⟧)
-}

{- this relation is the strongly normalizing subset of
   the calculus. It is just like _⟶₁_ in calculus.agda,
   but without the [par-swap] constructor. -}

data _sn⟶₁_ : Term → Term → Set where
  rpar-done-right : ∀{p q} →
    (p' : halted p) →
    (q' : done q) →
    (p ∥ q) sn⟶₁ (value-max (dhalted p') q' (inj₁ p'))

  rpar-done-left : ∀{p q} →
    (p' : done p) →
    (q' : halted q) →
    (p ∥ q) sn⟶₁ (value-max p' (dhalted q') (inj₂ q'))

  ris-present : ∀{θ S r p q E A} →
    (S∈ : (Env.isSig∈ S θ)) →
    Env.sig-stats{S} θ S∈ ≡ Signal.present →
    r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e →
    (ρ⟨ θ , A ⟩· r) sn⟶₁ (ρ⟨ θ , A ⟩· E ⟦ p ⟧e)

  ris-absent : ∀{θ S r p q E A} →
    (S∈ : (Env.isSig∈ S θ)) →
    Env.sig-stats{S} θ S∈ ≡ Signal.absent →
    r ≐ E ⟦ present S ∣⇒ p ∣⇒ q ⟧e →
    (ρ⟨ θ , A ⟩· r) sn⟶₁ (ρ⟨ θ , A ⟩· E ⟦ q ⟧e)

  remit : ∀{θ r S E} →
    (S∈ : (Env.isSig∈ S θ)) →
    (¬S≡a : ¬ (Env.sig-stats{S} θ S∈) ≡ Signal.absent) →
    r ≐ E ⟦ emit S ⟧e →
    (ρ⟨ θ , GO ⟩· r) sn⟶₁
    (ρ⟨ (Env.set-sig{S} θ S∈ Signal.present) , GO ⟩·
      E ⟦ nothin ⟧e)

  rloop-unroll : ∀{p} →
    (loop p)
    sn⟶₁
    (loopˢ p p)

  rseq-done : ∀{q} →
    (nothin >> q) sn⟶₁ q

  rseq-exit : ∀{q n} →
    (exit n >> q) sn⟶₁ (exit n)

  rloopˢ-exit : ∀{q n} →
    (loopˢ (exit n) q) sn⟶₁ (exit n)

  rsuspend-done : ∀{p S} →
    halted p →
    (suspend p S) sn⟶₁ p

  -- traps
  rtrap-done : ∀{p} →
    (p' : halted p) →
    (trap p) sn⟶₁ (↓ p')

  -- lifting signals
  rraise-signal : ∀{p S} →
    (signl S p) sn⟶₁
    (ρ⟨ (Θ SigMap.[ S ↦ Signal.unknown ] ShrMap.empty VarMap.empty) , WAIT ⟩·
      p)

  -- shared state
  rraise-shared : ∀{θ r s e p E A} →
    (e' : all-ready e θ) →
    r ≐ E ⟦ shared s ≔ e in: p ⟧e →
    (ρ⟨ θ , A ⟩· r) sn⟶₁
    (ρ⟨ θ , A ⟩·
      E ⟦ (ρ⟨ [s,δe]-env s (δ e') , WAIT ⟩· p) ⟧e)

  rset-shared-value-old : ∀{θ r s e E} →
    (e' : all-ready e θ) →
    (s∈ : (Env.isShr∈ s θ)) →
    Env.shr-stats{s} θ s∈ ≡ SharedVar.old →
    r ≐ E ⟦ s ⇐ e ⟧e →
    (ρ⟨ θ , GO ⟩· r) sn⟶₁
    (ρ⟨ (Env.set-shr{s} θ s∈ (SharedVar.new) (δ e')) , GO ⟩·
      E ⟦ nothin ⟧e)

  rset-shared-value-new : ∀{θ r s e E} →
    (e' : all-ready e θ) →
    (s∈ : (Env.isShr∈ s θ)) →
    Env.shr-stats{s} θ s∈ ≡ SharedVar.new →
    r ≐ E ⟦ s ⇐ e ⟧e →
    (ρ⟨ θ , GO ⟩· r) sn⟶₁
    (ρ⟨ (Env.set-shr{s} θ s∈ (SharedVar.new) (Env.shr-vals{s} θ s∈ + δ e')) , GO ⟩·
      E ⟦ nothin ⟧e)

  -- unshared state
  rraise-var : ∀{θ r x p e E A} →
    (e' : all-ready e θ) →
    r ≐ E ⟦ var x ≔ e in: p ⟧e →
    (ρ⟨ θ , A ⟩· r) sn⟶₁
    (ρ⟨ θ , A ⟩·
      E ⟦ (ρ⟨ [x,δe]-env x (δ e') , WAIT ⟩· p) ⟧e)

  rset-var : ∀{θ r x e E A} →
    (x∈ : (Env.isVar∈ x θ)) →
    (e' : all-ready e θ) →
    r ≐ E ⟦ x ≔ e ⟧e →
    (ρ⟨ θ , A ⟩· r) sn⟶₁
    (ρ⟨ (Env.set-var{x} θ x∈ (δ e')) , A ⟩·
      E ⟦ nothin ⟧e)

  -- if
  rif-false : ∀{θ r p q x E A} →
    (x∈ : (Env.isVar∈ x θ)) →
    Env.var-vals{x} θ x∈ ≡ zero →
    r ≐ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e →
    (ρ⟨ θ , A ⟩· r) sn⟶₁ (ρ⟨ θ , A ⟩· E ⟦ q ⟧e)

  rif-true : ∀{θ r p q x E n A} →
    (x∈ : (Env.isVar∈ x θ)) →
    Env.var-vals{x} θ x∈ ≡ suc n →
    r ≐ E ⟦ if x ∣⇒ p ∣⇒ q ⟧e →
    (ρ⟨ θ , A ⟩· r) sn⟶₁ (ρ⟨ θ , A ⟩· E ⟦ p ⟧e)

  -- progression
  {-
    Thoughts:
    * These two rules are expressed differently to the definition in model/shared.rkt
      for simplicity. Instead of being more 'computative', the definition here is
      more 'declarative'. Keep an eye on the original definition to make sure that
      they are equivalent.
  -}
  rabsence : ∀{θ p S A} →
    (S∈ : (Env.isSig∈ S θ)) →
    Env.sig-stats{S} θ S∈ ≡ Signal.unknown →
    (Signal.unwrap S) ∉ Canθₛ (sig θ) 0 p []env →
    (ρ⟨ θ , A ⟩· p) sn⟶₁
    (ρ⟨ (Env.set-sig{S} θ S∈ (Signal.absent)) , A ⟩·
      p)

  rreadyness : ∀{θ p s A} →
    (s∈ : (Env.isShr∈ s θ)) →
    (Env.shr-stats{s} θ s∈ ≡ SharedVar.old) ⊎ (Env.shr-stats{s} θ s∈ ≡ SharedVar.new) →
    (SharedVar.unwrap s) ∉ Canθₛₕ (sig θ) 0 p []env →
    (ρ⟨ θ , A ⟩· p) sn⟶₁
    (ρ⟨ (Env.set-shr{s} θ s∈ (SharedVar.ready) (Env.shr-vals{s} θ s∈)) , A ⟩·
      p)

  rmerge : ∀{θ₁ θ₂ r p E A₁ A₂} →
    r ≐ E ⟦ ρ⟨ θ₂ , A₂ ⟩· p ⟧e →
    (ρ⟨ θ₁ , A₁ ⟩· r) sn⟶₁ (ρ⟨ (θ₁ ← θ₂) , (A-max A₁ A₂) ⟩· E ⟦ p ⟧e)

-- The compatible closure of _sn⟶₁_.
data _sn⟶_ : Term → Term → Set where
  rcontext : ∀{r p p'} →
    (C : Context) →
    (dc : r ≐ C ⟦ p ⟧c) →
    (psn⟶₁p' : p sn⟶₁ p') →
    r sn⟶ (C ⟦ p' ⟧c)

sn⟶-inclusion : ∀{p q} → p sn⟶₁ q → p sn⟶ q
sn⟶-inclusion psn⟶₁q = rcontext [] dchole psn⟶₁q

data _sn⟶*_ : Term → Term → Set where
  rrefl : ∀{p} → (p sn⟶* p)
  rstep : ∀{p q r} → (psn⟶q : p sn⟶ q) → (qsn⟶*r : q sn⟶* r) → (p sn⟶* r)

sn⟶*-inclusion : ∀{p q} → p sn⟶ q → p sn⟶* q
sn⟶*-inclusion psn⟶q = rstep psn⟶q rrefl

data _sn≡ₑ_ : Term → Term → Set where
  rstp : ∀{p q} → (psn⟶q : p sn⟶ q) → p sn≡ₑ q
  rsym : ∀{p q BV FV} → (psn≡ₑq : p sn≡ₑ q) → (CBp : CorrectBinding p BV FV) → q sn≡ₑ p
  rref : ∀{p} → p sn≡ₑ p
  rtrn : ∀{p q r} → (psn≡ₑr : p sn≡ₑ r) → (rsn≡ₑq : r sn≡ₑ q) → p sn≡ₑ q

-- rstep, reversed: walk many steps first then walk one step
rpets : ∀ {p q r} → p sn⟶* q → q sn⟶ r → p sn⟶* r
rpets rrefl qsn⟶r = sn⟶*-inclusion qsn⟶r
rpets (rstep psn⟶s ssn⟶*q) qsn⟶r = rstep psn⟶s (rpets ssn⟶*q qsn⟶r)

{-
Properties relating halted, paused, done programs and the reduction relation.
* Halted, paused and done programs do not reduce under the original reduction relation _sn⟶₁_.
    halted-¬sn⟶₁ : ∀{p p'} → halted p → ¬ p sn⟶₁ p'
    paused-¬sn⟶₁ : ∀{p p'} → paused p → ¬ p sn⟶₁ p'
    done-¬sn⟶₁ : ∀{p p'} → done p → ¬ p sn⟶₁ p'
* Halted programs do not reduce under the compatible closure relation _sn⟶_.
    halted-¬sn⟶ : ∀{p p'} → halted p → ¬ p sn⟶ p'
* Paused programs remain paused under the compatible closure relation _sn⟶_.
    paused-sn⟶ : ∀{p p'} → paused p → p sn⟶ p' → paused p'
-}
halted-¬sn⟶₁ : ∀{p p'} → halted p → ¬ p sn⟶₁ p'
halted-¬sn⟶₁ hnothin ()
halted-¬sn⟶₁ (hexit n) ()

paused-¬sn⟶₁ : ∀{p p'} → paused p → ¬ p sn⟶₁ p'
paused-¬sn⟶₁ ppause ()
paused-¬sn⟶₁ (pseq ()) rseq-done
paused-¬sn⟶₁ (pseq ()) rseq-exit
paused-¬sn⟶₁ (ploopˢ ppause) ()
paused-¬sn⟶₁ (ploopˢ (pseq a)) ()
paused-¬sn⟶₁ (ploopˢ (ppar a a₁)) ()
paused-¬sn⟶₁ (ploopˢ (psuspend a)) ()
paused-¬sn⟶₁ (ploopˢ (ptrap a)) ()
paused-¬sn⟶₁ (ploopˢ (ploopˢ a)) ()
paused-¬sn⟶₁ (ppar paused₁ paused₂) (rpar-done-right p' q') =
  halted-paused-disjoint p' paused₁
paused-¬sn⟶₁ (ppar paused₁ paused₂) (rpar-done-left p' q') =
  halted-paused-disjoint q' paused₂
paused-¬sn⟶₁ (psuspend paused) (rsuspend-done halted) =
  halted-paused-disjoint halted paused
paused-¬sn⟶₁ (ptrap paused) (rtrap-done halted) =
  halted-paused-disjoint halted paused

done-¬sn⟶₁ : ∀{p p'} → done p → ¬ p sn⟶₁ p'
done-¬sn⟶₁ (dhalted halted) psn⟶₁p' = halted-¬sn⟶₁ halted psn⟶₁p'
done-¬sn⟶₁ (dpaused paused) psn⟶₁p' = paused-¬sn⟶₁ paused psn⟶₁p'

halted-¬sn⟶ : ∀{p p'} → halted p → ¬ p sn⟶ p'
halted-¬sn⟶ halted (rcontext C dc psn⟶₁p') =
  halted-¬sn⟶₁ (halted-⟦⟧c halted dc) psn⟶₁p'

paused-sn⟶ : ∀{p p'} → paused p → p sn⟶ p' → paused p'
paused-sn⟶ ppause                 (rcontext _ dchole psn⟶₁p') =
  ⊥-elim (paused-¬sn⟶₁ ppause psn⟶₁p')
paused-sn⟶ (pseq paused)          (rcontext _ dchole psn⟶₁p') =
  ⊥-elim (paused-¬sn⟶₁ (pseq paused) psn⟶₁p')
paused-sn⟶ (ppar paused₁ paused₂) (rcontext _ dchole psn⟶₁p') =
  ⊥-elim (paused-¬sn⟶₁ (ppar paused₁ paused₂) psn⟶₁p')
paused-sn⟶ (psuspend paused)      (rcontext _ dchole psn⟶₁p') =
  ⊥-elim (paused-¬sn⟶₁ (psuspend paused) psn⟶₁p')
paused-sn⟶ (ptrap paused)         (rcontext _ dchole psn⟶₁p') =
  ⊥-elim (paused-¬sn⟶₁ (ptrap paused) psn⟶₁p')
paused-sn⟶ (ploopˢ paused)          (rcontext _ dchole psn⟶₁p') =
  ⊥-elim (paused-¬sn⟶₁ (ploopˢ paused) psn⟶₁p')
paused-sn⟶ (ploopˢ paused)          (rcontext _ (dcloopˢ₁ dc) psn⟶₁p') =
  ploopˢ (paused-sn⟶ paused (rcontext _ dc psn⟶₁p'))
paused-sn⟶ (ploopˢ paused)          (rcontext _ (dcloopˢ₂ dc) psn⟶₁p') =
  ploopˢ paused
paused-sn⟶ (pseq paused)          (rcontext _ (dcseq₁ dc) psn⟶₁p') =
  pseq (paused-sn⟶ paused (rcontext _ dc psn⟶₁p'))
paused-sn⟶ (pseq paused)          (rcontext _ (dcseq₂ dc) psn⟶₁p') =
  pseq paused
paused-sn⟶ (ppar paused₁ paused₂) (rcontext _ (dcpar₁ dc) psn⟶₁p') =
  ppar (paused-sn⟶ paused₁ (rcontext _ dc psn⟶₁p')) paused₂
paused-sn⟶ (ppar paused₁ paused₂) (rcontext _ (dcpar₂ dc) psn⟶₁p') =
  ppar paused₁ (paused-sn⟶ paused₂ (rcontext _ dc psn⟶₁p'))
paused-sn⟶ (psuspend paused)      (rcontext _ (dcsuspend dc) psn⟶₁p') =
  psuspend (paused-sn⟶ paused (rcontext _ dc psn⟶₁p'))
paused-sn⟶ (ptrap paused)         (rcontext _ (dctrap dc) psn⟶₁p') =
  ptrap (paused-sn⟶ paused (rcontext _ dc psn⟶₁p'))

done-sn⟶ : ∀{p q} → done p → p sn⟶ q → done q
done-sn⟶ (dhalted p/halted) psn⟶q = ⊥-elim (halted-¬sn⟶ p/halted psn⟶q)
done-sn⟶ (dpaused p/paused) psn⟶q = dpaused (paused-sn⟶ p/paused psn⟶q)

Context1-sn⟶ : ∀{p p'} → (C1 : Context1) → p sn⟶ p' → (C1 ∷ []) ⟦ p ⟧c sn⟶ (C1 ∷ []) ⟦ p' ⟧c
Context1-sn⟶ (ceval (epar₁ q)) (rcontext C dc psn⟶₁p') =
  rcontext (ceval (epar₁ q) ∷ C) (dcpar₁ dc) psn⟶₁p'
Context1-sn⟶ (ceval (epar₂ p₁)) (rcontext C dc psn⟶₁p') =
  rcontext (ceval (epar₂ p₁) ∷ C) (dcpar₂ dc) psn⟶₁p'
Context1-sn⟶ (ceval (eseq q)) (rcontext C dc psn⟶₁p') =
  rcontext (ceval (eseq q) ∷ C) (dcseq₁ dc) psn⟶₁p'
Context1-sn⟶ (ceval (eloopˢ q)) (rcontext C dc psn⟶₁p') =
  rcontext (ceval (eloopˢ q) ∷ C) (dcloopˢ₁ dc) psn⟶₁p'
Context1-sn⟶ (ceval (esuspend S)) (rcontext C dc psn⟶₁p') =
  rcontext (ceval (esuspend S) ∷ C) (dcsuspend dc) psn⟶₁p'
Context1-sn⟶ (ceval etrap) (rcontext C dc psn⟶₁p') =
  rcontext (ceval etrap ∷ C) (dctrap dc) psn⟶₁p'
Context1-sn⟶ (csignl S) (rcontext C dc psn⟶₁p') =
  rcontext (csignl S ∷ C) (dcsignl dc) psn⟶₁p'
Context1-sn⟶ (cpresent₁ S q)(rcontext C dc psn⟶₁p') =
  rcontext (cpresent₁ S q ∷ C) (dcpresent₁ dc) psn⟶₁p'
Context1-sn⟶ (cpresent₂ S p') (rcontext C dc psn⟶₁p') =
  rcontext (cpresent₂ S p' ∷ C) (dcpresent₂ dc) psn⟶₁p'
Context1-sn⟶ (cloop) (rcontext C dc psn⟶₁p') =
  rcontext (cloop ∷ C) (dcloop dc) psn⟶₁p'
Context1-sn⟶ (cloopˢ₂ p) (rcontext C dc psn⟶₁p') =
  rcontext (cloopˢ₂ p ∷ C) (dcloopˢ₂ dc) psn⟶₁p'
Context1-sn⟶ (cseq₂ p') (rcontext C dc psn⟶₁p') =
  rcontext (cseq₂ p' ∷ C) (dcseq₂ dc) psn⟶₁p'
Context1-sn⟶ (cshared s e) (rcontext C dc psn⟶₁p') =
  rcontext (cshared s e ∷ C) (dcshared dc) psn⟶₁p'
Context1-sn⟶ (cvar x e) (rcontext C dc psn⟶₁p') =
  rcontext (cvar x e ∷ C) (dcvar dc) psn⟶₁p'
Context1-sn⟶ (cif₁ x q) (rcontext C dc psn⟶₁p') =
  rcontext (cif₁ x q ∷ C) (dcif₁ dc) psn⟶₁p'
Context1-sn⟶ (cif₂ x p') (rcontext C dc psn⟶₁p') =
  rcontext (cif₂ x p' ∷ C) (dcif₂ dc) psn⟶₁p'
Context1-sn⟶ (cenv θ A) (rcontext C dc psn⟶₁p') =
  rcontext (cenv θ A ∷ C) (dcenv dc) psn⟶₁p'

Context1-sn⟶* : ∀{p p'} → (C1 : Context1) → p sn⟶* p' → (C1 ∷ []) ⟦ p ⟧c sn⟶* (C1 ∷ []) ⟦ p' ⟧c
Context1-sn⟶* C1 rrefl                 = rrefl
Context1-sn⟶* C1 (rstep psn⟶p' p'sn⟶*p'') = rstep (Context1-sn⟶ C1 psn⟶p') (Context1-sn⟶* C1 p'sn⟶*p'')

-- Unused helper function: compatible context append for _sn⟶_
-- We can't just give r sn⟶ C ⟦ p' ⟧c as the result since we can't pattern match on it
Context-sn⟶ : ∀{r p p'} →
  (C : Context) → r ≐ C ⟦ p ⟧c → p sn⟶ p' →
  Σ[ r' ∈ Term ] (r' ≐ C ⟦ p' ⟧c) × (r sn⟶ r')
Context-sn⟶ [] dchole psn⟶p' =
  _ , dchole ,′ psn⟶p'
Context-sn⟶ (_ ∷ C) (dcpar₁ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcpar₁ dc₂ ,′ rcontext _ (dcpar₁ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcpar₂ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcpar₂ dc₂ ,′ rcontext _ (dcpar₂ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcseq₁ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcseq₁ dc₂ ,′ rcontext _ (dcseq₁ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcseq₂ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcseq₂ dc₂ ,′ rcontext _ (dcseq₂ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcsuspend dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcsuspend dc₂ ,′ rcontext _ (dcsuspend dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dctrap dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dctrap dc₂ ,′ rcontext _ (dctrap dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcsignl dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcsignl dc₂ ,′ rcontext _ (dcsignl dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcpresent₁ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcpresent₁ dc₂ ,′ rcontext _ (dcpresent₁ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcpresent₂ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcpresent₂ dc₂ ,′ rcontext _ (dcpresent₂ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcloop dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcloop dc₂ ,′ rcontext _ (dcloop dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcloopˢ₁ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcloopˢ₁ dc₂ ,′ rcontext _ (dcloopˢ₁ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcloopˢ₂ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcloopˢ₂ dc₂ ,′ rcontext _ (dcloopˢ₂ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcshared dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcshared dc₂ ,′ rcontext _ (dcshared dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcvar dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcvar dc₂ ,′ rcontext _ (dcvar dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcif₁ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcif₁ dc₂ ,′ rcontext _ (dcif₁ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcif₂ dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcif₂ dc₂ ,′ rcontext _ (dcif₂ dc') psn⟶₁p'
Context-sn⟶ (_ ∷ C) (dcenv dc₁) psn⟶p' with Context-sn⟶ C dc₁ psn⟶p'
... | _ , dc₂ , rcontext _ dc' psn⟶₁p' =
  _ , dcenv dc₂ ,′ rcontext _ (dcenv dc') psn⟶₁p'

Context-sn⟶⟦⟧ : ∀{p q} → (C : Context) → p sn⟶ q → ((C ⟦ p ⟧c) sn⟶ (C ⟦ q ⟧c))
Context-sn⟶⟦⟧{p}  C psn⟶q with Context-sn⟶{r = C ⟦ p ⟧c} C Crefl psn⟶q
... | (r' , r=C⟦q⟧ , rsn⟶r') rewrite unplugc r=C⟦q⟧ = rsn⟶r'

Context-sn⟶* : ∀{p q} → (C : Context) → p sn⟶* q → (C ⟦ p ⟧c) sn⟶* (C ⟦ q ⟧c)
Context-sn⟶* C rrefl = rrefl
Context-sn⟶* C₁ (rstep C→ psn⟶*q) = (rstep (Context-sn⟶⟦⟧ C₁ C→) (Context-sn⟶* C₁ psn⟶*q))

sn⟶*+ : ∀{p q r} → p sn⟶* r → r sn⟶* q → p sn⟶* q
sn⟶*+ rrefl rsn⟶*q = rsn⟶*q
sn⟶*+ (rstep x psn⟶*r) rsn⟶*q = rstep x (sn⟶*+ psn⟶*r rsn⟶*q)

ρ-stays-ρ-sn⟶₁ : ∀{θ p q A} → (ρ⟨ θ , A ⟩· p) sn⟶₁ q → Σ[ θ' ∈ Env.Env ] Σ[ qin ∈ Term ] Σ[ A' ∈ Ctrl ] q ≡ (ρ⟨ θ' , A' ⟩· qin)
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (ris-present{p = p}{E = E} S∈ x x₁) = θ , E ⟦ p ⟧e , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (ris-absent{q = q}{E = E} S∈ x x₁) = θ , E ⟦ q ⟧e , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (remit{S = S}{E = E} S∈ _ x) = (Env.set-sig{S} θ S∈ Signal.present) , E ⟦ nothin ⟧e , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (rraise-shared{s = s}{p = p}{E = E} e' x) = θ , (E ⟦ (ρ⟨ (Θ SigMap.empty ShrMap.[ s ↦ (SharedVar.old ,′ (δ e'))] VarMap.empty) , WAIT ⟩· p) ⟧e) , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (rset-shared-value-old{s = s}{E = E} e' s∈ x x₁) = (Env.set-shr{s} θ s∈ (SharedVar.new) (δ e')) , E ⟦ nothin ⟧e , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (rset-shared-value-new{s = s}{E = E} e' s∈ x x₁) = (Env.set-shr{s} θ s∈ (SharedVar.new) (Env.shr-vals{s} θ s∈ + δ e')) , E ⟦ nothin ⟧e , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (rraise-var{x = x}{p = p}{E = E} e' x₁) = θ , (E ⟦ (ρ⟨ (Θ SigMap.empty ShrMap.empty VarMap.[ x ↦ δ e' ]) , WAIT ⟩· p) ⟧e) , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (rset-var{x = x}{E = E} x∈ e' x₁) = (Env.set-var{x} θ x∈ (δ e')) , E ⟦ nothin ⟧e , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (rif-false{q = q}{E = E} x∈ x₁ x₂) = θ , E ⟦ q ⟧e , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (rif-true{p = p}{E = E} x∈ x₁ x₂) = θ , E ⟦ p ⟧e , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (rabsence{.θ}{p}{S} S∈ x x₁) = (Env.set-sig{S} θ S∈ (Signal.absent)) , p , A , refl
ρ-stays-ρ-sn⟶₁ {θ} {A = A} (rreadyness{.θ}{p}{s} s∈ x x₁) = (Env.set-shr{s} θ s∈ (SharedVar.ready) (Env.shr-vals{s} θ s∈)) , p , A , refl
ρ-stays-ρ-sn⟶₁ {θ} (rmerge{θ₁}{θ₂}{r}{p}{E}{A₁}{A₂} x) =  (θ₁ ← θ₂) , E ⟦ p ⟧e , (A-max A₁ A₂) , refl

ρ-stays-ρ-sn⟶ : ∀{θ p q A} → (ρ⟨ θ , A ⟩· p) sn⟶ q → Σ[ θ' ∈ Env.Env ] Σ[ qin ∈ Term ] Σ[ A' ∈ Ctrl ] q ≡ (ρ⟨ θ' , A' ⟩· qin)
ρ-stays-ρ-sn⟶ (rcontext .[] dchole psn⟶₁p') = ρ-stays-ρ-sn⟶₁ psn⟶₁p'
ρ-stays-ρ-sn⟶ (rcontext .(cenv _ _ ∷ _) (dcenv dc) psn⟶₁p') = _ , _ , _ , refl

ρ-stays-ρ-sn⟶* : ∀{θ p q A} → (ρ⟨ θ , A ⟩· p) sn⟶* q → Σ[ θ' ∈ Env.Env ] Σ[ qin ∈ Term ] Σ[ A ∈ Ctrl ] q ≡ (ρ⟨ θ' , A ⟩· qin)
ρ-stays-ρ-sn⟶* rrefl = _ , _ , _ , refl
ρ-stays-ρ-sn⟶* (rstep x psn⟶*q) rewrite proj₂ (proj₂ (proj₂ (ρ-stays-ρ-sn⟶ x))) = ρ-stays-ρ-sn⟶* psn⟶*q
