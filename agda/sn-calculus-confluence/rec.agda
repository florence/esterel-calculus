module sn-calculus-confluence.rec where

open import Data.Nat using (_+_)
open import Function using (_∋_ ; _∘_)
open import Data.Nat.Properties.Simple using ( +-comm ; +-assoc )
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
open import Data.List.Any
open import Data.List.Any.Properties

open import Data.FiniteMap
import Data.OrderedListMap as OMap
open import Data.Nat as Nat using (ℕ)
open import Esterel.Variable.Signal as Signal
  using (Signal)
open import Esterel.Variable.Shared as SharedVar
  using (SharedVar)
open import Esterel.Variable.Sequential as SeqVar

open import sn-calculus-confluence.helper
open import sn-calculus-confluence.recrec

ρ-conf-rec : ∀{θ El Er ql qr i oli ori qro qlo FV BV θl θr A Al Ar}
             → CorrectBinding (ρ⟨ θ , A ⟩· i) FV BV
             → (ieql : i ≐ El ⟦ ql ⟧e)
             → (ieqr : i ≐ Er ⟦ qr ⟧e)
             → El a~ Er
             → (rl : (ρ⟨ θ , A ⟩· i) sn⟶₁ (ρ⟨ θl , Al ⟩· oli))
             → (rr : (ρ⟨ θ , A ⟩· i) sn⟶₁ (ρ⟨ θr , Ar ⟩· ori))
             → (olieq : oli ≐ El ⟦ qlo ⟧e)
             → (orieq : ori ≐ Er ⟦ qro ⟧e)
             → (->E-view rl ieql olieq)
             → (->E-view rr ieqr orieq)
             → (
             Σ[ θo ∈ Env ]
             Σ[ Ao ∈ Ctrl ]
             Σ[ si ∈ Term ]
             Σ[ Elo ∈ EvaluationContext ]
             Σ[ Ero ∈ EvaluationContext ]
             Σ[ oorieq ∈ ori ≐ Elo ⟦ ql ⟧e ]
             Σ[ oolieq ∈ oli ≐ Ero ⟦ qr ⟧e ]
             Σ[ sireq ∈ (si ≐ Elo ⟦ qlo ⟧e ) ]
             Σ[ sileq ∈ (si ≐ Ero ⟦ qro ⟧e ) ]
             Σ[ redl ∈ ((ρ⟨ θl , Al ⟩· oli) sn⟶₁ (ρ⟨ θo , Ao ⟩· si )) ]
             Σ[ redr ∈ ((ρ⟨ θr , Ar ⟩· ori) sn⟶₁ (ρ⟨ θo , Ao ⟩· si )) ]
             ((->E-view redl oolieq sileq) × (->E-view redr oorieq sireq)))

ρ-conf-rec {p₂} {El = El@.(epar₂ _ ∷ _)} {Er@.(epar₁ _ ∷ _)} {i = .(_ ∥ _)} cb (depar₂ ieqr) (depar₁ ieql) par redl redr olieq orieq viewl viewr with ρ-conf-rec2{El = El}{Er} cb (depar₂ ieqr) (depar₁ ieql) par redl redr olieq orieq viewl viewr refl refl
... | (θo , Ao , whatever , Erl , Ero , thig , oolieq , sireq , sileq , rlout , rrout , viewlo , viewro , _) = θo , Ao , whatever , Erl , Ero , thig , oolieq , sireq , sileq , rlout , rrout , viewlo , viewro

ρ-conf-rec {p₂} {El = (epar₁ q ∷ El)} {(epar₂ p ∷ Er)} {i = .(_ ∥ _)}{oli = (olp ∥ .q)}{ori = (.p ∥ orq)} cb@(CBρ (CBpar cbl cbr a b c d))  (depar₁ ieql) (depar₂ ieqr) par2 redl redr (depar₁ olieq) (depar₂ orieq) viewl viewr
  with unwrap-rho redl (depar₁ ieql) (depar₁ olieq) ieql olieq viewl | unwrap-rho redr (depar₂ ieqr) (depar₂ orieq) ieqr orieq viewr
... | (redli , viewli) | (redri , viewri) with wrap-rho redli ieql olieq viewli (epar₂ q) (depar₂ ieql) (depar₂ olieq) | wrap-rho redri ieqr orieq viewri (epar₁ p) (depar₁ ieqr) (depar₁ orieq)
... | (redl2 , viewl2) | (redr2 , viewr2) with ρ-conf-rec2{El = epar₂ q ∷ El}{epar₁ p ∷ Er}{oli = oli2}{ori = ori2} (CBρ (CBpar cbr cbl (distinct-sym a) (distinct-sym c) (distinct-sym b) (distinct'-sym d))) (depar₂ ieql) (depar₁ ieqr) par redl2 redr2  (depar₂ olieq) (depar₁ orieq) viewl2 viewr2 refl refl
      where
       oli2 = Term ∋ (q ∥ olp)
       ori2 = orq ∥ p
... | (θo , Ao , (sil@.orq ∥ sir@.olp) , (epar₂ _ ∷ Erl) , (epar₁ _ ∷ Ero) , (depar₂ oorieq) , (depar₁ oolieq) , (depar₂ sireq) , (depar₁ sileq) , rlout , rrout , viewlo , viewro , ((.Erl , .Ero , _ , _) , refl , refl))
    with unwrap-rho rlout (depar₁ oolieq) (depar₁ sileq) oolieq sileq viewlo | unwrap-rho rrout (depar₂ oorieq) (depar₂ sireq) oorieq sireq viewro
... | (roli , roliview) | (rori , roriview)
      with wrap-rho roli oolieq sileq roliview (epar₂ sir) (depar₂ oolieq) (depar₂ sileq) | wrap-rho rori oorieq sireq roriview (epar₁ sil) (depar₁ oorieq) (depar₁ sireq)
... | (rolo , roloview) | (roro , roroview) = θo , Ao , sir ∥ sil , epar₁ orq ∷ Erl ,
                                                                 epar₂ olp ∷ Ero ,
                                                                 depar₁ oorieq ,
                                                                 depar₂ oolieq ,
                                                                 depar₁ sireq , depar₂ sileq , rolo , roro , roloview , roroview -- _ , _ , _ , _ , _ , rolo , roro , roloview , roroview -- {! !}

ρ-conf-rec {El = epar₁ q ∷ El} {epar₁ .q ∷ Er} {ql} {qr} {.(_ ∥ q)} (CBρ (CBpar cb cb₁ x x₁ x₂ x₃)) (depar₁ ieql) (depar₁ ieqr) (parr a~~) redl redr (depar₁ olieq) (depar₁ orieq) viewl viewr
  with unwrap-rho redl (depar₁ ieql) (depar₁ olieq) ieql olieq viewl | unwrap-rho redr (depar₁ ieqr) (depar₁ orieq) ieqr orieq viewr
... | (redli , viewli) | (redri , viewri) with ρ-conf-rec (CBρ cb) ieql ieqr a~~ redli redri olieq orieq viewli viewri
... | ( θo , Ao , si , Elo , Ero , oorieq , oolieq , sireq , sileq , rlout , rrout , viewlo , viewro )
    with wrap-rho rlout oolieq sileq viewlo (epar₁ q) (depar₁ oolieq) (depar₁ sileq) | wrap-rho rrout oorieq sireq viewro (epar₁ q) (depar₁ oorieq) (depar₁ sireq)
... | (rol , rolview) | (ror , rorview) = θo , Ao , si ∥ q , (epar₁ q) ∷ Elo , (epar₁ q) ∷ Ero , depar₁ oorieq ,
                                                                                            depar₁ oolieq , depar₁ sireq , depar₁ sileq , rol , ror , rolview , rorview

ρ-conf-rec {El = (epar₂ p ∷ El)} {(epar₂ .p ∷ Er)} {i = .(_ ∥ _)} (CBρ (CBpar cb₁ cb x x₁ x₂ x₃)) (depar₂ ieql) (depar₂ ieqr) (parl a~~) redl redr (depar₂ olieq) (depar₂ orieq) viewl viewr
  with unwrap-rho redl (depar₂ ieql) (depar₂ olieq) ieql olieq viewl | unwrap-rho redr (depar₂ ieqr) (depar₂ orieq) ieqr orieq viewr
... | (redli , viewli) | (redri , viewri) with ρ-conf-rec (CBρ cb) ieql ieqr a~~ redli redri olieq orieq viewli viewri
... | ( θo , Ao , si , Elo , Ero , oorieq , oolieq , sireq , sileq , rlout , rrout , viewlo , viewro )
    with wrap-rho rlout oolieq sileq viewlo (epar₂ p) (depar₂ oolieq) (depar₂ sileq) | wrap-rho rrout oorieq sireq viewro (epar₂ p) (depar₂ oorieq) (depar₂ sireq)
... | (rol , rolview) | (ror , rorview) = θo , Ao , p ∥ si , (epar₂ p) ∷ Elo , (epar₂ p) ∷ Ero , depar₂ oorieq ,
                                                                                            depar₂ oolieq , depar₂ sireq , depar₂ sileq , rol , ror , rolview , rorview
ρ-conf-rec {El = (eseq q ∷ El)} {(eseq .q ∷ Er)} {i = .(_ >> q)} (CBρ (CBseq cb cb₁ x)) (deseq ieql) (deseq ieqr) (seq a~~) redl redr (deseq olieq) (deseq orieq) viewl viewr
  with unwrap-rho redl (deseq ieql) (deseq olieq) ieql olieq viewl | unwrap-rho redr (deseq ieqr) (deseq orieq) ieqr orieq viewr
... | (redli , viewli) | (redri , viewri) with ρ-conf-rec (CBρ cb) ieql ieqr a~~ redli redri olieq orieq viewli viewri
... | ( θo , Ao , si , Elo , Ero , oorieq , oolieq , sireq , sileq , rlout , rrout , viewlo , viewro )
    with wrap-rho rlout oolieq sileq viewlo (eseq q) (deseq oolieq) (deseq sileq) | wrap-rho rrout oorieq sireq viewro (eseq q) (deseq oorieq) (deseq sireq)
... | (rol , rolview) | (ror , rorview) = θo , Ao , (si >> q) , (eseq q) ∷ Elo , (eseq q) ∷ Ero , deseq oorieq ,
                                                                                            deseq oolieq , deseq sireq , deseq sileq , rol , ror , rolview , rorview

ρ-conf-rec {El = (eloopˢ q ∷ El)} {(eloopˢ .q ∷ Er)} {i = .(loopˢ _ q)} (CBρ (CBloopˢ cb cb₁ x _)) (deloopˢ ieql) (deloopˢ ieqr) (loopˢ a~~) redl redr (deloopˢ olieq) (deloopˢ orieq) viewl viewr
  with unwrap-rho redl (deloopˢ ieql) (deloopˢ olieq) ieql olieq viewl | unwrap-rho redr (deloopˢ ieqr) (deloopˢ orieq) ieqr orieq viewr
... | (redli , viewli) | (redri , viewri) with ρ-conf-rec (CBρ cb) ieql ieqr a~~ redli redri olieq orieq viewli viewri
... | ( θo , Ao , si , Elo , Ero , oorieq , oolieq , sireq , sileq , rlout , rrout , viewlo , viewro )
    with wrap-rho rlout oolieq sileq viewlo (eloopˢ q) (deloopˢ oolieq) (deloopˢ sileq) | wrap-rho rrout oorieq sireq viewro (eloopˢ q) (deloopˢ oorieq) (deloopˢ sireq)
... | (rol , rolview) | (ror , rorview) = θo , Ao , (loopˢ si q) , (eloopˢ q) ∷ Elo , (eloopˢ q) ∷ Ero , deloopˢ oorieq ,
                                                                                            deloopˢ oolieq , deloopˢ sireq , deloopˢ sileq , rol , ror , rolview , rorview


ρ-conf-rec {El = (esuspend S ∷ El)} {(esuspend .S ∷ Er)} {i = .(suspend _ _)} (CBρ (CBsusp cb x)) (desuspend ieql) (desuspend ieqr) (susp a~~) redl redr (desuspend olieq) (desuspend orieq) viewl viewr
  with unwrap-rho redl (desuspend ieql) (desuspend olieq) ieql olieq viewl | unwrap-rho redr (desuspend ieqr) (desuspend orieq) ieqr orieq viewr
... | (redli , viewli) | (redri , viewri) with ρ-conf-rec (CBρ cb) ieql ieqr a~~ redli redri olieq orieq viewli viewri
... | ( θo , Ao , si , Elo , Ero , oorieq , oolieq , sireq , sileq , rlout , rrout , viewlo , viewro )
    with wrap-rho rlout oolieq sileq viewlo (esuspend S) (desuspend oolieq) (desuspend sileq) | wrap-rho rrout oorieq sireq viewro (esuspend S) (desuspend oorieq) (desuspend sireq)
... | (rol , rolview) | (ror , rorview) = θo , Ao , (suspend si S) , (esuspend S) ∷ Elo , (esuspend S) ∷ Ero , desuspend oorieq ,
                                                                                            desuspend oolieq , desuspend sireq , desuspend sileq , rol , ror , rolview , rorview


ρ-conf-rec {El = (etrap ∷ El)} {(etrap ∷ Er)} {i = .(trap _)} (CBρ (CBtrap cb)) (detrap ieql) (detrap ieqr) (trp a~~) redl redr (detrap olieq) (detrap orieq) viewl viewr
  with unwrap-rho redl (detrap ieql) (detrap olieq) ieql olieq viewl | unwrap-rho redr (detrap ieqr) (detrap orieq) ieqr orieq viewr
... | (redli , viewli) | (redri , viewri) with ρ-conf-rec (CBρ cb) ieql ieqr a~~ redli redri olieq orieq viewli viewri
... | ( θo , Ao , si , Elo , Ero , oorieq , oolieq , sireq , sileq , rlout , rrout , viewlo , viewro )
    with wrap-rho rlout oolieq sileq viewlo (etrap) (detrap oolieq) (detrap sileq) | wrap-rho rrout oorieq sireq viewro (etrap) (detrap oorieq) (detrap sireq)
... | (rol , rolview) | (ror , rorview) = θo , Ao , (trap si) , (etrap) ∷ Elo , (etrap) ∷ Ero , detrap oorieq ,
                                                                                            detrap oolieq , detrap sireq , detrap sileq , rol , ror , rolview , rorview
