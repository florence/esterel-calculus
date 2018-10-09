module sn-calculus-confluence.recrec where

open import Data.Nat using (_+_)
open import Function using (_∋_ ; _∘_ ; id)
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

ρ-conf-rec2 : ∀{θ El Er ql qr i oli ori qro qlo FV BV θl θr a b El' Er'}
             → CorrectBinding (ρ θ · i) FV BV
             → (ieql : i ≐ El ⟦ ql ⟧e)
             → (ieqr : i ≐ Er ⟦ qr ⟧e)
             → El a~ Er
             → (rl : (ρ θ · i) sn⟶₁ (ρ θl · oli))
             → (rr : (ρ θ · i) sn⟶₁ (ρ θr · ori))
             → (olieq : oli ≐ El ⟦ qlo ⟧e)
             → (orieq : ori ≐ Er ⟦ qro ⟧e)
             → (->E-view rl ieql olieq)
             → (->E-view rr ieqr orieq)
             → (El ≡ (epar₂ a ∷ El'))
             → (Er ≡ (epar₁ b ∷ Er'))
             → (
             Σ[ θo ∈ Env ]
             Σ[ si ∈ Term ]
             Σ[ Elo ∈ EvaluationContext ]
             Σ[ Ero ∈ EvaluationContext ]
             Σ[ oorieq ∈ ori ≐ Elo ⟦ ql ⟧e ]
             Σ[ oolieq ∈ oli ≐ Ero ⟦ qr ⟧e ]
             Σ[ sireq ∈ (si ≐ Elo ⟦ qlo ⟧e ) ]
             Σ[ sileq ∈ (si ≐ Ero ⟦ qro ⟧e ) ]
             Σ[ redl ∈ ((ρ θl · oli) sn⟶₁ (ρ θo · si )) ]
             Σ[ redr ∈ ((ρ θr · ori) sn⟶₁ (ρ θo · si )) ]
             ((->E-view redl oolieq sileq)
              ×
              (->E-view redr oorieq sireq)
              ×
              (∃ λ { (Elo' , Ero' , a , b) → (Elo ≡ (epar₂ a ∷ Elo') × Ero ≡ (epar₁ b ∷ Ero'))})))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)}{ql = ql}{qr = qr} {i = .(p ∥ q)} cb (depar₂ ieql) (depar₁ ieqr) par (ris-present{p = pr} a1 b1 .(depar₂ ieql)) (ris-present{p = pl} a2 b2 (depar₁ .ieqr)) olieq orieq vis-present vis-present refl refl
    = θ , (El ⟦ pl ⟧e) ∥ (Er ⟦ pr ⟧e) , (epar₂ (El ⟦ pl ⟧e) ∷ Er) , (epar₁ (Er ⟦ pr ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , (ris-present a2 b2 (depar₁ ieqr)) , (ris-present a1 b1 (depar₂ ieql))
        , (vis-present , vis-present , (_ , refl , refl))

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} cb (depar₂ ieql) (depar₁ ieqr) par (ris-present{p = r} a1 b1 .(depar₂ ieql)) (ris-absent{q = l} a2 b2 .(depar₁ ieqr)) olieq orieq vis-present vis-absent refl refl
   = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)) , depar₂ ieql , (depar₁ ieqr) , Erefl , (Erefl , ((ris-absent a2 b2 (depar₁ ieqr)) , ((ris-present a1 b1 (depar₂ ieql)) , (vis-absent , vis-present , (_ , refl , refl)))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-present a1 b1 .(depar₂ ieql)) (rraise-shared a2 .(depar₁ ieqr)) olieq orieq vis-present vraise-shared refl refl
 = θ , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , ((depar₁ ieqr) , (Erefl , (Erefl , ((rraise-shared a2 (depar₁ ieqr)) , ((ris-present a1 b1 (depar₂ ieql)) , (vraise-shared , vis-present , (_ , refl , refl))))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-present a1 b1 .(depar₂ ieql)) (rraise-var a2    .(depar₁ ieqr)) olieq orieq vis-present vraise-var refl refl
   = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , (rraise-var a2 (depar₁ ieqr)) , ((ris-present a1 b1 (depar₂ ieql)) , (vraise-var , vis-present , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-present a1 b1 .(depar₂ ieql)) (rif-false a2 b2 .(depar₁ ieqr)) olieq orieq vis-present vif-false refl refl
   =  θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , (rif-false a2 b2 (depar₁ ieqr)) , ((ris-present a1 b1 (depar₂ ieql)) , (vif-false , vis-present , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-present a1 b1 .(depar₂ ieql)) (rif-true a2 b2 .(depar₁ ieqr)) olieq orieq vis-present vif-true refl refl
  = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , (rif-true a2 b2 (depar₁ ieqr)) , ((ris-present a1 b1 (depar₂ ieql)) , (vif-true , vis-present , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-absent a1 b1 .(depar₂ ieql)) (ris-present a2 b2 .(depar₁ ieqr)) olieq orieq vis-absent vis-present refl refl
   = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-present a2 b2 (depar₁ ieqr) , (ris-absent a1 b1 (depar₂ ieql) , (vis-present , vis-absent , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-absent a1 b1 .(depar₂ ieql)) (ris-absent a2 b2 .(depar₁ ieqr)) olieq orieq vis-absent vis-absent refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-absent a2 b2 (depar₁ ieqr) , (ris-absent a1 b1 (depar₂ ieql) , (vis-absent , vis-absent , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-absent a1 b1 .(depar₂ ieql)) (rif-false a2 b2 .(depar₁ ieqr)) olieq orieq vis-absent vif-false refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-false a2 b2 (depar₁ ieqr) , (ris-absent a1 b1 (depar₂ ieql) , (vif-false , vis-absent , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-absent a1 b1 .(depar₂ ieql)) (rif-true a2 b2 .(depar₁ ieqr)) olieq orieq vis-absent vif-true refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-true a2 b2 (depar₁ ieqr) , (ris-absent a1 b1 (depar₂ ieql) , (vif-true , vis-absent , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-absent a1 b1 .(depar₂ ieql)) (rraise-var a2 .(depar₁ ieqr)) olieq orieq vis-absent vraise-var refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-var a2 (depar₁ ieqr) , (ris-absent a1 b1 (depar₂ ieql) , (vraise-var , vis-absent , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-absent a1 b1 .(depar₂ ieql)) (rraise-shared a2 .(depar₁ ieqr)) olieq orieq vis-absent vraise-shared refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-shared a2 (depar₁ ieqr) , (ris-absent a1 b1 (depar₂ ieql) , (vraise-shared , vis-absent , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-shared a .(depar₂ ieql)) (ris-present a2 b2 .(depar₁ ieqr)) olieq orieq vraise-shared vis-present refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-present a2 b2 (depar₁ ieqr) , (rraise-shared a (depar₂ ieql) , (vis-present , vraise-shared , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-shared a .(depar₂ ieql)) (ris-absent a2 b2 .(depar₁ ieqr)) olieq orieq vraise-shared vis-absent refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-absent a2 b2 (depar₁ ieqr) , (rraise-shared a (depar₂ ieql) , (vis-absent , vraise-shared , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-shared a .(depar₂ ieql)) (rraise-shared a2 .(depar₁ ieqr)) olieq orieq vraise-shared vraise-shared refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-shared a2 (depar₁ ieqr) , (rraise-shared a (depar₂ ieql) , (vraise-shared , vraise-shared , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-shared a .(depar₂ ieql)) (rif-false a2 b2 .(depar₁ ieqr)) olieq orieq vraise-shared vif-false refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-false a2 b2 (depar₁ ieqr) , (rraise-shared a (depar₂ ieql) , (vif-false , vraise-shared , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-shared a .(depar₂ ieql)) (rif-true a2 b2 .(depar₁ ieqr)) olieq orieq vraise-shared vif-true refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-true a2 b2 (depar₁ ieqr) , (rraise-shared a (depar₂ ieql) , (vif-true , vraise-shared , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-shared a .(depar₂ ieql)) (rraise-var a2 .(depar₁ ieqr)) olieq orieq vraise-shared vraise-var refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-var a2 (depar₁ ieqr) , (rraise-shared a (depar₂ ieql) , (vraise-var , vraise-shared , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-var a1 .(depar₂ ieql)) (ris-present a2 b2 .(depar₁ ieqr)) olieq orieq vraise-var vis-present refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-present a2 b2 (depar₁ ieqr) , (rraise-var a1 (depar₂ ieql) , (vis-present , vraise-var , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-var a1 .(depar₂ ieql)) (ris-absent a2 b2 .(depar₁ ieqr)) olieq orieq vraise-var vis-absent refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-absent a2 b2 (depar₁ ieqr) , (rraise-var a1 (depar₂ ieql) , (vis-absent , vraise-var , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-var a1 .(depar₂ ieql)) (rraise-shared a2 .(depar₁ ieqr)) olieq orieq vraise-var vraise-shared refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-shared a2 (depar₁ ieqr) , (rraise-var a1 (depar₂ ieql) , (vraise-shared , vraise-var , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-var a1 .(depar₂ ieql)) (rraise-var a2 .(depar₁ ieqr)) olieq orieq vraise-var vraise-var refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-var a2 (depar₁ ieqr) , (rraise-var a1 (depar₂ ieql) , (vraise-var , vraise-var , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-var a1 .(depar₂ ieql)) (rif-false a2 b2 .(depar₁ ieqr)) olieq orieq vraise-var vif-false refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-false a2 b2 (depar₁ ieqr) , (rraise-var a1 (depar₂ ieql) , (vif-false , vraise-var , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rraise-var a1 .(depar₂ ieql)) (rif-true a2 b2 .(depar₁ ieqr)) olieq orieq vraise-var vif-true refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-true a2 b2 (depar₁ ieqr) , (rraise-var a1 (depar₂ ieql) , (vif-true , vraise-var , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-false a1 b1 .(depar₂ ieql)) (ris-present a2 b2 .(depar₁ ieqr)) olieq orieq vif-false vis-present refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-present a2 b2 (depar₁ ieqr) , (rif-false a1 b1 (depar₂ ieql) , (vis-present , vif-false , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-false a1 b1 .(depar₂ ieql)) (ris-absent a2 b2 .(depar₁ ieqr)) olieq orieq vif-false vis-absent refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-absent a2 b2 (depar₁ ieqr) , (rif-false a1 b1 (depar₂ ieql) , (vis-absent , vif-false , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-false a1 b1 .(depar₂ ieql)) (rraise-shared a2 .(depar₁ ieqr)) olieq orieq vif-false vraise-shared refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-shared a2 (depar₁ ieqr) , (rif-false a1 b1 (depar₂ ieql) , (vraise-shared , vif-false , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-false a1 b1 .(depar₂ ieql)) (rraise-var a2 .(depar₁ ieqr)) olieq orieq vif-false vraise-var refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-var a2 (depar₁ ieqr) , (rif-false a1 b1 (depar₂ ieql) , (vraise-var , vif-false , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-false a1 b1 .(depar₂ ieql)) (rif-false a2 b2 .(depar₁ ieqr)) olieq orieq vif-false vif-false refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-false a2 b2 (depar₁ ieqr) , (rif-false a1 b1 (depar₂ ieql) , (vif-false , vif-false , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-false a1 b1 .(depar₂ ieql)) (rif-true a2 b2 .(depar₁ ieqr)) olieq orieq vif-false vif-true refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-true a2 b2 (depar₁ ieqr) , (rif-false a1 b1 (depar₂ ieql) , (vif-true , vif-false , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-true a1 b1 .(depar₂ ieql)) (ris-present a2 b2 .(depar₁ ieqr)) olieq orieq vif-true vis-present refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-present a2 b2 (depar₁ ieqr) , (rif-true a1 b1 (depar₂ ieql) , (vis-present , vif-true , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-true a1 b1 .(depar₂ ieql)) (ris-absent a2 b2 .(depar₁ ieqr)) olieq orieq vif-true vis-absent refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , ris-absent a2 b2 (depar₁ ieqr) , (rif-true a1 b1 (depar₂ ieql) , (vis-absent , vif-true , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-true a1 b1 .(depar₂ ieql)) (rraise-shared a2 .(depar₁ ieqr)) olieq orieq vif-true vraise-shared refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-shared a2 (depar₁ ieqr) , (rif-true a1 b1 (depar₂ ieql) , (vraise-shared , vif-true , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-true a1 b1 .(depar₂ ieql)) (rraise-var a2 .(depar₁ ieqr)) olieq orieq vif-true vraise-var refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rraise-var a2 (depar₁ ieqr) , (rif-true a1 b1 (depar₂ ieql) , (vraise-var , vif-true , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-true a1 b1 .(depar₂ ieql)) (rif-false a2 b2 .(depar₁ ieqr)) olieq orieq vif-true vif-false refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-false a2 b2 (depar₁ ieqr) , (rif-true a1 b1 (depar₂ ieql) , (vif-false , vif-true , (_ , refl , refl)))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (rif-true a1 b1 .(depar₂ ieql)) (rif-true a2 b2 .(depar₁ ieqr)) olieq orieq vif-true vif-true refl refl
 = θ , ( ( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ) ) , (epar₂ (El ⟦ l ⟧e) ∷ Er) , (epar₁ (Er ⟦ r ⟧e) ∷ El) , depar₂ ieql , (depar₁ ieqr) , Erefl , Erefl , rif-true a2 b2 (depar₁ ieqr) , (rif-true a1 b1 (depar₂ ieql) , (vif-true , vif-true , (_ , refl , refl)))

--   = ? , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , ({!!} , ({!!} , ({!!} , {!!})))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)}{qro = l}{qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-present{S = Sp} a b .(depar₂ ieql)) (remit{S = S} ein ¬S≡a .(depar₁ ieqr)) olieq orieq vis-present vemit refl refl
    with Sp Signal.≟ S
... | yes refl = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr) , (Erefl , Erefl , ((remit ein ¬S≡a (depar₁ ieqr)) , (ris-present (sig-set-mono'{Sp}{S}{θ}{Signal.present}{ein} a) eq (depar₂ ieql) , (vemit , vis-present , (_ , refl , refl))))))
      where θo = (set-sig{S = S} θ ein Signal.present)
            eq = (sig-putget {S}{θ}{Signal.present} a (sig-set-mono'{S}{S}{θ}{Signal.present}{a} a))
... | no ¬pr = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr) , (Erefl , Erefl , ((remit ein ¬S≡a (depar₁ ieqr)) , (ris-present (sig-set-mono'{Sp}{S}{θ}{Signal.present}{ein} a) eq (depar₂ ieql) , (vemit , vis-present , (_ , refl , refl))))))
      where θo = (set-sig{S = S} θ ein Signal.present)
            eq = (sig-putputget{Sp}{S}{θ}{Signal.present}{Signal.present} ¬pr a ein (sig-set-mono'{Sp}{S}{θ}{Signal.present}{ein} a) b)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (ris-present a1 b1 .(depar₂ ieql)) (rset-shared-value-old{s = s} a2 b2 c2 .(depar₁ ieqr)) olieq orieq vis-present vset-shared-value-old refl refl
   = (Env.set-shr{s} θ b2 (SharedVar.new) (δ a2)) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr) , (Erefl , Erefl , (rset-shared-value-old a2 b2 c2 (depar₁ ieqr) , (ris-present a1 b1 (depar₂ ieql) , (vset-shared-value-old , vis-present , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (ris-present a b .(depar₂ ieql)) (rset-shared-value-new{s = s} e' s∈ x .ieqr) olieq orieq vis-present vset-shared-value-new refl refl
   = (Env.set-shr{s} θ s∈ (SharedVar.new) (Env.shr-vals{s} θ s∈ + δ e')) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (rset-shared-value-new e' s∈ x (depar₁ ieqr') , (ris-present a b (depar₂ ieql) , (vset-shared-value-new , vis-present , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (ris-present a b .(depar₂ ieql)) (rset-var{x = x} x∈ e' .ieqr) olieq orieq vis-present vset-var refl refl
   =  (Env.set-var{x} θ x∈ (δ e')) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (rset-var x∈ e' (depar₁ ieqr') , (ris-present a b (depar₂ ieql) , (vset-var , vis-present , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (ris-absent{S = Sp} Sp∈ Sp≡ .(depar₂ ieql)) (remit{S = S} S∈ ¬S≡a .ieqr) olieq orieq vis-absent vemit refl refl
  with Sp Signal.≟ S
... | yes refl = ⊥-elim (¬S≡a (subst (λ x → sig-stats{Sp} θ x ≡ Signal.absent) (sig∈-eq{S}{θ} Sp∈ S∈) Sp≡))
... | no ¬pr
   = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (remit S∈ ¬S≡a (depar₁ ieqr') , (ris-absent (sig-set-mono'{Sp}{S}{θ}{_}{S∈} Sp∈) eq (depar₂ ieql) , (vemit , vis-absent , (_ , refl , refl))))))
   where θo = (set-sig{S = S} θ S∈ Signal.present)
         eq = (sig-putputget{Sp}{S}{θ}{_}{_} ¬pr Sp∈ S∈ (sig-set-mono'{Sp}{S}{θ}{Signal.present}{S∈} Sp∈) Sp≡)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (ris-absent{S = Sp} Sp∈ Sp≡ .(depar₂ ieql)) (rset-shared-value-old{s = s} e' s∈ x .ieqr) olieq orieq vis-absent vset-shared-value-old refl refl
    = (Env.set-shr{s} θ s∈ (SharedVar.new) (δ e')) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (rset-shared-value-old e' s∈ x (depar₁ ieqr') , (ris-absent Sp∈ Sp≡ (depar₂ ieql) , (vset-shared-value-old , vis-absent , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (ris-absent{S = Sp} Sp∈ Sp≡ .(depar₂ ieql)) (rset-shared-value-new{s = s} e' s∈ x .ieqr) olieq orieq vis-absent vset-shared-value-new  refl refl
   = (Env.set-shr{s} θ s∈ (SharedVar.new) (Env.shr-vals{s} θ s∈ + δ e')) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (rset-shared-value-new e' s∈ x (depar₁ ieqr') , (ris-absent Sp∈ Sp≡ (depar₂ ieql) , (vset-shared-value-new , vis-absent , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (ris-absent{S = Sp} Sp∈ Sp≡ .(depar₂ ieql)) (rset-var{x = x} x∈ e' .ieqr) olieq orieq vis-absent vset-var refl refl
   = (Env.set-var{x} θ x∈ (δ e')) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (rset-var x∈ e' (depar₁ ieqr') , (ris-absent Sp∈ Sp≡ (depar₂ ieql) , (vset-var , vis-absent , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (remit{S = S} ein ¬S≡a .(depar₂ ieql)) (ris-present{S = Sp} a b .(depar₁ ieqr)) olieq orieq vemit vis-present  refl refl
    with Sp Signal.≟ S
... | yes refl = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr) , (Erefl , Erefl , (ris-present (sig-set-mono'{Sp}{S}{θ}{Signal.present}{ein} a) eq (depar₁ ieqr) , ((remit ein ¬S≡a (depar₂ ieql)) , (vis-present , vemit , (_ , refl , refl))))))
      where θo = (set-sig{S = S} θ ein Signal.present)
            eq = (sig-putget {S}{θ}{Signal.present} a (sig-set-mono'{S}{S}{θ}{Signal.present}{a} a))
... | no ¬pr = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr) , (Erefl , Erefl , (ris-present (sig-set-mono'{Sp}{S}{θ}{Signal.present}{ein} a) eq (depar₁ ieqr) , ((remit ein ¬S≡a (depar₂ ieql)) , (vis-present , vemit , (_ , refl , refl))))))
      where θo = (set-sig{S = S} θ ein Signal.present)
            eq = (sig-putputget{Sp}{S}{θ}{Signal.present}{Signal.present} ¬pr a ein (sig-set-mono'{Sp}{S}{θ}{Signal.present}{ein} a) b)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) (depar₁ ieqr) par (remit{S = S} S∈ ¬S≡a .(depar₂ ieql)) (ris-absent{S = Sp} Sp∈ Sp≡ .(depar₁ ieqr)) olieq orieq vemit vis-absent refl refl
  with Sp Signal.≟ S
... | yes refl = ⊥-elim ((¬S≡a (subst (λ x → sig-stats{Sp} θ x ≡ Signal.absent) (sig∈-eq{S}{θ} Sp∈ S∈) Sp≡)))
... | no ¬pr
   = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr) , (Erefl , Erefl , (ris-absent (sig-set-mono'{Sp}{S}{θ}{_}{S∈} Sp∈) eq (depar₁ ieqr) , (remit S∈ ¬S≡a (depar₂ ieql) , (vis-absent , vemit , (_ , refl , refl))))))
   where θo = (set-sig{S = S} θ S∈ Signal.present)
         eq = (sig-putputget{Sp}{S}{θ}{_}{_} ¬pr Sp∈ S∈ (sig-set-mono'{Sp}{S}{θ}{Signal.present}{S∈} Sp∈) Sp≡)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = S} S∈ ¬S≡a  .(depar₂ ieql)) (rif-false{x = x} x∈ x≡ .ieqr) olieq orieq vemit vif-false refl refl
   = (Env.set-sig{S} θ S∈ Signal.present) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (rif-false x∈ x≡ (depar₁ ieqr') , (remit S∈ ¬S≡a (depar₂ ieql) , (vif-false , vemit , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = S} S∈ ¬S≡a  .(depar₂ ieql)) (rif-true{x = x} x∈ x≡ .ieqr) olieq orieq vemit vif-true refl refl
   = (Env.set-sig{S} θ S∈ Signal.present) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (rif-true x∈ x≡ (depar₁ ieqr') , (remit S∈ ¬S≡a (depar₂ ieql) , (vif-true , vemit , (_ , refl , refl))))))

 --  = (Env.set-sig{S} θ S∈ Signal.present) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , ({!!} , ({!!} , ({!!} , {!!})))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = S} S∈ ¬S≡a  .(depar₂ ieql)) (rraise-shared{s = s}{p = pp} e' .ieqr) olieq orieq vemit vraise-shared refl refl
   with (ready-maint/irr S S∈ Signal.present e')
... | e'' , e≡
    = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl ,
         ((proj₁ rett)
         , (remit S∈ ¬S≡a (depar₂ ieql) , (proj₂ rett , vemit , (_ , refl , refl))))))
    where
     θo = (Env.set-sig{S} θ S∈ Signal.present)
     get : (typeof e≡) → Σ[ redl ∈ ((ρ θo · p ∥ (Er ⟦ r ⟧e)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₁ ieqr') Erefl
     get e≡ rewrite e≡ = (rraise-shared e'' (depar₁ ieqr')) , vraise-shared
     rett = (get e≡)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = S} S∈ ¬S≡a  .(depar₂ ieql)) (rset-shared-value-old{s = s}{e = ee} e' s∈ s≡ .ieqr) olieq orieq vemit vset-shared-value-old refl refl
   with (ready-maint/irr S S∈ Signal.present e')
... | (e'' , e≡)
  = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (proj₁ rett , (remit S∈ ¬S≡a (depar₂ ieql) , (proj₂ rett , vemit , (_ , refl , refl))))))
  where
    θo = (Env.set-sig{S} (Env.set-shr{s = s} θ s∈ SharedVar.new (δ e')) S∈ Signal.present)
    get : (typeof e≡) → Σ[ redl ∈ ((ρ (Env.set-sig{S} θ S∈ Signal.present) · p ∥ (Er ⟦ r ⟧e)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₁ ieqr') Erefl
    get e≡ rewrite e≡ = (rset-shared-value-old e'' s∈ s≡ (depar₁ ieqr')) , vset-shared-value-old
    rett = (get e≡)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = S} S∈ ¬S≡a  .(depar₂ ieql)) rl@(rset-shared-value-new{s = s} e' s∈ s≡ .ieqr) olieq orieq vemit vset-shared-value-new refl refl
   with (ready-maint/irr S S∈ Signal.present e')
... | (e'' , e≡)
   = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (proj₁ rett , (remit S∈ ¬S≡a (depar₂ ieql) , (proj₂ rett , vemit , (_ , refl , refl))))))
   where
    θo = (Env.set-sig{S} (Env.set-shr{s} θ s∈ SharedVar.new ( (shr-vals{s = s} θ s∈) + (δ e') )) S∈ Signal.present)
    get : (typeof e≡) → Σ[ redl ∈ ((ρ (Env.set-sig{S} θ S∈ Signal.present) · p ∥ (Er ⟦ r ⟧e)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₁ ieqr') Erefl
    get e≡ rewrite e≡ = (rset-shared-value-new e'' s∈ s≡ (depar₁ ieqr')) , vset-shared-value-new
    rett = (get e≡)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = S} S∈ ¬S≡a  .(depar₂ ieql)) (rraise-var{x = x} e' .ieqr) olieq orieq vemit vraise-var refl refl
   with ready-maint/irr S S∈ Signal.present e'
... | (e'' , e≡)
   = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (proj₁ rett , (remit S∈ ¬S≡a (depar₂ ieql) , (proj₂ rett , vemit , (_ , refl , refl))))))
   where
    θo = (Env.set-sig{S} θ S∈ Signal.present)
    get : (typeof e≡) → Σ[ redl ∈ ((ρ θo · p ∥ (Er ⟦ r ⟧e)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₁ ieqr') Erefl
    get e≡ rewrite e≡ = (rraise-var e'' (depar₁ ieqr')) , vraise-var
    rett = (get e≡)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = S} S∈ ¬S≡a  .(depar₂ ieql)) (rset-var{x = x} x∈ e' .ieqr) olieq orieq vemit vset-var refl refl
   with (ready-maint/irr S S∈ Signal.present e')
... | (e'' , e≡)
   = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (proj₁ rett , (remit S∈ ¬S≡a (depar₂ ieql) , (proj₂ rett , vemit , (_ , refl , refl))))))
   where
    θo = (Env.set-sig {S} (Env.set-var{x} θ x∈ (δ e')) S∈ Signal.present)
    θ2 = (Env.set-sig {S} θ S∈ Signal.present)
    get : (typeof e≡) → Σ[ redl ∈ ((ρ θ2 · p ∥ (Er ⟦ r ⟧e)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₁ ieqr') Erefl
    get e≡ rewrite e≡ = (rset-var{x = x} x∈ e'' (depar₁ ieqr')) , vset-var
    rett = (get e≡)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = Sl} Sl∈ ¬Sl≡a  .(depar₂ ieql)) (remit{S = Sr} Sr∈ ¬Sr≡a .ieqr) olieq orieq vemit vemit refl refl
   with Sr Signal.≟ Sl
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = Sl} Sl∈  ¬Sl≡a.(depar₂ ieql)) (remit{S = Sr} Sr∈ ¬Sr≡a .ieqr) olieq orieq vemit vemit refl refl | no ¬pr
   with sig-set-comm{θ}{Sl}{Sr}{Signal.present}{Signal.present} Sl∈ Sr∈ (λ x → ¬pr (sym x))
... | in1 , in2 , θ≡ = θo  , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (remit {S = Sr} in2 (sig-put-mby-overwrite Sr Sl θ Signal.absent Signal.present Sr∈ Sl∈
                                                                                                                                                                                                 in2 (λ ()) ¬Sr≡a) (depar₁ ieqr') , ( proj₁ (get θ≡)  , (vemit , proj₂ (get θ≡) , (_ , refl , refl))))))
  where
     θl = (Env.set-sig{Sl} θ Sl∈ Signal.present)
     θr = (Env.set-sig{Sr} θ Sr∈ Signal.present)
     θo = (Env.set-sig{Sr} θl in2 Signal.present)
     get : (typeof θ≡) →  Σ[ redl ∈ ((ρ θr · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₂ ieql) Erefl
     get θ≡ rewrite θ≡ = remit in1 (sig-put-mby-overwrite Sl Sr θ Signal.absent Signal.present Sl∈ Sr∈ in1 (λ ()) ¬Sl≡a) (depar₂ ieql) , vemit
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (remit{S = Sl} Sl∈ ¬Sl≡a .(depar₂ ieql)) (remit{S = Sr} Sr∈ ¬Sr≡a .ieqr) olieq orieq vemit vemit refl refl | yes refl  with sig∈-eq{Sl}{θ} Sl∈ Sr∈
... | ∈≡ rewrite ∈≡ = θ2  , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (remit {S = S} S∈2 ((sig-put-mby-overwrite Sl Sr θ Signal.absent Signal.present Sr∈ Sl∈ S∈2 (λ ()) ¬Sl≡a) )
             (depar₁ ieqr') , (remit {S = S} S∈2 ((sig-put-mby-overwrite Sl Sr θ Signal.absent Signal.present Sr∈ Sl∈ S∈2 (λ ()) ¬Sl≡a)) (depar₂ ieql) , (vemit , vemit , (_ , refl , refl))))))
      where
        S = Sl
        θ1 = (Env.set-sig{S} θ Sl∈ Signal.present)
        S∈2 = sig-set-mono'{S}{S}{θ}{Signal.present}{Sl∈} Sr∈
        θ2 = (Env.set-sig{S} θ1 S∈2 Signal.present)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rraise-shared{s = s}{p = pp} e' .(depar₂ ieql)) (remit{S = S} S∈ ¬S≡a .ieqr) olieq orieq vraise-shared vemit refl refl
   with (ready-maint/irr S S∈ Signal.present e')
... | e'' , e≡
    = θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl ,
         (remit S∈ ¬S≡a (depar₁ ieqr')
         ,((proj₁ rett) , (vemit , proj₂ rett , (_ , refl , refl))))))
    where
     θo = (Env.set-sig{S} θ S∈ Signal.present)
     get : (typeof e≡) → Σ[ redl ∈ ((ρ θo · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₂ ieql) Erefl
     get e≡ rewrite e≡ = (rraise-shared e'' (depar₂ ieql)) , vraise-shared
     rett = (get e≡)

--  = ? , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , ({!!} , ({!!} , ({!!} , {!!})))))


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rset-shared-value-old{s = sl} e'l sl∈ sl≡ .(depar₂ ieql)) (ris-present{S = S} S∈ S≡ .ieqr) olieq orieq vset-shared-value-old vis-present refl refl
  =  θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (ris-present S∈ S≡ (depar₁ ieqr') , (rset-shared-value-old e'l sl∈ sl≡ (depar₂ ieql) , (vis-present , vset-shared-value-old , (_ , refl , refl))))))
  where
   θo = (Env.set-shr{sl} θ sl∈ (SharedVar.new) (δ e'l))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rset-shared-value-old{s = sl} e'l sl∈ sl≡ .(depar₂ ieql)) (ris-absent{S = S} S∈ S≡ .ieqr) olieq orieq vset-shared-value-old vis-absent refl refl
   =  (Env.set-shr{sl} θ sl∈ (SharedVar.new) (δ e'l)) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (ris-absent S∈ S≡ (depar₁ ieqr') , (rset-shared-value-old e'l sl∈ sl≡ (depar₂ ieql) , (vis-absent , vset-shared-value-old , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rset-shared-value-old{s = sl} e'l sl∈ sl≡ .(depar₂ ieql)) (remit{S = S} S∈ ¬S≡a .ieqr) olieq orieq vset-shared-value-old vemit refl refl
  =  θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (remit S∈ ¬S≡a (depar₁ ieqr') , (proj₁ res , (vemit , proj₂ res , (_ , refl , refl))))))
  where
    θ1 = (Env.set-sig{S} θ S∈ Signal.present)
    θ2 = (Env.set-shr{sl} θ sl∈ (SharedVar.new) (δ e'l))
    θo = (Env.set-sig{S} θ2 S∈ Signal.present)
    e≡ = (ready-maint/irr S S∈ Signal.present e'l)
    get : (typeof e≡) → Σ[ redl ∈ ((ρ θ1 · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₂ ieql) Erefl
    get (e'' , e≡) rewrite e≡ = rset-shared-value-old {s = sl} e'' sl∈ sl≡ (depar₂ ieql) , vset-shared-value-old
    res = get e≡
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rset-shared-value-old{s = sl} e'l sl∈ sl≡ .(depar₂ ieql)) (rif-false{x = x} x∈ x≡ .ieqr) olieq orieq vset-shared-value-old vif-false refl refl
  =  θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (rif-false x∈ x≡ (depar₁ ieqr') , (rset-shared-value-old e'l sl∈ sl≡ (depar₂ ieql) , (vif-false , vset-shared-value-old , (_ , refl , refl))))))
    where
     θo = (Env.set-shr{sl} θ sl∈ (SharedVar.new) (δ e'l))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rset-shared-value-old{s = sl} e'l sl∈ sl≡ .(depar₂ ieql)) (rif-true x∈ x≡ .ieqr) olieq orieq vset-shared-value-old vif-true refl refl
  = (Env.set-shr{sl} θ sl∈ (SharedVar.new) (δ e'l)) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (rif-true x∈ x≡ (depar₁ ieqr') , (rset-shared-value-old e'l sl∈ sl≡ (depar₂ ieql) , (vif-true , vset-shared-value-old , (_ , refl , refl))))))

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rset-shared-value-new{s = sl} e'l sl∈ sl≡ .(depar₂ ieql)) (ris-absent S∈ S≡ .ieqr) olieq orieq vset-shared-value-new vis-absent refl refl
  = (Env.set-shr{sl} θ sl∈ (SharedVar.new) (Env.shr-vals{sl} θ sl∈ + (δ e'l))) , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (ris-absent S∈ S≡ (depar₁ ieqr') , ( rset-shared-value-new e'l sl∈ sl≡ (depar₂ ieql) , (vis-absent , vset-shared-value-new , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rset-shared-value-new{s = sl} e'l sl∈ sl≡ .(depar₂ ieql)) (remit{S = S} S∈ ¬S≡a .ieqr) olieq orieq vset-shared-value-new vemit refl refl
  = (θo , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e )) , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El) , (depar₂ ieql) , (depar₁ ieqr') , (Erefl , Erefl , (remit S∈ ¬S≡a (depar₁ ieqr') , ( proj₁ res , (vemit , proj₂ res , (_ , refl , refl)))))))
    where
      θ1 = Env.set-shr{sl} θ sl∈ (SharedVar.new) (Env.shr-vals{sl} θ sl∈ + (δ e'l))
      θ2 = Env.set-sig{S} θ S∈ Signal.present
      θo = Env.set-sig{S} θ1 S∈ Signal.present
      e≡ = (ready-maint/irr S S∈ Signal.present e'l)
      get : (typeof e≡) → Σ[ redl ∈ ((ρ θ2 · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₂ ieql) Erefl
      get (e'' , e≡) rewrite e≡ = rset-shared-value-new {s = sl} e'' sl∈ sl≡ (depar₂ ieql) , vset-shared-value-new
      res = get e≡
-- {θ r s e E}
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-new{s = sl}{e} e'l sl∈ sl≡ .(depar₂ ieqr)) (rraise-var e'r .ieql) olieq orieq vset-shared-value-new vraise-var refl refl
      = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ (get e''l,δl≡) , (rset-shared-value-new{θ = θ}{(El ⟦ l ⟧e) ∥ q}{s = sl}{e}{epar₂ (El ⟦ l ⟧e) ∷ Er} e'l sl∈ sl≡ (depar₂ ieqr)
      , (proj₂ (get e''l,δl≡)  , vset-shared-value-new , (_ , refl , refl)))))))
    where
      θo = Env.set-shr{s = sl} θ sl∈ SharedVar.new (shr-vals{s = sl} θ sl∈ + δ e'l)
      ¬s=ready : ¬ (shr-stats{sl} θ sl∈) ≡ SharedVar.ready
      ¬s=ready = λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ()) -- (coherence-of-shr-set* any/env sl sl∈ (depar₂ ieqr) ? )
      e''l,δl≡ = (ready-irr-on-irr-s sl (Env.shr-vals{sl} θ sl∈ + δ e'l) sl∈ ¬s=ready e'r)
      get : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θo · p ∥ (Er ⟦ r ⟧e)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
      get (e'' , e≡) rewrite e≡ = rraise-var e'' (depar₁ ieql') , vraise-var


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rset-shared-value-new{s = sl} e'l sl∈ sl≡ .(depar₂ ieql)) (rif-false{x = x} x∈ x≡ .ieqr) olieq orieq vset-shared-value-new vif-false refl refl
    = (Env.set-shr{s = sl} θ sl∈ SharedVar.new (shr-vals{s = sl} θ sl∈ + δ e'l)
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieql) , (depar₁ ieqr')
      , (Erefl , Erefl
      , (rif-false{x = x} x∈ x≡ (depar₁ ieqr') , rset-shared-value-new e'l sl∈ sl≡ (depar₂ ieql)
      , (vif-false  , vset-shared-value-new , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rset-shared-value-new{s = sl} e'l sl∈ sl≡ .(depar₂ ieql)) (rif-true{x = x} x∈ x≡ .ieqr) olieq orieq vset-shared-value-new vif-true refl refl
   = (Env.set-shr{s = sl} θ sl∈ SharedVar.new (shr-vals{s = sl} θ sl∈ + δ e'l)
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieql) , (depar₁ ieqr')
      , (Erefl , Erefl
      , (rif-true{x = x} x∈ x≡ (depar₁ ieqr') , rset-shared-value-new e'l sl∈ sl≡ (depar₂ ieql)
      , (vif-true , vset-shared-value-new , (_ , refl , refl))))))

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieql) ieqr@(depar₁ ieqr') par (rraise-var{_}{_}{x}{pl}{e}{_} e'l .(depar₂ ieql)) (remit{S = S} S∈ ¬S≡a .ieqr) olieq orieq vraise-var vemit refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieql) , (depar₁ ieqr')
      , (Erefl , Erefl
      , (remit S∈ ¬S≡a (depar₁ ieqr') , proj₁ res
      , (vemit , proj₂ res , (_ , refl , refl))))))
      where
       θo = Env.set-sig{S = S} θ S∈ Signal.present
       e''l,δl≡ = (ready-maint/irr S S∈ Signal.present e'l)
       get : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θo · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieql) Erefl
       get (e'' , e≡) rewrite e≡ = rraise-var e'' (depar₂ ieql) , vraise-var
       res = (get e''l,δl≡)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rraise-var{x = x} e'l .(depar₂ ieqr)) (rset-shared-value-old{s = s} e'r s∈ s≡  .ieql) olieq orieq vraise-var vset-shared-value-old refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rset-shared-value-old{s = s} e'r s∈ s≡ (depar₁ ieql') , proj₁ res
      , (vset-shared-value-old , proj₂ res , (_ , refl , refl))))))
  where
   θo = Env.set-shr{s = s} θ s∈ SharedVar.new (δ e'r)
   ¬s=ready : ¬ (shr-stats{s} θ s∈) ≡ SharedVar.ready
   ¬s=ready = λ x₁ → lookup-s-eq θ s s∈ s∈ x₁ s≡ (λ ()) -- (coherence-of-shr-set* any/env s s∈ (depar₂ ieqr) ? )
   e''l,δl≡ = (ready-irr-on-irr-s s (δ e'r) s∈ ¬s=ready e'l)
   get : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θo · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
   get (e'' , e≡) rewrite e≡ =  rraise-var e'' (depar₂ ieqr)  ,  vraise-var
   res = (get e''l,δl≡)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rraise-var{x = x} e'l .(depar₂ ieqr)) (rset-shared-value-new{s = s} e'r s∈ s≡ .ieql) olieq orieq vraise-var vset-shared-value-new refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rset-shared-value-new{s = s} e'r s∈ s≡ (depar₁ ieql') , proj₁ res
      , (vset-shared-value-new , proj₂ res , (_ , refl , refl))))))
  where
   θo = Env.set-shr{s = s} θ s∈ SharedVar.new ( (Env.shr-vals{s = s} θ s∈) + (δ e'r))
   ¬s=ready : ¬ (shr-stats{s} θ s∈) ≡ SharedVar.ready
   ¬s=ready = λ x₁ → lookup-s-eq θ s s∈ s∈ x₁ s≡ (λ ()) -- (coherence-of-shr-set* any/env s s∈ (depar₂ ieqr) ? )
   e''l,δl≡ = (ready-irr-on-irr-s s ( (Env.shr-vals{s = s} θ s∈) + (δ e'r)) s∈ ¬s=ready e'l)
   get : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θo · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
   get (e'' , e≡) rewrite e≡ =  rraise-var e'' (depar₂ ieqr)  ,  vraise-var
   res = (get e''l,δl≡)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ CBpp@(CBpar cbl cbr BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq)) (depar₂ ieqr) ieql@(depar₁ ieql') par (rraise-var{x = xl}{pl}{e = el} e'l .(depar₂ ieqr)) (rset-var{x = xr}{e = er} xr∈ e'r .ieql) olieq orieq vraise-var vset-var refl refl
 =   (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rset-var xr∈ e'r (depar₁ ieql') , proj₁ res
      , (vset-var , proj₂ res , (_ , refl , refl))))))
    where
     θo = Env.set-var{x = xr} θ xr∈ (δ e'r)

     BV<=,FV<=,CB<= : ∃ (λ BV → ∃ (λ FV → (CorrectBinding (xr ≔ er) BV FV)))
     BV<=,FV<=,CB<= = CBE⟦p⟧=>CBp{E = El}{p = (xr ≔ er)} ( (subst (λ x → CorrectBinding x _ _) (sym (unplug ieql')) cbl) )
     BV<= = (proj₁ BV<=,FV<=,CB<=)
     FV<= = (proj₁ (proj₂ BV<=,FV<=,CB<=))
     CB<= = (proj₂ (proj₂ BV<=,FV<=,CB<=))
     FV<=⊆FVE,BV<=⊆BVE : (FV<= ⊆ _ × BV<= ⊆ _)
     FV<=⊆FVE,BV<=⊆BVE = CBp⊆CBE⟦p⟧ El (xr ≔ er) CB<= (subst (λ x → CorrectBinding x _ _) (sym (unplug ieql')) cbl)
     BV<=⊆BVE = proj₂ FV<=⊆FVE,BV<=⊆BVE
     FV<=⊆FVE = proj₁ FV<=⊆FVE,BV<=⊆BVE

     xr∈FVrf : (typeof CB<=) → (SeqVar.unwrap xr) ∈ Xs FV<=
     xr∈FVrf cb with BV<= | FV<=
     xr∈FVrf CBvset | .([] , [] , []) | FV = here refl
     xr∈FVr = xr∈FVrf CB<=

     BVvar,FVvar,CBvar : ∃ (λ BV → ∃ (λ FV → (CorrectBinding (var xl ≔ el in: pl) BV FV)))
     BVvar,FVvar,CBvar = CBE⟦p⟧=>CBp{E = Er}{p = (var xl ≔ el in: pl)} ( (subst (λ x → CorrectBinding x _ _) (sym (unplug ieqr)) cbr) )
     BVvar = (proj₁ BVvar,FVvar,CBvar)
     FVvar = (proj₁ (proj₂ BVvar,FVvar,CBvar))
     CBvar' = (proj₂ (proj₂ BVvar,FVvar,CBvar))
     FVvar⊆FVE,BVvar⊆BVE : (FVvar ⊆ _ × BVvar ⊆ _)
     FVvar⊆FVE,BVvar⊆BVE = CBp⊆CBE⟦p⟧ Er (var xl ≔ el in: pl) CBvar' (subst (λ x → CorrectBinding x _ _) (sym (unplug ieqr)) cbr)
     BVvar⊆BVE = proj₂ FVvar⊆FVE,BVvar⊆BVE
     FVvar⊆FVE = proj₁ FVvar⊆FVE,BVvar⊆BVE

     FVel⊆FVEf : (typeof CBvar') → (FVₑ el) ⊆ FVvar
     FVel⊆FVEf cb with BVvar | FVvar
     FVel⊆FVEf (CBvar cb) | BV | FV = ∪ˡ ⊆-refl
     FVel⊆FVE = FVel⊆FVEf CBvar'
     -- Xp≠Xq
     xr∉FVel : (SeqVar.unwrap xr) ∉ (Xs (FVₑ el))
     xr∉FVel x = Xp≠Xq _ xr∈FVEl xr∈FVE
       where
        xr∈FVE  = (proj₂ (proj₂ (⊆-trans FVel⊆FVE FVvar⊆FVE))) _ x
        xr∈FVEl =  (proj₂ (proj₂ FV<=⊆FVE)) _ xr∈FVr
     e''l,δl≡ = ready-irr-on-irr-x xr (δ e'r) xr∈ e'l xr∉FVel
     get : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θo · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     get (e'' , e≡) rewrite e≡ = rraise-var e'' (depar₂ ieqr)  ,  vraise-var
     res = (get e''l,δl≡)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xl}{e = el} xl∈ e'l .(depar₂ ieqr)) (ris-present{S = S} S∈ S≡ .ieql) olieq orieq vset-var vis-present refl refl
  =  (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (ris-present S∈ S≡ (depar₁ ieql') , rset-var xl∈ e'l (depar₂ ieqr)
      , (vis-present , vset-var , (_ , refl , refl))))))
    where
     θo = Env.set-var{x = xl} θ xl∈ (δ e'l)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xl}{e = el} xl∈ e'l .(depar₂ ieqr)) (ris-absent S∈ S≡ .ieql) olieq orieq vset-var vis-absent refl refl
  =  (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (ris-absent S∈ S≡ (depar₁ ieql') , rset-var xl∈ e'l (depar₂ ieqr)
      , (vis-absent , vset-var , (_ , refl , refl))))))
    where
     θo = Env.set-var{x = xl} θ xl∈ (δ e'l)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xl}{e = el} xl∈ e'l .(depar₂ ieqr)) (remit{S = S} S∈ ¬S≡a .ieql) olieq orieq vset-var vemit refl refl
  =  (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (remit S∈ ¬S≡a (depar₁ ieql') , proj₁ rett
      , (vemit , proj₂ rett , (_ , refl , refl))))))
    where
     θo = Env.set-var{x = xl} (Env.set-sig{S = S} θ S∈ Signal.present) xl∈ (δ e'l)
     θ2 = (Env.set-sig {S} θ S∈ Signal.present)
     x = (ready-maint/irr S S∈ Signal.present e'l)
     get : (typeof x) → Σ[ redl ∈ ((ρ θ2 · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₂ ieqr) Erefl
     get (e'' , e≡) rewrite e≡ = (rset-var{x = xl} xl∈ e'' (depar₂ ieqr)) , vset-var
     rett = (get x)




ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ CBpp@(CBpar cbl cbr BVp≠BVq FVp≠BVq BVp≠FVq Xp≠Xq)) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xl}{e = el} xl∈ e'l .(depar₂ ieqr)) (rraise-var{x = xr}{pr}{e = er} e'r .ieql) olieq orieq vset-var vraise-var refl refl
 =   (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( proj₁ res , rset-var xl∈ e'l (depar₂ ieqr)
      , ( proj₂ res , vset-var , (_ , refl , refl))))))
    where
     θo = Env.set-var{x = xl} θ xl∈ (δ e'l)

     BV<=,FV<=,CB<= : ∃ (λ BV → ∃ (λ FV → (CorrectBinding (xl ≔ el) BV FV)))
     BV<=,FV<=,CB<= = CBE⟦p⟧=>CBp{E = Er}{p = (xl ≔ el)} ( (subst (λ x → CorrectBinding x _ _) (sym (unplug ieqr)) cbr) )
     BV<= = (proj₁ BV<=,FV<=,CB<=)
     FV<= = (proj₁ (proj₂ BV<=,FV<=,CB<=))
     CB<= = (proj₂ (proj₂ BV<=,FV<=,CB<=))
     FV<=⊆FVE,BV<=⊆BVE : (FV<= ⊆ _ × BV<= ⊆ _)
     FV<=⊆FVE,BV<=⊆BVE = CBp⊆CBE⟦p⟧ Er (xl ≔ el) CB<= (subst (λ x → CorrectBinding x _ _) (sym (unplug ieqr)) cbr)
     BV<=⊆BVE = proj₂ FV<=⊆FVE,BV<=⊆BVE
     FV<=⊆FVE = proj₁ FV<=⊆FVE,BV<=⊆BVE

     xr∈FVlf : (typeof CB<=) → (SeqVar.unwrap xl) ∈ Xs FV<=
     xr∈FVlf cb with BV<= | FV<=
     xr∈FVlf CBvset | .([] , [] , []) | FV = here refl
     xr∈FVl = xr∈FVlf CB<=

     BVvar,FVvar,CBvar : ∃ (λ BV → ∃ (λ FV → (CorrectBinding (var xr ≔ er in: pr) BV FV)))
     BVvar,FVvar,CBvar = CBE⟦p⟧=>CBp{E = El}{p = (var xr ≔ er in: pr)} ( (subst (λ x → CorrectBinding x _ _) (sym (unplug ieql')) cbl) )
     BVvar = (proj₁ BVvar,FVvar,CBvar)
     FVvar = (proj₁ (proj₂ BVvar,FVvar,CBvar))
     CBvar' = (proj₂ (proj₂ BVvar,FVvar,CBvar))
     FVvar⊆FVE,BVvar⊆BVE : (FVvar ⊆ _ × BVvar ⊆ _)
     FVvar⊆FVE,BVvar⊆BVE = CBp⊆CBE⟦p⟧ El (var xr ≔ er in: pr) CBvar' (subst (λ x → CorrectBinding x _ _) (sym (unplug ieql')) cbl)
     BVvar⊆BVE = proj₂ FVvar⊆FVE,BVvar⊆BVE
     FVvar⊆FVE = proj₁ FVvar⊆FVE,BVvar⊆BVE

     FVel⊆FVEf : (typeof CBvar') → (FVₑ er) ⊆ FVvar
     FVel⊆FVEf cb with BVvar | FVvar
     FVel⊆FVEf (CBvar cb) | BV | FV = ∪ˡ ⊆-refl
     FVel⊆FVE = FVel⊆FVEf CBvar'
     -- Xp≠Xq
     xr∉FVer : (SeqVar.unwrap xl) ∉ (Xs (FVₑ er))
     xr∉FVer x =  Xp≠Xq _ xr∈FVE xr∈FVEl
       where
        xr∈FVE  = (proj₂ (proj₂ (⊆-trans FVel⊆FVE FVvar⊆FVE))) _ x
        xr∈FVEl =  (proj₂ (proj₂ FV<=⊆FVE)) _ xr∈FVl
     e''r,δr≡ = ready-irr-on-irr-x xl (δ e'l) xl∈ e'r xr∉FVer
     get : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θo · (p ∥ (Er ⟦ r ⟧e))) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
     get (e'' , e≡) rewrite e≡ = rraise-var e'' (depar₁ ieql')  ,  vraise-var
     res = (get e''r,δr≡)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-true a b .(depar₂ ieqr)) (remit{S = S} S∈ ¬S≡a .ieql) olieq orieq vif-true vemit refl refl
 =   ((Env.set-sig{S = S} θ S∈ Signal.present)
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( remit S∈ ¬S≡a (depar₁ ieql') , rif-true a b (depar₂ ieqr)
      , ( vemit , vif-true , (_ , refl , refl))))))

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-false a b .(depar₂ ieqr)) (remit{S = S} S∈ ¬S≡a .ieql) olieq orieq vif-false vemit refl refl
  = ((Env.set-sig{S = S} θ S∈ Signal.present)
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( remit S∈ ¬S≡a (depar₁ ieql') , rif-false a b (depar₂ ieqr)
      , ( vemit , vif-false , (_ , refl , refl))))))

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂{r = .(sr ⇐ er)} ieqr) ieql@(depar₁{r = .(xl ≔ el)} ieql') par (rset-shared-value-new{s = sr}{e = er} e'r sr∈ sr≡ .(depar₂ ieqr)) (rset-var{x = xl}{e = el} xl∈ e'l .ieql) olieq orieq vset-shared-value-new vset-var refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (.((xl ≔ el) ∥ (sr ⇐ er)) , BVo , FVo) , (CBpar{FVp = FV≔}{FVq = FV<=} cb≔@(CBvset{.xl}{.el}) cb<=@(CBsset{.sr}{.er})  BV≔≠BV<= FV≔≠BV<= BV≔≠FV<- X≔≠X<=) , refl
     = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , proj₁ resr
      , (proj₂ resl  , proj₂ resr , (_ , refl , refl))))))
      where
        θr = Env.set-shr{s = sr} θ sr∈ SharedVar.new (shr-vals{s = sr} θ sr∈ + δ e'r)
        θl = Env.set-var{x = xl} θ xl∈ (δ e'l)
        -- θo = Env.set-shr{s = sr} θl sr∈ SharedVar.new (shr-vals{s = sr} θ sr∈ + δ e'r)
        θo = Env.set-var{x = xl} θr xl∈ (δ e'l)
        xl∈FVel = ((SeqVar.unwrap xl) ∈ (Xs FV≔)) ∋ here refl
        xl∉FVer : (SeqVar.unwrap xl) ∉ (Xs (FVₑ er))
        xl∉FVer = X≔≠X<= _ xl∈FVel
        ¬sl≡ready : ¬ (Env.shr-stats {sr} θ sr∈ ≡ SharedVar.ready)
        ¬sl≡ready = λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())
        e''r,δr≡ = ready-irr-on-irr-x xl (δ e'l) xl∈ e'r xl∉FVer
        e''l,δl≡ = ready-irr-on-irr-s sr (shr-vals{s = sr} θ sr∈ + δ e'r) sr∈ ¬sl≡ready e'l

        getr : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θl · ((El ⟦ l ⟧e ) ∥ q)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
        getr (e'' , e≡) rewrite e≡ = rset-shared-value-new e'' sr∈ sr≡ (depar₂ ieqr) , vset-shared-value-new
        resr = getr e''r,δr≡


        getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · (p ∥ (Er ⟦ r ⟧e))) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
        getl (e'' , e≡) rewrite e≡ =  rset-var{x = xl} xl∈ e'' (depar₁ ieql')  , vset-var
        resl = getl e''l,δl≡

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xr}{e = er} xr∈ e'r .(depar₂ ieqr)) (rif-false{p = pt}{q = pf}{x = xl} xl∈ xl≡ .ieql) olieq orieq vset-var vif-false refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (  o , BVo , FVo ) , (CBpar{FVp = FVif}{FVq = FV≔} cbif@(CBif _ _) cb≔@CBvset BVif≠BV≔ FVif≠BV≔ BVif≠FV≔ Xif≠X≔) , refl
      = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ res , rset-var xr∈ e'r (depar₂ ieqr)
      , (proj₂ res , vset-var , (_ , refl , refl))))))
    where
      θo = Env.set-var{x = xr} θ xr∈ (δ e'r)
      xr∈XsFV≔ = ((SeqVar.unwrap xr) ∈ (Xs FV≔)) ∋ here refl
      xl∈XsFVif = ((SeqVar.unwrap xl) ∈ (Xs FVif)) ∋ here refl
      ¬xl≡xr : ¬ xl ≡ xr
      ¬xl≡xr refl = Xif≠X≔ _ xl∈XsFVif xr∈XsFV≔
      xl∈2 = (seq-set-mono'{xl}{xr}{θ}{δ e'r}{xr∈} xl∈)
      θ≡xl = seq-putputget {xl} {xr}{θ}{0}{δ e'r} ¬xl≡xr xl∈ xr∈ xl∈2 xl≡
      res : Σ[ redr ∈ ((ρ θo · (p ∥ (Er ⟦ r ⟧e))) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
      res = rif-false xl∈2 θ≡xl (depar₁ ieql')  , vif-false



ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xr}{e = er} xr∈ e'r .(depar₂ ieqr)) (rif-true{x = xl} xl∈ xl≡ .ieql) olieq orieq vset-var vif-true refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (  o , BVo , FVo ) , (CBpar{FVp = FVif}{FVq = FV≔} cbif@(CBif _ _) cb≔@CBvset BVif≠BV≔ FVif≠BV≔ BVif≠FV≔ Xif≠X≔) , refl
      = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ res , rset-var xr∈ e'r (depar₂ ieqr)
      , (proj₂ res , vset-var , (_ , refl , refl))))))
    where
      θo = Env.set-var{x = xr} θ xr∈ (δ e'r)
      xr∈XsFV≔ = ((SeqVar.unwrap xr) ∈ (Xs FV≔)) ∋ here refl
      xl∈XsFVif = ((SeqVar.unwrap xl) ∈ (Xs FVif)) ∋ here refl
      ¬xl≡xr : ¬ xl ≡ xr
      ¬xl≡xr refl = Xif≠X≔ _ xl∈XsFVif xr∈XsFV≔
      xl∈2 = (seq-set-mono'{xl}{xr}{θ}{δ e'r}{xr∈} xl∈)
      θ≡xl = seq-putputget {xl} {xr}{θ}{_}{δ e'r} ¬xl≡xr xl∈ xr∈ xl∈2 xl≡
      res : Σ[ redr ∈ ((ρ θo · (p ∥ (Er ⟦ r ⟧e))) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
      res = rif-true xl∈2 θ≡xl (depar₁ ieql')  , vif-true

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xr}{e = er} xr∈ e'r .(depar₂ ieqr)) (rraise-shared{e = el} e'l .ieql) olieq orieq vset-var vraise-shared refl refl
   with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... |  ( o , BVo , FVo ) , (CBpar{FVq = FV≔} cbr@(CBshared _) cb≔@CBvset BVr≠BV≔ FVr≠BV≔ BVr≠FV≔ Xr≠X≔) , refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , rset-var xr∈ e'r (depar₂ ieqr)
      , (proj₂ resl , vset-var , (_ , refl , refl))))))
  where
    θo = Env.set-var{x = xr} θ xr∈ (δ e'r)
    xr∈Fv≔ : (SeqVar.unwrap xr) ∈ (Xs FV≔)
    xr∈Fv≔ = here refl
    xr∉FVel : (SeqVar.unwrap xr) ∉ (Xs (FVₑ el))
    xr∉FVel x = Xr≠X≔ _ (++ˡ x) xr∈Fv≔
    e''l,δl≡ = ready-irr-on-irr-x xr (δ e'r) xr∈ e'l xr∉FVel
    getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θo · (p ∥ (Er ⟦ r ⟧e))) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
    getl (e'' , e≡) rewrite e≡ = (rraise-shared e'' (depar₁ ieql')) , vraise-shared
    resl = (getl e''l,δl≡)


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xr}{e = er} xr∈ e'r .(depar₂ ieqr)) (rset-shared-value-old{s = sl}{e = el} e'l sl∈ sl≡ .ieql) olieq orieq vset-var vset-shared-value-old  refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (o , BVo , FVo) , (CBpar{FVp = FV<=}{FVq = FV≔} cb≔@(CBsset) cb<=@(CBvset)  BV≔≠BV<= FV≔≠BV<= BV≔≠FV<- X≔≠X<=) , refl
     = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , proj₁ resr
      , (proj₂ resl  , proj₂ resr , (_ , refl , refl))))))
      where
        θl = Env.set-shr{s = sl} θ sl∈ SharedVar.new (δ e'l)
        θr = Env.set-var{x = xr} θ xr∈ (δ e'r)
        -- θo = Env.set-shr{s = sr} θl sr∈ SharedVar.new (shr-vals{s = sr} θ sr∈ + δ e'r)
        θo = Env.set-var{x = xr} θl xr∈ (δ e'r)
        xr∈FVer = ((SeqVar.unwrap xr) ∈ (Xs FV≔)) ∋ here refl
        xr∉FVel : (SeqVar.unwrap xr) ∉ (Xs (FVₑ el))
        xr∉FVel x = X≔≠X<= _ x xr∈FVer
        ¬sl≡ready : ¬ (Env.shr-stats {sl} θ sl∈ ≡ SharedVar.ready)
        ¬sl≡ready = λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ())
        e''l,δl≡ = ready-irr-on-irr-x xr (δ e'r) xr∈ e'l xr∉FVel
        e''r,δr≡ = ready-irr-on-irr-s sl (δ e'l) sl∈ ¬sl≡ready e'r

        getr : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θl · ((El ⟦ l ⟧e ) ∥ q)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
        getr (e'' , e≡) rewrite e≡ = (rset-var xr∈ e'' (depar₂ ieqr)) , vset-var
        resr = getr e''r,δr≡


        getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · (p ∥ (Er ⟦ r ⟧e))) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
        getl (e'' , e≡) rewrite e≡ = (rset-shared-value-old e'' sl∈ sl≡ (depar₁ ieql')) , vset-shared-value-old
        resl = getl e''l,δl≡
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}   (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xr}{e = er} xr∈ e'r .(depar₂ ieqr)) (rset-shared-value-new{s = sl}{e = el} e'l sl∈ sl≡ .ieql) olieq orieq vset-var vset-shared-value-new refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (o , BVo , FVo) , (CBpar{FVp = FV<=}{FVq = FV≔} cb≔@(CBsset) cb<=@(CBvset)  BV≔≠BV<= FV≔≠BV<= BV≔≠FV<- X≔≠X<=) , refl
     = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , proj₁ resr
      , (proj₂ resl  , proj₂ resr , (_ , refl , refl))))))
      where
        θl = Env.set-shr{s = sl} θ sl∈ SharedVar.new (Env.shr-vals{s = sl} θ sl∈ + δ e'l)
        θr = Env.set-var{x = xr} θ xr∈ (δ e'r)
        -- θo = Env.set-shr{s = sr} θl sr∈ SharedVar.new (shr-vals{s = sr} θ sr∈ + δ e'r)
        θo = Env.set-var{x = xr} θl xr∈ (δ e'r)
        xr∈FVer = ((SeqVar.unwrap xr) ∈ (Xs FV≔)) ∋ here refl
        xr∉FVel : (SeqVar.unwrap xr) ∉ (Xs (FVₑ el))
        xr∉FVel x = X≔≠X<= _ x xr∈FVer
        ¬sl≡ready : ¬ (Env.shr-stats {sl} θ sl∈ ≡ SharedVar.ready)
        ¬sl≡ready = λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ())
        e''l,δl≡ = ready-irr-on-irr-x xr (δ e'r) xr∈ e'l xr∉FVel
        e''r,δr≡ = ready-irr-on-irr-s sl (Env.shr-vals{s = sl} θ sl∈ + δ e'l) sl∈ ¬sl≡ready e'r

        getr : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θl · ((El ⟦ l ⟧e ) ∥ q)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
        getr (e'' , e≡) rewrite e≡ = (rset-var xr∈ e'' (depar₂ ieqr)) , vset-var
        resr = getr e''r,δr≡

        getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · (p ∥ (Er ⟦ r ⟧e))) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
        getl (e'' , e≡) rewrite e≡ = (rset-shared-value-new e'' sl∈ sl≡ (depar₁ ieql')) , vset-shared-value-new
        resl = getl e''l,δl≡

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-false{x = xr} xr∈ xr≡ .(depar₂ ieqr)) (rset-shared-value-old{s = sl} e'l sl∈ sl≡ .ieql) olieq orieq vif-false vset-shared-value-old refl refl
  = (Env.set-shr{s = sl} θ sl∈ SharedVar.new (δ e'l)
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rset-shared-value-old e'l sl∈ sl≡ (depar₁ ieql') , rif-false xr∈ xr≡ (depar₂ ieqr)
      , (vset-shared-value-old , vif-false , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-false{x = xr} xr∈ xr≡ .(depar₂ ieqr)) (rset-shared-value-new{s = sl} e'l sl∈ sl≡ .ieql) olieq orieq vif-false vset-shared-value-new refl refl
  = (Env.set-shr{s = sl} θ sl∈ SharedVar.new (Env.shr-vals{s = sl} θ sl∈ + δ e'l)
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rset-shared-value-new e'l sl∈ sl≡ (depar₁ ieql') , rif-false xr∈ xr≡ (depar₂ ieqr)
      , (vset-shared-value-new , vif-false , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-true {x = xr} xr∈ xr≡ .(depar₂ ieqr)) (rset-shared-value-old{s = sl} e'l sl∈ sl≡ .ieql) olieq orieq vif-true vset-shared-value-old refl refl
  = (Env.set-shr{s = sl} θ sl∈ SharedVar.new (δ e'l)
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rset-shared-value-old e'l sl∈ sl≡ (depar₁ ieql') , rif-true xr∈ xr≡ (depar₂ ieqr)
      , (vset-shared-value-old , vif-true , (_ , refl , refl))))))
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-true {x = xr} xr∈ xr≡ .(depar₂ ieqr)) (rset-shared-value-new{s = sl} e'l sl∈ sl≡ .ieql) olieq orieq vif-true vset-shared-value-new refl refl
  = (Env.set-shr{s = sl} θ sl∈ SharedVar.new (Env.shr-vals{s = sl} θ sl∈ + δ e'l)
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rset-shared-value-new e'l sl∈ sl≡ (depar₁ ieql') , rif-true xr∈ xr≡ (depar₂ ieqr)
      , (vset-shared-value-new , vif-true , (_ , refl , refl))))))

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = xr}{e = er} xr∈ e'r .(depar₂ ieqr)) (rset-var{x = xl}{e = el} xl∈ e'l .ieql) olieq orieq vset-var vset-var refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (o , BVo , FVo) , (CBpar{p = .(xl ≔ el)}{q = .(xr ≔ er)}{FVp = FVl}{FVq = FVr} cb≔@(CBvset) cb<=@(CBvset)  BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr , (_ , refl , refl))))))
      where
        θl = Env.set-var{x = xl} θ xl∈ (δ e'l)
        θr = Env.set-var{x = xr} θ xr∈ (δ e'r)
        xr∈2 = (seq-set-mono'{xr}{xl}{θ}{δ e'l}{x'∈ = xl∈} xr∈)
        xl∈2 = (seq-set-mono'{xl}{xr}{θ}{δ e'r}{x'∈ = xr∈} xl∈)
        θo = Env.set-var{x = xr} θl xr∈2 (δ e'r)
        θo2 = Env.set-var{x = xl} θr xl∈2  (δ e'l)
        xl∈FVl = ((SeqVar.unwrap xl) ∈ (Xs FVl)) ∋ (here refl)
        xr∈FVr = ((SeqVar.unwrap xr) ∈ (Xs FVr)) ∋ (here refl)
        xr∉FVl = ((SeqVar.unwrap xr) ∉ (Xs FVl)) ∋ (dist'-sym Xl≠Xr) _ xr∈FVr
        xl∉FVr = ((SeqVar.unwrap xl) ∉ (Xs FVr)) ∋ Xl≠Xr _ xl∈FVl
        ¬xl≡xr = (¬ xl ≡ xr) ∋ (λ {refl → xl∉FVr xr∈FVr})
        e''l,δl≡ = ready-irr-on-irr-x xr (δ e'r) xr∈ e'l (xr∉FVl ∘ there)
        e''r,δr≡ = ready-irr-on-irr-x xl (δ e'l) xl∈ e'r (xl∉FVr ∘ there)
        {-

seq-set-comm : ∀ θ x1 x2 n1 n2 → (x1∈ : isVar∈ x1 θ) → (x2∈ : isVar∈ x2 θ)
               → ¬ x1 ≡ x2 → ∃ λ x1∈' → ∃ λ x2∈'
               → (set-var{x2} (set-var{x1} θ x1∈ n1) x2∈' n2) ≡ (set-var{x1} (set-var{x2} θ x2∈ n2) x1∈' n1)
-}
        getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · (p ∥ (Er ⟦ r ⟧e))) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
        getl (e'' , e≡) rewrite e≡ with seq-set-comm θ xr xl (δ e'r) (δ e'') xr∈ xl∈ (¬xl≡xr ∘ sym)
        ... | (_ , xl∈2 , eq) rewrite sym eq = ( rset-var xl∈2 e'' (depar₁ ieql') , vset-var )

        getr : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θl · ((El ⟦ l ⟧e) ∥ q)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
        getr (e'' , e≡) rewrite e≡ = rset-var xr∈2 e'' (depar₂ ieqr) , vset-var

        resl = getl e''l,δl≡
        resr = getr e''r,δr≡





ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-false{x = xr} xr∈ xr≡ .(depar₂ ieqr)) (rset-var{x = xl}{e = el} xl∈ e'l .ieql) olieq orieq vif-false vset-var refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (  o , BVo , FVo ) , (CBpar{FVp = FV≔}{FVq = FVif} cb≔@CBvset cbif@(CBif _ _) BV≔≠BV FV≔≠BVif BV≔≠FVif X≔≠Xif) , refl
      = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( rset-var xl∈ e'l (depar₁ ieql') , proj₁ res
      , ( vset-var , proj₂ res , (_ , refl , refl) )))))
    where
      θo = Env.set-var{x = xl} θ xl∈ (δ e'l)
      xl∈XsFV≔ = ((SeqVar.unwrap xl) ∈ (Xs FV≔)) ∋ here refl
      xr∈XsFVif = ((SeqVar.unwrap xr) ∈ (Xs FVif)) ∋ here refl
      ¬xl≡xr : ¬ xl ≡ xr
      ¬xl≡xr refl = X≔≠Xif _ xl∈XsFV≔ xr∈XsFVif
      xr∈2 = (seq-set-mono'{xr}{xl}{θ}{δ e'l}{xl∈} xr∈)
      θ≡xr = seq-putputget {xr} {xl}{θ}{0}{δ e'l} (¬xl≡xr ∘ sym) xr∈ xl∈ xr∈2 xr≡
      res : Σ[ redr ∈ ((ρ θo · ((El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
      res = rif-false xr∈2 θ≡xr (depar₂ ieqr)  , vif-false

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-true{x = xr} xr∈ xr≡ .(depar₂ ieqr)) (rset-var{x = xl}{e = el} xl∈ e'l .ieql) olieq orieq vif-true vset-var refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (  o , BVo , FVo ) , (CBpar{FVp = FV≔}{FVq = FVif} cb≔@CBvset cbif@(CBif _ _) BV≔≠BV FV≔≠BVif BV≔≠FVif X≔≠Xif) , refl
      = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( rset-var xl∈ e'l (depar₁ ieql') , proj₁ res
      , ( vset-var , proj₂ res , (_ , refl , refl) )))))
    where
      θo = Env.set-var{x = xl} θ xl∈ (δ e'l)
      xl∈XsFV≔ = ((SeqVar.unwrap xl) ∈ (Xs FV≔)) ∋ here refl
      xr∈XsFVif = ((SeqVar.unwrap xr) ∈ (Xs FVif)) ∋ here refl
      ¬xl≡xr : ¬ xl ≡ xr
      ¬xl≡xr refl = X≔≠Xif _ xl∈XsFV≔ xr∈XsFVif
      xr∈2 = (seq-set-mono'{xr}{xl}{θ}{δ e'l}{xl∈} xr∈)
      θ≡xr = seq-putputget {xr} {xl}{θ}{_}{δ e'l} (¬xl≡xr ∘ sym) xr∈ xl∈ xr∈2 xr≡
      res : Σ[ redr ∈ ((ρ θo · ((El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
      res = rif-true xr∈2 θ≡xr (depar₂ ieqr)  , vif-true

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}  (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rraise-shared{s = sr} e'r .(depar₂ ieqr)) (rset-shared-value-old{s = sl} e'l sl∈ sl≡ .ieql) olieq orieq vraise-shared vset-shared-value-old refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (  o , BVo , FVo ) , (CBpar{FVp = FV<=} cb<=@(CBsset) cbr BV<=≠BVr FV<=≠BVr BV<=≠FVr X<=≠Xr) , refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( rset-shared-value-old e'l sl∈ sl≡ (depar₁ ieql') , proj₁ res
      , ( vset-shared-value-old , proj₂ res , (_ , refl , refl) )))))
      where
        θo = Env.set-shr{s = sl} θ sl∈ SharedVar.new (δ e'l)
        e''r,δr≡ = ready-irr-on-irr-s sl (δ e'l) sl∈ (λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ())) e'r
        res :  Σ[ redr ∈ ((ρ θo · ((El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
        res rewrite proj₂ e''r,δr≡ = (rraise-shared
                                        (ready-maint-s _ (δ e'l) sl∈
                                         (λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ())) e'r)
                                        (depar₂ ieqr)) , vraise-shared

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}  (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rraise-shared e'r .(depar₂ ieqr)) (rset-shared-value-new{s = sl} e'l sl∈ sl≡ .ieql) olieq orieq vraise-shared vset-shared-value-new refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (  o , BVo , FVo ) , (CBpar{FVp = FV<=} cb<=@(CBsset) cbr BV<=≠BVr FV<=≠BVr BV<=≠FVr X<=≠Xr) , refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( rset-shared-value-new e'l sl∈ sl≡ (depar₁ ieql') , proj₁ res
      , ( vset-shared-value-new , proj₂ res , (_ , refl , refl) )))))
      where
        θo = Env.set-shr{s = sl} θ sl∈ SharedVar.new (Env.shr-vals{s = sl} θ sl∈ + δ e'l)
        e''r,δr≡ = ready-irr-on-irr-s sl (Env.shr-vals{s = sl} θ sl∈ + δ e'l) sl∈ (λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ())) e'r
        res :  Σ[ redr ∈ ((ρ θo · ((El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
        res rewrite proj₂ e''r,δr≡ = rraise-shared (proj₁ e''r,δr≡) (depar₂ ieqr) , vraise-shared
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}  (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rraise-shared{e = er} e'r .(depar₂ ieqr)) (rset-var{x = xl}{e = el} xl∈ e'l .ieql) olieq orieq vraise-shared vset-var refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (  o , BVo , FVo ) , (CBpar{FVp = FV≔} cb≔@(CBvset) cbr@(CBshared _) BV≔≠BVr FV≔≠BVr BV≔≠FVr X≔≠Xr) , refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( rset-var xl∈ e'l (depar₁ ieql') , proj₁ res
      , ( vset-var , proj₂ res , (_ , refl , refl) )))))
   where
     θo = Env.set-var{x = xl} θ xl∈ (δ e'l)
     xl∈FVel = ((SeqVar.unwrap xl) ∈ (Xs FV≔)) ∋ here refl
     e''r,δr≡ = ready-irr-on-irr-x xl (δ e'l) xl∈ e'r ((X≔≠Xr _ xl∈FVel) ∘ ++ˡ)
     res :  Σ[ redr ∈ ((ρ θo · ((El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     res rewrite proj₂ e''r,δr≡ = (rraise-shared (proj₁ e''r,δr≡) (depar₂ ieqr)) , vraise-shared
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}  cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-old{s = sr} e'r sr∈ sr≡ .(depar₂ ieqr)) (rraise-shared{e = el} e'l .ieql) olieq orieq vset-shared-value-old vraise-shared refl refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( proj₁ res , rset-shared-value-old e'r sr∈ sr≡ (depar₂ ieqr)
      , ( proj₂ res , vset-shared-value-old , (_ , refl , refl) )))))
  where
   θo = Env.set-shr{s = sr} θ sr∈ SharedVar.new (δ e'r)
   e''l,δl≡ = ready-irr-on-irr-s sr (δ e'r) sr∈ (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l
   res :  Σ[ redr ∈ ((ρ θo · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
   res rewrite proj₂ e''l,δl≡ = (rraise-shared
                                   (ready-maint-s sr (δ e'r) sr∈
                                    (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l)
                                   (depar₁ ieql')) , vraise-shared


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}  cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-old{s = sr} e'r sr∈ sr≡ .(depar₂ ieqr)) (rraise-var{e = el} e'l .ieql) olieq orieq vset-shared-value-old vraise-var refl refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( proj₁ res , rset-shared-value-old e'r sr∈ sr≡ (depar₂ ieqr)
      , ( proj₂ res , vset-shared-value-old , (_ , refl , refl) )))))
    where
      θo = Env.set-shr{s = sr} θ sr∈ SharedVar.new (δ e'r)
      e''l,δl≡ = ready-irr-on-irr-s sr (δ e'r) sr∈ (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l
      res : Σ[ redr ∈ ((ρ θo · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
      res rewrite proj₂ e''l,δl≡ = (rraise-var
                                      (ready-maint-s sr (δ e'r) sr∈
                                       (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l)
                                      (depar₁ ieql')) , vraise-var

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-new{s = sr} e'r sr∈ sr≡ .(depar₂ ieqr)) (rraise-shared e'l .ieql) olieq orieq vset-shared-value-new vraise-shared refl refl
     = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( proj₁ res , rset-shared-value-new e'r sr∈ sr≡ (depar₂ ieqr)
      , ( proj₂ res , vset-shared-value-new , (_ , refl , refl) )))))
    where
      nn = (Env.shr-vals{s = sr} θ sr∈ + δ e'r)
      θo = Env.set-shr{s = sr} θ sr∈ SharedVar.new nn
      e''l,δl≡ = ready-irr-on-irr-s sr nn sr∈ (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l
      res : Σ[ redr ∈ ((ρ θo · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
      res rewrite proj₂ e''l,δl≡ = (rraise-shared
                                      (ready-maint-s sr nn sr∈
                                       (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l)
                                      (depar₁ ieql')) , vraise-shared

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}  (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-old{s = sr}{e = er} e'r sr∈ sr≡ .(depar₂ ieqr)) (rset-var{x = xl}{e = el} xl∈ e'l .ieql) olieq orieq vset-shared-value-old vset-var refl refl
  with inspecting-cb-distinct-double-unplug cb ieql' ieqr
... | (  o , BVo , FVo ) , (CBpar{FVp = FV:=}{FVq = FV<=} cb:=@(CBvset) cb<=@(CBsset) BV:=≠BV<= FV:=≠BV<= BV:=≠FV<= X:=≠X<=) , refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , ( proj₁ resl , proj₁ resr
      , ( proj₂ resl , proj₂ resr , (_ , refl , refl) )))))
    where
      θr = Env.set-shr{s = sr} θ sr∈ SharedVar.new (δ e'r)
      θl = Env.set-var{x = xl} θ xl∈ (δ e'l)
      θo = Env.set-var{x = xl} θr xl∈ (δ e'l)
      xl∉FVer = ((SeqVar.unwrap xl) ∉ (Xs (FVₑ er))) ∋ X:=≠X<= _ (here refl)
      ¬sr≡ready = (¬ (Env.shr-stats{s = sr} θ sr∈) ≡ SharedVar.ready) ∋ λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())
      e''l,δl≡ = ready-irr-on-irr-s sr (δ e'r) sr∈ ¬sr≡ready e'l
      e''r,δr≡ = ready-irr-on-irr-x xl (δ e'l) xl∈ e'r xl∉FVer
      resl : Σ[ redr ∈ ((ρ θr · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
      resl rewrite proj₂ e''l,δl≡ = (rset-var xl∈
                                       (ready-maint-s _ (δ e'r) sr∈
                                        (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l)
                                       (depar₁ ieql')) , vset-var

      resr : Σ[ redr ∈ ((ρ θl · ( (El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
      resr rewrite proj₂ e''r,δr≡ = (rset-shared-value-old (proj₁ e''r,δr≡) sr∈ sr≡ (depar₂ ieqr)) , vset-shared-value-old

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-new{s = sr}{e = er} e'r sr∈ sr≡ .(depar₂ ieqr)) (rset-shared-value-new{s = sl}{e = el} e'l sl∈ sl≡ .ieql) olieq orieq vset-shared-value-new vset-shared-value-new refl refl
  with sl SharedVar.≟ sr
... | yes sl≡sr rewrite sl≡sr | shr∈-eq{sr}{θ} sl∈ sr∈
    = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ l-res , (proj₁ r-res
      , (proj₂ l-res , proj₂ r-res , (_ , refl , refl)))))))
    where
      s = sr
      s∈ = sr∈
      ¬s=ready : ¬ (shr-stats{s} θ s∈) ≡ SharedVar.ready
      ¬s=ready = λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ()) -- coherence-of-shr-set* any/env s s∈ (depar₂ ieqr)
      e''l,δl≡ = ready-irr-on-irr-s s (Env.shr-vals{s} θ s∈ + δ e'r) s∈ ¬s=ready e'l
      e''r,δr≡ = ready-irr-on-irr-s s (Env.shr-vals{s} θ s∈ + δ e'l) s∈ ¬s=ready e'r

      θl  = Env.set-shr{s} θ sl∈ SharedVar.new (Env.shr-vals{s} θ s∈ + δ e'l)
      s∈2 = (shr-set-mono'{s}{s}{θ}{s'∈ = s∈} s∈)
      θo  = Env.set-shr{s} θl s∈2 SharedVar.new (Env.shr-vals{s} θl ((shr-set-mono'{s}{s}{θ}{s'∈ = s∈} s∈)) + δ e'r)

      getr : (typeof e''r,δr≡) → Σ[ redl ∈ ((ρ θl · (El ⟦ l ⟧e) ∥ q) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redl (depar₂ ieqr) Erefl
      getr (e'' , e≡) rewrite e≡
         = (rset-shared-value-new{θl} {s = s}{E = epar₂ (El ⟦ l ⟧e) ∷ Er} e'' s∈2 (proj₁ (Env.shr-putget{s}{θ}{SharedVar.new} s∈ s∈2)) (depar₂ ieqr))
           , vset-shared-value-new
      r-res = (getr e''r,δr≡)

      s∈22 = (shr-set-mono'{s}{s}{θ}{s'∈ = s∈} s∈)
      θr = Env.set-shr{s} θ sl∈ SharedVar.new (Env.shr-vals{s} θ s∈ + δ e'r)
      θo2 = Env.set-shr{s} θr s∈22 SharedVar.new (Env.shr-vals{s} θr (s∈22) + δ e'l)

      getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · p ∥ (Er ⟦ r ⟧e)) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
      getl (e'' , e≡) rewrite (shr-putput-overwrite s θ SharedVar.new (Env.shr-vals{s} θ s∈ + δ e'l)
                                                       SharedVar.new (Env.shr-vals{s} θl s∈2 + δ e'r)
                                                       s∈ s∈2)
                            | sym (shr-putput-overwrite s θ SharedVar.new (Env.shr-vals{s} θ s∈ + δ e'r)
                                                       SharedVar.new (Env.shr-vals{s} θr s∈22 + δ e'l)
                                                       s∈ s∈22)
                            | sym (shr-putput-overwrite s θ SharedVar.new (Env.shr-vals{s} θ s∈ + δ e'r)
                                                        SharedVar.new (Env.shr-vals{s} θr s∈22 + δ e'')
                                                        s∈ s∈22)

                            | proj₂ (shr-putget {s}{θ}{SharedVar.new}{(Env.shr-vals{s} θ s∈ + δ e'l)} s∈ s∈2)
                            | e≡
                            | +-assoc (Env.shr-vals{s} θ s∈) (δ e'') (δ e'r)
                            | +-comm (δ e'') (δ e'r)
                            | sym (+-assoc (Env.shr-vals{s} θ s∈) (δ e'r) (δ e''))
                            with red
                               | (->E-view red (depar₁ ieql') Erefl) ∋ vset-shared-value-new
                             where red = rset-shared-value-new{θr}{p ∥ (Er ⟦ r ⟧e)}{s = s}{E = epar₁ (Er ⟦ r ⟧e) ∷ El} e'' s∈22 (proj₁ (Env.shr-putget{s}{θ}{SharedVar.new} s∈ s∈22)) (depar₁ ieql')
      ... | red | view
                rewrite (proj₂ (shr-putget {s}{θ}{SharedVar.new}{(Env.shr-vals{s} θ s∈ + δ e'r)} s∈ s∈22))
                      | (shr-putput-overwrite s θ SharedVar.new (Env.shr-vals{s} θ s∈ + δ e'r)
                                              SharedVar.new (Env.shr-vals{s} θ s∈ + δ e'r + δ e'')
                                              s∈ s∈22)
        =  red , view

      l-res = (getl e''l,δl≡)

... | no ¬sl≡sr = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , (proj₁ resr
      , (proj₂ resl , proj₂ resr , (_ , refl , refl)))))))
  where
    nl = (Env.shr-vals{sl} θ sl∈ + δ e'l)
    nr = (Env.shr-vals{sr} θ sr∈ + δ e'r)
    θl = Env.set-shr{sl} θ sl∈ SharedVar.new nl
    θr = Env.set-shr{sr} θ sr∈ SharedVar.new nr

    sl∈2 = shr-set-mono'{sl}{sr}{θ}{SharedVar.new}{nr}{sr∈} sl∈
    sr∈2 = shr-set-mono'{sr}{sl}{θ}{SharedVar.new}{nl}{sl∈} sr∈
    θo   = Env.set-shr{sr} θl sr∈2 SharedVar.new nr
    e''l,δl≡ = ready-irr-on-irr-s sr nr sr∈ (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l
    e''r,δr≡ = ready-irr-on-irr-s sl nl sl∈ (λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ())) e'r
    getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
    getl (e'' , e≡) with shr-set-comm θ sl sr SharedVar.new nl SharedVar.new nr sl∈ sr∈ ¬sl≡sr
    ... | (_ , _ , θ≡)  rewrite θ≡ with shr-putputget {sl}{sr}{θ}{_}{Env.shr-vals{sl} θ sl∈}{SharedVar.new}{nr} ¬sl≡sr sl∈ sr∈ sl∈2 sl≡ refl
    ... | (eq1 , eq2) rewrite e≡ | sym eq2
           = rset-shared-value-new e'' sl∈2 eq1 (depar₁ ieql') , vset-shared-value-new
    resl = (getl e''l,δl≡)

    getr : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θl · ( (El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
    getr (e''r , δr≡) rewrite δr≡ with shr-putputget {sr}{sl}{θ}{_}{Env.shr-vals{sr} θ sr∈}{SharedVar.new}{nl} (¬sl≡sr ∘ sym) sr∈ sl∈ sr∈2 sr≡ refl
    ... | (eq1 , eq2) rewrite {- sym eq1 | -} sym eq2 =( rset-shared-value-new e''r sr∈2 eq1 (depar₂ ieqr)) , vset-shared-value-new
    resr = getr e''r,δr≡


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}  cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-old{s = sr} e'r sr∈ sr≡ .(depar₂ ieqr)) (rset-shared-value-old{s = sl} e'l sl∈ sl≡  .ieql) olieq orieq vset-shared-value-old vset-shared-value-old refl refl
  with sl SharedVar.≟ sr
... | yes refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr , (_ , refl , refl))))))
      where
        s = sl
        s∈ = sl∈
        nl = (δ e'l)
        nr = (δ e'r)
        s∈l = shr-set-mono'{s}{s}{θ}{SharedVar.new}{nr}{s∈} s∈
        s∈r = shr-set-mono'{s}{s}{θ}{SharedVar.new}{nl}{s∈} s∈
        s≡r,s≡nr = shr-putget{s}{θ}{SharedVar.new}{nr} s∈ s∈l
        s≡r,s≡nl = shr-putget{s}{θ}{SharedVar.new}{nl} s∈ s∈r
        θl = (Env.set-shr{s = s} θ  s∈ SharedVar.new nl)
        θr = (Env.set-shr{s = s} θ  s∈ SharedVar.new nr)
        θo = (Env.set-shr{s = s} θl s∈r SharedVar.new ((Env.shr-vals{s = s} θl s∈r) + nr))
        θo2 = (Env.set-shr{s = s} θr s∈l SharedVar.new ((Env.shr-vals{s = s} θr s∈l) + nl))
        e''l,δl≡ = ready-irr-on-irr-s sr nr sr∈ (λ x → lookup-s-eq θ sl sr∈ sr∈ x sr≡ (λ ())) e'l
        e''r,δr≡ = ready-irr-on-irr-s sl nl sl∈ (λ x → lookup-s-eq θ sl sl∈ sr∈ x sr≡ (λ ())) e'r
        -- s≡r,s≡nl' = shr-putget{s}{_}{SharedVar.new}{(δ (proj₁ e''l,δl≡)) } s∈ s∈r
        θo≡θo2 : θo ≡ θo2
        θo≡θo2 rewrite (proj₂ s≡r,s≡nr)
                     | (proj₂ s≡r,s≡nl)
                     | +-comm nl nr
                     | shr-putput-overwrite s θ SharedVar.new nl SharedVar.new (nr + nl) s∈ s∈r
                     | shr-putput-overwrite s θ SharedVar.new nr SharedVar.new (nr + nl) s∈ s∈l
             = refl

        getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
        getl (e'' , e≡) rewrite θo≡θo2 | e≡ = (rset-shared-value-new e'' s∈l ((proj₁ s≡r,s≡nr)) (depar₁{q = (Er ⟦ r ⟧e)} ieql')) , vset-shared-value-new

        {-
        getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
        getl (e'' , e≡) rewrite sym (proj₂ s≡r,s≡nr) with rk | vk
        ... | redr | viewr rewrite (sym e≡) | (proj₂ s≡r,s≡nr) | sym (proj₂ s≡r,s≡nl) | +-comm nr (δ e'') = {! redr!} , {!(proj₂ s≡r,s≡nr)!}
        -}
        resl = getl e''l,δl≡

        getr : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θl · ( (El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
        getr (e''r , δr≡) rewrite δr≡  = (rset-shared-value-new e''r s∈r (proj₁ s≡r,s≡nl) (depar₂ ieqr)) , vset-shared-value-new
        resr = getr e''r,δr≡

... | no ¬sl≡sr = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , (proj₁ resr
      , (proj₂ resl , proj₂ resr , (_ , refl , refl)))))))
  where
    nl = (δ e'l)
    nr = (δ e'r)
    θl = Env.set-shr{sl} θ sl∈ SharedVar.new nl
    θr = Env.set-shr{sr} θ sr∈ SharedVar.new nr

    sl∈2 = shr-set-mono'{sl}{sr}{θ}{SharedVar.new}{nr}{sr∈} sl∈
    sr∈2 = shr-set-mono'{sr}{sl}{θ}{SharedVar.new}{nl}{sl∈} sr∈
    θo   = Env.set-shr{sr} θl sr∈2 SharedVar.new nr
    e''l,δl≡ = ready-irr-on-irr-s sr nr sr∈ (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l
    e''r,δr≡ = ready-irr-on-irr-s sl nl sl∈ (λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ())) e'r
    getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
    getl (e'' , e≡) with shr-set-comm θ sl sr SharedVar.new nl SharedVar.new nr sl∈ sr∈ ¬sl≡sr
    ... | (_ , _ , θ≡)  rewrite θ≡ with shr-putputget {sl}{sr}{θ}{_}{Env.shr-vals{sl} θ sl∈}{SharedVar.new}{nr} ¬sl≡sr sl∈ sr∈ sl∈2 sl≡ refl
    ... | (eq1 , eq2) rewrite e≡ | sym eq2
           = rset-shared-value-old e'' sl∈2 eq1 (depar₁ ieql') , vset-shared-value-old
    resl = (getl e''l,δl≡)

    getr : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θl · ( (El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
    getr (e''r , δr≡) rewrite δr≡ with shr-putputget {sr}{sl}{θ}{_}{Env.shr-vals{sr} θ sr∈}{SharedVar.new}{nl} (¬sl≡sr ∘ sym) sr∈ sl∈ sr∈2 sr≡ refl
    ... | (eq1 , eq2) rewrite {- sym eq1 | -} sym eq2 =( rset-shared-value-old e''r sr∈2 eq1 (depar₂ ieqr)) , vset-shared-value-old
    resr = getr e''r,δr≡
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}  cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-old{s = sr} e'r sr∈ sr≡ .(depar₂ ieqr)) (rset-shared-value-new{s = sl} e'l sl∈ sl≡ .ieql) olieq orieq vset-shared-value-old vset-shared-value-new refl refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr , (_ , refl , refl))))))
   where
     ¬sl≡sr : ¬ sl ≡ sr
     ¬sl≡sr refl rewrite shr∈-eq'{sl}{shr θ} sl∈ sr∈ | sl≡ = ((¬ (SharedVar.new ≡ SharedVar.old)) ∋ (λ ())) sr≡
     nl = (Env.shr-vals{s = sl} θ sl∈ + (δ e'l))
     nr = (δ e'r)
     sl∈2 = shr-set-mono'{sl}{sr}{θ}{SharedVar.new}{nr}{sr∈} sl∈
     sr∈2 = shr-set-mono'{sr}{sl}{θ}{SharedVar.new}{nl}{sl∈} sr∈

     θl = (Env.set-shr{s = sl} θ sl∈ SharedVar.new nl)
     θr = (Env.set-shr{s = sr} θ sr∈ SharedVar.new nr)
     θo = (Env.set-shr{s = sr} θl sr∈2 SharedVar.new nr)

     e''l,δl≡ = ready-irr-on-irr-s sr nr sr∈ (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l
     e''r,δr≡ = ready-irr-on-irr-s sl nl sl∈ (λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ())) e'r

     getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
     getl (e'' , e≡) with (shr-set-comm θ sl sr SharedVar.new nl SharedVar.new nr sl∈ sr∈ ¬sl≡sr)
     ... | (_ , _ , eq) rewrite eq with (shr-putputget {sl} {sr} {θ}{SharedVar.new}{Env.shr-vals{sl} θ sl∈}{SharedVar.new}{nr} ¬sl≡sr sl∈ sr∈ sl∈2 sl≡ refl)
     ... | (eq1 , eq2) rewrite sym eq2 | e≡ = rset-shared-value-new e'' sl∈2 eq1 (depar₁ ieql')  , vset-shared-value-new
     resl = (getl e''l,δl≡)

     getr : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θl · ( (El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     getr (e''r , δr≡) rewrite δr≡ = rset-shared-value-old e''r sr∈2 (proj₁ (shr-putputget {sr} {sl} {θ}{SharedVar.old}{Env.shr-vals{sr} θ sr∈}{SharedVar.new}{nl} (¬sl≡sr ∘ sym) sr∈ sl∈ sr∈2 sr≡ refl)) (depar₂ ieqr) , vset-shared-value-old
     resr = getr e''r,δr≡

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r}  cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-new{s = sr} e'r sr∈ sr≡ .(depar₂ ieqr)) (rset-shared-value-old{s = sl} e'l sl∈ sl≡ .ieql) olieq orieq vset-shared-value-new vset-shared-value-old refl refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr , (_ , refl , refl))))))
   where
     ¬sl≡sr : ¬ sl ≡ sr
     ¬sl≡sr refl rewrite shr∈-eq'{sl}{shr θ} sl∈ sr∈ | sl≡ = ((¬ (SharedVar.new ≡ SharedVar.old)) ∋ (λ ())) (sym sr≡)
     nl = (δ e'l)
     nr = (Env.shr-vals{s = sr} θ sr∈ + (δ e'r))
     sl∈2 = shr-set-mono'{sl}{sr}{θ}{SharedVar.new}{nr}{sr∈} sl∈
     sr∈2 = shr-set-mono'{sr}{sl}{θ}{SharedVar.new}{nl}{sl∈} sr∈

     θl = (Env.set-shr{s = sl} θ sl∈ SharedVar.new nl)
     θr = (Env.set-shr{s = sr} θ sr∈ SharedVar.new nr)
     θo = (Env.set-shr{s = sr} θl sr∈2 SharedVar.new nr)

     e''l,δl≡ = ready-irr-on-irr-s sr nr sr∈ (λ x → lookup-s-eq θ sr sr∈ sr∈ x sr≡ (λ ())) e'l
     e''r,δr≡ = ready-irr-on-irr-s sl nl sl∈ (λ x → lookup-s-eq θ sl sl∈ sl∈ x sl≡ (λ ())) e'r

     getl : (typeof e''l,δl≡) → Σ[ redr ∈ ((ρ θr · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
     getl (e'' , e≡) with (shr-set-comm θ sl sr SharedVar.new nl SharedVar.new nr sl∈ sr∈ ¬sl≡sr)
     ... | (_ , _ , eq) rewrite eq with (shr-putputget {sl} {sr} {θ}{SharedVar.old}{Env.shr-vals{sl} θ sl∈}{SharedVar.new}{nr} ¬sl≡sr sl∈ sr∈ sl∈2 sl≡ refl)
     ... | (eq1 , eq2) rewrite sym eq2 | e≡ = rset-shared-value-old e'' sl∈2 eq1 (depar₁ ieql')  , vset-shared-value-old
     resl = (getl e''l,δl≡)

     getr : (typeof e''r,δr≡) → Σ[ redr ∈ ((ρ θl · ( (El ⟦ l ⟧e) ∥ q )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     getr (e''r , δr≡) with (shr-putputget {sr} {sl} {θ}{SharedVar.new}{Env.shr-vals{sr} θ sr∈}{SharedVar.new}{nl} (¬sl≡sr ∘ sym) sr∈ sl∈ sr∈2 sr≡ refl)
     ... | (eq1 , eq2) rewrite sym eq2 | δr≡ =   rset-shared-value-new e''r sr∈2 eq1 (depar₂ ieqr)  , vset-shared-value-new -- rset-shared-value-new e''r sr∈2 (proj₁ ) (depar₂ ieqr) , vset-shared-value-new
     resr = getr e''r,δr≡

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} cb (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-new{s = sr} e'r sr∈ sr≡ .(depar₂ ieqr)) (ris-present{S = Sl} S∈ S≡ .ieql) olieq orieq vset-shared-value-new vis-present refl refl
  = (Env.set-shr{s = sr} θ sr∈ SharedVar.new (Env.shr-vals{s = sr} θ sr∈ + (δ e'r))
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (ris-present S∈ S≡ (depar₁ ieql') , rset-shared-value-new e'r sr∈ sr≡ (depar₂ ieqr)
      , (vis-present , vset-shared-value-new , (_ , refl , refl))))))

-- IDK about these
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-false{x = x} x∈ x≡ .(depar₂ ieqr)) (rmerge{θ₁ = .θ}{θm} .ieql) olieq orieq vif-false vmerge refl refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rmerge (depar₁ ieql') , rif-false x∈2
                                   (trans (sym (seq-←-irr-get' {θ} {θm} {x} x∈ x∉Domθm x∈2)) x≡) (depar₂ ieqr)
      , (vmerge , vif-false , (_ , refl , refl))))))
     where
      θo = (θ ← θm)
      x∈2 = (seq-←-monoˡ x θ θm x∈)
      x∉Domθm : ¬ isVar∈ x θm
      x∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
      ... | (  o , BVo , FVo ) , (CBpar{FVp = FVm}{FVq = FVif} cbm@(CBρ _) cb<=@(CBif _ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
          = λ x₁ → proj₂ (proj₂ BVl≠FVr) (SeqVar.unwrap x) (++ˡ x₁) (here refl)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rif-true{x = x} x∈ x≡ .(depar₂ ieqr)) (rmerge{θ₂ = θm} .ieql) olieq orieq vif-true vmerge refl refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rmerge (depar₁ ieql') , rif-true  x∈2
                                   (trans (sym (seq-←-irr-get' {θ} {θm} {x} x∈ x∉Domθm x∈2)) x≡) (depar₂ ieqr)
      , (vmerge , vif-true , (_ , refl , refl))))))
     where
      θo = (θ ← θm)
      x∈2 = (seq-←-monoˡ x θ θm x∈)
      x∉Domθm : ¬ isVar∈ x θm
      x∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
      ... | (  o , BVo , FVo ) , (CBpar{FVp = FVm}{FVq = FVif} cbm@(CBρ _) cb<=@(CBif _ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
          = λ x₁ → proj₂ (proj₂ BVl≠FVr) (SeqVar.unwrap x) (++ˡ x₁) (here refl)

ρ-conf-rec2 {θ}  {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r}  (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (rif-false{x = x} x∈ x≡ .ieql) olieq orieq vmerge vif-false refl refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rif-false x∈2
      (trans (sym (seq-←-irr-get' {θ} {θm} {x} x∈ x∉Domθm x∈2)) x≡) (depar₁ ieql')
      , rmerge (depar₂ ieqr)
      , (vif-false , vmerge , (_ , refl , refl))))))
     where
      θo = (θ ← θm)
      x∈2 = (seq-←-monoˡ x θ θm x∈)
      x∉Domθm : ¬ isVar∈ x θm
      x∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
      ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBif _ _) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
          = λ x₁ → proj₂ (proj₂ FVl≠BVr) (SeqVar.unwrap x) (here refl) (++ˡ x₁)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r}  (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (rif-true{x = x} x∈ x≡ .ieql) olieq orieq vmerge vif-true refl refl
   = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rif-true x∈2
      (trans (sym (seq-←-irr-get' {θ} {θm} {x} x∈ x∉Domθm x∈2)) x≡) (depar₁ ieql')
      , rmerge (depar₂ ieqr)
      , (vif-true , vmerge , (_ , refl , refl))))))
     where
      θo = (θ ← θm)
      x∈2 = (seq-←-monoˡ x θ θm x∈)
      x∉Domθm : ¬ isVar∈ x θm
      x∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
      ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBif _ _) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
          = λ x₁ → proj₂ (proj₂ FVl≠BVr) (SeqVar.unwrap x) (here refl) (++ˡ x₁)


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (ris-absent{S = S} S∈ S≡ .(depar₂ ieqr)) (rmerge{θ₁ = .θ}{θ₂ = θm} .ieql) olieq orieq vis-absent vmerge refl refl
    = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rmerge (depar₁ ieql') , ris-absent S∈2 (trans (sym (sig-←-irr-get' {θ} {θm} {S} S∈ S∉Domθm S∈2)) S≡) (depar₂ ieqr)
      , (vmerge , vis-absent , (_ , refl , refl))))))
      where
        θo = (θ ← θm)
        S∈2 = (sig-←-monoˡ S θ θm S∈)
        S∉Domθm : ¬ isSig∈ S θm
        S∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
        ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBρ _) cbm@(CBpresent _ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
          = λ y →  proj₁ BVl≠FVr _ (++ˡ y) (here refl)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (ris-absent{S = S} S∈ S≡ .ieql) olieq orieq vmerge vis-absent refl refl
    = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (ris-absent S∈2 (trans (sym (sig-←-irr-get' {θ} {θm} {S} S∈ S∉Domθm S∈2)) S≡) (depar₁ ieql') , rmerge (depar₂ ieqr)
      , ( vis-absent , vmerge , (_ , refl , refl))))))
      where
        θo = (θ ← θm)
        S∈2 = (sig-←-monoˡ S θ θm S∈)
        S∉Domθm : ¬ isSig∈ S θm
        S∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
        ... | (  o , BVo , FVo ) , (CBpar cbm@(CBpresent _ _) cb<=@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
          = λ y →  proj₁ FVl≠BVr _ (here refl) (++ˡ y)

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (ris-present{S = S} S∈ S≡ .(depar₂ ieqr)) (rmerge{θ₁ = .θ}{θ₂ = θm} .ieql) olieq orieq vis-present vmerge refl refl
    = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (rmerge (depar₁ ieql') , ris-present S∈2 (trans (sym (sig-←-irr-get' {θ} {θm} {S} S∈ S∉Domθm S∈2)) S≡) (depar₂ ieqr)
      , (vmerge , vis-present , (_ , refl , refl))))))
      where
        θo = (θ ← θm)
        S∈2 = (sig-←-monoˡ S θ θm S∈)
        S∉Domθm : ¬ isSig∈ S θm
        S∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
        ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBρ _) cbm@(CBpresent _ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
          = λ y →  proj₁ BVl≠FVr _ (++ˡ y) (here refl)
ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (ris-present{S = S} S∈ S≡ .ieql) olieq orieq vmerge vis-present refl refl
    = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (ris-present S∈2 (trans (sym (sig-←-irr-get' {θ} {θm} {S} S∈ S∉Domθm S∈2)) S≡) (depar₁ ieql') , rmerge (depar₂ ieqr)
      , ( vis-present , vmerge , (_ , refl , refl))))))
      where
        θo = (θ ← θm)
        S∈2 = (sig-←-monoˡ S θ θm S∈)
        S∉Domθm : ¬ isSig∈ S θm
        S∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
        ... | (  o , BVo , FVo ) , (CBpar cbm@(CBpresent _ _) cb<=@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
          = λ y →  proj₁ FVl≠BVr _ (here refl) (++ˡ y)


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (remit{S = S} S∈ ¬S≡a .(depar₂ ieqr)) (rmerge{θ₂ = θm} .ieql) olieq orieq vemit vmerge refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , proj₁ resl , remit S∈2 (λ x →  ¬S≡a (trans  (sig-←-∉-irr-stats' S θ θm S∈ S∉Domθm S∈2) x)) (depar₂ ieqr)
      , ( proj₂ resl , vemit
      , (_ , refl , refl)))))
  where
    S∉Domθm : ¬ isSig∈ S θm
    S∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
    ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBemit) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
      = λ x → (proj₁ BVl≠FVr) _ (++ˡ x) (here refl)
    S∈2,θ≡ = sig-set-←-comm S Signal.present θ θm S∈ S∉Domθm
    S∈2 = proj₁ S∈2,θ≡
    θ≡ = proj₂ S∈2,θ≡
    θr = Env.set-sig{S = S} θ S∈ Signal.present
    θo = Env.set-sig{S = S} (θ ← θm) S∈2 Signal.present
    resl : Σ[ redr ∈ ((ρ θr · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
    resl rewrite sym θ≡ = rmerge (depar₁ ieql') , vmerge

ρ-conf-rec2 {θ}  {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (remit{S = S} S∈ ¬S≡a .ieql) olieq orieq vmerge vemit refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      ,  remit S∈2 ((λ x →  ¬S≡a (trans  (sig-←-∉-irr-stats' S θ θm S∈ S∉Domθm S∈2) x))) (depar₁ ieql') , proj₁ resr
      , ( vemit , proj₂ resr
      , (_ , refl , refl)))))
  where
    S∉Domθm : ¬ isSig∈ S θm
    S∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
    ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBemit) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
      = λ x → (proj₁ FVl≠BVr) _ (here refl) (++ˡ x)
    S∈2,θ≡ = sig-set-←-comm S Signal.present θ θm S∈ S∉Domθm
    S∈2 = proj₁ S∈2,θ≡
    θ≡ = proj₂ S∈2,θ≡
    θr = Env.set-sig{S = S} θ S∈ Signal.present
    θo = Env.set-sig{S = S} (θ ← θm) S∈2 Signal.present
    resr : Σ[ redr ∈ (ρ θr · ( (El ⟦ l ⟧e) ∥ q ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
    resr rewrite sym θ≡ = rmerge (depar₂ ieqr) , vmerge


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rraise-shared{e = e} e' .(depar₂ ieqr)) (rmerge{θ₂ = θm} .ieql) olieq orieq vraise-shared vmerge refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , rmerge (depar₁ ieql') , proj₁ resr
      , ( vmerge , proj₂ resr
      , (_ , refl , refl)))))
  where
    θo = (θ ← θm)
    Domθm≠FVe : distinct (Dom θm) (FVₑ e)
    Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
    ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBshared _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
      = distinct-sym (dist++ˡ (distinct-sym (dist++ˡ BVl≠FVr)))
    resr : Σ[ redr ∈ (ρ θo · ( (El ⟦ l ⟧e) ∥ q ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
    resr with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
    ... | (e'' , e≡) rewrite e≡ = rraise-shared e'' (depar₂ ieqr) , vraise-shared

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (rraise-shared{e = e} e' .ieql) olieq orieq vmerge vraise-shared refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , proj₁ resl , rmerge (depar₂ ieqr)
      , (proj₂ resl , vmerge
      , (_ , refl , refl)))))
  where
    θo = (θ ← θm)
    Domθm≠FVe : distinct (Dom θm) (FVₑ e)
    Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
    ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBshared _) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
      = (dist++ˡ (distinct-sym (dist++ˡ FVl≠BVr)))
    resl : Σ[ redr ∈ (ρ θo · ( p ∥ (Er ⟦ r ⟧e) ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
    resl with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
    ... | (e'' , e≡) rewrite e≡ = rraise-shared e'' (depar₁ ieql') , vraise-shared

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rraise-var{e = e} e' .(depar₂ ieqr)) (rmerge{θ₂ = θm} .ieql) olieq orieq vraise-var vmerge refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , rmerge (depar₁ ieql') , proj₁ resr
      , ( vmerge , proj₂ resr
      , (_ , refl , refl)))))
  where
    θo = (θ ← θm)
    Domθm≠FVe : distinct (Dom θm) (FVₑ e)
    Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
    ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBvar _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
      = distinct-sym (dist++ˡ (distinct-sym (dist++ˡ BVl≠FVr)))
    resr : Σ[ redr ∈ (ρ θo · ( (El ⟦ l ⟧e) ∥ q ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
    resr with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
    ... | (e'' , e≡) rewrite e≡ = rraise-var e'' (depar₂ ieqr) , vraise-var

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (rraise-var{e = e} e' .ieql) olieq orieq vmerge vraise-var refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , proj₁ resl , rmerge (depar₂ ieqr)
      , (proj₂ resl , vmerge
      , (_ , refl , refl)))))
  where
    θo = (θ ← θm)
    Domθm≠FVe : distinct (Dom θm) (FVₑ e)
    Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
    ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBvar _) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
      = (dist++ˡ (distinct-sym (dist++ˡ FVl≠BVr)))
    resl : Σ[ redr ∈ (ρ θo · ( p ∥ (Er ⟦ r ⟧e) ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
    resl with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
    ... | (e'' , e≡) rewrite e≡ = rraise-var e'' (depar₁ ieql') , vraise-var

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-var{x = x}{e = e} x∈ e' .(depar₂ ieqr)) (rmerge{θ₂ = θm} .ieql) olieq orieq vset-var vmerge refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr
      , (_ , refl , refl)))))
  where
     Domθm≠FVe : distinct (Dom θm) (FVₑ e)
     Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBvset) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = distinct-sym (dist++ˡ (distinct-sym (id , id , dist':: # BVl≠FVr)))
     x∉Domθm : ¬ isVar∈ x θm
     x∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBvset) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = λ x₁ → (proj₂ (proj₂ BVl≠FVr)) _ (++ˡ x₁) (here refl)
     x∈2,θ≡ = var-set-←-comm x (δ e') θ θm x∈ x∉Domθm
     x∈2 = proj₁ x∈2,θ≡
     θ≡ = proj₂ x∈2,θ≡



     θl = (θ ← θm)
     θr = Env.set-var{x = x} θ x∈ (δ e')
     θo = Env.set-var{x = x} θl x∈2 (δ e')
     resr : Σ[ redr ∈ (ρ θl · ( (El ⟦ l ⟧e) ∥ q ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     resr with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
     ... | (e'' , e≡) rewrite e≡ = rset-var x∈2 e'' (depar₂ ieqr) , vset-var
     resl : Σ[ redr ∈ (ρ θr · ( p ∥ (Er ⟦ r ⟧e) ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
     resl rewrite sym θ≡ = rmerge (depar₁ ieql') , vmerge


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (rset-var{x = x}{e = e} x∈ e' .ieql) olieq orieq vmerge vset-var refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr
      , (_ , refl , refl)))))
  where
     Domθm≠FVe : distinct (Dom θm) (FVₑ e)
     Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBvset) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       =  id , id , dist':: # (distinct-sym (dist++ˡ FVl≠BVr))
     x∉Domθm : ¬ isVar∈ x θm
     x∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBvset) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = λ x₁ → (proj₂ (proj₂ FVl≠BVr)) _ (here refl) (++ˡ x₁)
     x∈2,θ≡ = var-set-←-comm x (δ e') θ θm x∈ x∉Domθm
     x∈2 = proj₁ x∈2,θ≡
     θ≡ = proj₂ x∈2,θ≡

     θr = (θ ← θm)
     θl = Env.set-var{x = x} θ x∈ (δ e')
     θo = Env.set-var{x = x} θr x∈2 (δ e')
     resl : Σ[ redr ∈ (ρ θr · ( p ∥ (Er ⟦ r ⟧e) ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
     resl with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
     ... | (e'' , e≡) rewrite e≡ = rset-var x∈2 e'' (depar₁ ieql') , vset-var

     resr : Σ[ redr ∈ (ρ θl · ( (El ⟦ l ⟧e) ∥ q ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     resr rewrite sym θ≡ = rmerge (depar₂ ieqr) , vmerge


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-old{s = s}{e = e} e' s∈ s≡ .(depar₂ ieqr)) (rmerge{θ₂ = θm} .ieql) olieq orieq vset-shared-value-old vmerge refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr
      , (_ , refl , refl)))))
  where
     Domθm≠FVe : distinct (Dom θm) (FVₑ e)
     Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBsset) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = distinct-sym (dist++ˡ (distinct-sym (id , dist':: , id # BVl≠FVr)))
     s∉Domθm : ¬ isShr∈ s θm
     s∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBsset) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = λ x₁ → (proj₁ (proj₂ BVl≠FVr)) _ (++ˡ x₁) (here refl)
     s∈2,θ≡ = shr-set-←-comm s SharedVar.new (δ e') θ θm s∈ s∉Domθm
     s∈2 = proj₁ s∈2,θ≡
     θ≡ = proj₂ s∈2,θ≡



     θl = (θ ← θm)
     θr = Env.set-shr{s = s} θ s∈ SharedVar.new (δ e')
     θo = Env.set-shr{s = s} θl s∈2 SharedVar.new (δ e')
     resr : Σ[ redr ∈ (ρ θl · ( (El ⟦ l ⟧e) ∥ q ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     resr with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
     ... | (e'' , e≡) rewrite e≡ = rset-shared-value-old e'' s∈2 ( trans (sym (shr-←-irr-get' {θ} {θm} {s} s∈ s∉Domθm s∈2)) s≡ ) (depar₂ ieqr) , vset-shared-value-old
     resl : Σ[ redr ∈ (ρ θr · ( p ∥ (Er ⟦ r ⟧e) ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
     resl rewrite sym θ≡ = rmerge (depar₁ ieql') , vmerge

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (rset-shared-value-old{s = s}{e = e} e' s∈ s≡ .ieql) olieq orieq vmerge vset-shared-value-old refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr
      , (_ , refl , refl)))))
  where
     Domθm≠FVe : distinct (Dom θm) (FVₑ e)
     Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBsset) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = id , dist':: , id # (distinct-sym (dist++ˡ ((FVl≠BVr))))
     s∉Domθm : ¬ isShr∈ s θm
     s∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBsset) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = λ x₁ → (proj₁ (proj₂ FVl≠BVr)) _ (here refl) (++ˡ x₁)
     s∈2,θ≡ = shr-set-←-comm s SharedVar.new (δ e') θ θm s∈ s∉Domθm
     s∈2 = proj₁ s∈2,θ≡
     θ≡ = proj₂ s∈2,θ≡

     θr = (θ ← θm)
     θl = Env.set-shr{s = s} θ s∈ SharedVar.new (δ e')
     θo = Env.set-shr{s = s} θr s∈2 SharedVar.new (δ e')
     resr : Σ[ redr ∈ (ρ θl · ( (El ⟦ l ⟧e) ∥ q ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     resr rewrite sym θ≡ = rmerge (depar₂ ieqr) , vmerge
     resl : Σ[ redr ∈ (ρ θr · ( p ∥ (Er ⟦ r ⟧e) ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
     resl  with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
     ... | (e'' , e≡) rewrite e≡ = rset-shared-value-old e'' s∈2 ( trans (sym (shr-←-irr-get' {θ} {θm} {s} s∈ s∉Domθm s∈2)) s≡ ) (depar₁ ieql') , vset-shared-value-old


ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(p ∥ q)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rset-shared-value-new{s = s}{e = e} e' s∈ s≡ .(depar₂ ieqr)) (rmerge{θ₂ = θm} .ieql) olieq orieq vset-shared-value-new vmerge refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr
      , (_ , refl , refl)))))
  where
     sn = (Env.shr-vals{s = s} θ s∈ + δ e')
     Domθm≠FVe : distinct (Dom θm) (FVₑ e)
     Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBsset) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = distinct-sym (dist++ˡ (distinct-sym (id , dist':: , id # BVl≠FVr)))
     s∉Domθm : ¬ isShr∈ s θm
     s∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBsset) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = λ x₁ → (proj₁ (proj₂ BVl≠FVr)) _ (++ˡ x₁) (here refl)
     s∈2,θ≡ = shr-set-←-comm s SharedVar.new sn θ θm s∈ s∉Domθm
     s∈2 = proj₁ s∈2,θ≡
     θ≡ = proj₂ s∈2,θ≡

     θl = (θ ← θm)
     θr = Env.set-shr{s = s} θ s∈ SharedVar.new sn
     θo = Env.set-shr{s = s} θl s∈2 SharedVar.new sn
     resr : Σ[ redr ∈ (ρ θl · ( (El ⟦ l ⟧e) ∥ q ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     resr with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
     ... | (e'' , e≡) rewrite e≡ | (shr-←-irr-get/vals' {θ} {θm} {s} s∈ s∉Domθm s∈2) = rset-shared-value-new e'' s∈2 ( trans (sym (shr-←-irr-get' {θ} {θm} {s} s∈ s∉Domθm s∈2)) s≡ ) (depar₂ ieqr) , vset-shared-value-new
     resl : Σ[ redr ∈ (ρ θr · ( p ∥ (Er ⟦ r ⟧e) ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
     resl rewrite sym θ≡ = rmerge{θ₁ = θr}{θ₂ = θm} (depar₁ ieql') , vmerge

ρ-conf-rec2 {θ}  {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)}  {i = .(_ ∥ _)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θm} .(depar₂ ieqr)) (rset-shared-value-new{s = s}{e = e} e' s∈ s≡ .ieql) olieq orieq vmerge vset-shared-value-new refl refl
 = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , proj₁ resl , proj₁ resr
      , (proj₂ resl , proj₂ resr
      , (_ , refl , refl)))))
  where
     sn = (Env.shr-vals{s = s} θ s∈ + δ e')
     Domθm≠FVe : distinct (Dom θm) (FVₑ e)
     Domθm≠FVe with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBsset) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = (id , dist':: , id # (distinct-sym (dist++ˡ FVl≠BVr)))
     s∉Domθm : ¬ isShr∈ s θm
     s∉Domθm with inspecting-cb-distinct-double-unplug cb ieql' ieqr
     ... | (  o , BVo , FVo ) , (CBpar cb<=@(CBsset) cbm@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
       = λ x₁ → (proj₁ (proj₂ FVl≠BVr)) _ (here refl) (++ˡ x₁)
     s∈2,θ≡ = shr-set-←-comm s SharedVar.new sn θ θm s∈ s∉Domθm
     s∈2 = proj₁ s∈2,θ≡
     θ≡ = proj₂ s∈2,θ≡

     θr = (θ ← θm)
     θl = Env.set-shr{s = s} θ s∈ SharedVar.new sn
     θo = Env.set-shr{s = s} θr s∈2 SharedVar.new sn
     resr : Σ[ redr ∈ (ρ θl · ( (El ⟦ l ⟧e) ∥ q ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₂ ieqr) Erefl
     resr rewrite sym θ≡ = rmerge{θ₁ = θl}{θ₂ = θm} (depar₂ ieqr) , vmerge
     resl : Σ[ redr ∈ (ρ θr · ( p ∥ (Er ⟦ r ⟧e) ) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
     resl with ready-irr-on-irr-θˡ θm e' Domθm≠FVe
     ... | (e'' , e≡) rewrite e≡ | (shr-←-irr-get/vals' {θ} {θm} {s} s∈ s∉Domθm s∈2) = rset-shared-value-new e'' s∈2 ( trans (sym (shr-←-irr-get' {θ} {θm} {s} s∈ s∉Domθm s∈2)) s≡ ) (depar₁ ieql') , vset-shared-value-new

ρ-conf-rec2 {θ} {(epar₂ p ∷ Er)} {(epar₁ q ∷ El)} {i = .(_ ∥ _)} {qro = l} {qlo = r} (CBρ cb) (depar₂ ieqr) ieql@(depar₁ ieql') par (rmerge{θ₂ = θr} .(depar₂ ieqr)) (rmerge{θ₂ = θl} .ieql) olieq orieq vmerge vmerge refl refl
  = (θo
      , (( El ⟦ l ⟧e ) ∥ ( Er ⟦ r ⟧e ))
      , ((epar₂ (El ⟦ l ⟧e) ∷ Er)) , ((epar₁ (Er ⟦ r ⟧e) ∷ El)
      , (depar₂ ieqr) , (depar₁ ieql')
      , (Erefl , Erefl
      , (proj₁ resl , rmerge (depar₂ ieqr)
      , (proj₂ resl , vmerge , (_ , refl , refl))))))

  where
    θo = (θ ← θl) ← θr
    Domθl≠Domθr : distinct (Dom θl) (Dom θr)
    Domθl≠Domθr with inspecting-cb-distinct-double-unplug cb ieql' ieqr
    ... | (  o , BVo , FVo ) , (CBpar cbm@(CBρ _) cb<=@(CBρ _) BVl≠BVr FVl≠BVr BVl≠FVr Xl≠Xr) , refl
          = (λ f a b c → f a (++ˡ b) (++ˡ c)) , (λ f a b c → f a (++ˡ b) (++ˡ c)) , (λ f a b c → f a (++ˡ b) (++ˡ c)) # BVl≠BVr

    θ←θl←θr≡ = ←-assoc-comm θ θl θr Domθl≠Domθr

    resl : Σ[ redr ∈ ((ρ (θ ← θr) · ( p ∥ (Er ⟦ r ⟧e) )) sn⟶₁ (ρ θo · (El ⟦ l ⟧e) ∥ (Er ⟦ r ⟧e) )) ] ->E-view redr (depar₁ ieql') Erefl
    resl rewrite θ←θl←θr≡ = rmerge (depar₁ ieql') , vmerge
