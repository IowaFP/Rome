{-# OPTIONS --allow-unsolved-metas #-}
module Mix.Pre.Semantics where

open import Mix.Pre.Terms

module Rμ where
 open import Rome.Kinds.Syntax public
 open import Rome.Types.Syntax public
 open import Rome.Terms.Syntax public
 open import Rome.Entailment.Syntax public

open Rμ.Kind
open Rμ.KEnv
open Rμ.Type
open Rμ.TVar
open Rμ.Term

Row : Term → Term
Row s = `∃ Nat (`∀ (Ix varZ) s)

--------------------------------------------------------------------------------
-- Translating typed Rω to untyped Mix.
--
⟦_⟧κ : (κ : Rμ.Kind) →  Term
⟦ ★ ⟧κ = ★
⟦ L ⟧κ = ⊤
⟦ R[ κ ] ⟧κ = Row ⟦ κ ⟧κ
⟦ κ₁ `→ κ₂ ⟧κ = `∀ ⟦ κ₁ ⟧κ ⟦ κ₂ ⟧κ

⟦_⟧p : ∀ {Δ}{κ} → Rμ.Pred Δ κ → Term
⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Term

⟦ U ⟧τ = ⊤
⟦ tvar Z ⟧τ = varZ
⟦ tvar (S x) ⟧τ = varS ⟦ (tvar x) ⟧τ
⟦ τ `→ υ ⟧τ = `∀ ⟦ τ ⟧τ ⟦ υ ⟧τ 
⟦ `∀ κ τ ⟧τ = `∀ ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ `λ κ τ ⟧τ = `∀ ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ τ ·[ υ ] ⟧τ = ⟦ τ ⟧τ · ⟦ υ ⟧τ
⟦ μ τ ⟧τ = ⊤
⟦ ν τ ⟧τ = ⊤
⟦ π ⇒ τ ⟧τ = `∀ ⟦ π ⟧p ⟦ τ ⟧τ
⟦ lab l ⟧τ = ⊤
⟦ _ ▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ _ R▹ τ ⟧τ = ⟪ One ⦂ Nat , `λ (Ix One) CaseIx varZ of[ ⟦ τ ⟧τ ∣ ƛ⦅⦆ ] ⟫
⟦ ⌊ _ ⌋ ⟧τ = ⊤
⟦ ε ⟧τ = ⟪ Z ⦂ Nat , ƛ⦅⦆ ⟫
⟦ Π ρ ⟧τ = Case∃ ⟦ ρ ⟧τ of[ 
  (`λ Nat 
    (`λ (`∀ (Ix varZ) ★) 
      (`∀ (Ix (varS varZ)) 
        ((varS varZ) · varZ)))) ]
⟦ Σ ρ ⟧τ = Case∃ ⟦ ρ ⟧τ of[ 
  (`λ Nat 
    (`λ (`∀ (Ix varZ) ★) 
      (`∃ (Ix (varS varZ)) 
        ((varS varZ) · varZ)))) ]
⟦ _·⌈_⌉ {κ₁ = κ₁} {κ₂} τ υ ⟧τ = {!!}
⟦ ⌈_⌉·_ {κ₁ = κ₁} {κ₂} τ υ ⟧τ = {!!}

⟦ ρ₁ Rμ.≲ ρ₂ ⟧p = {!!}
⟦ ρ₁ Rμ.· ρ₂ ~ ρ₃ ⟧p = {!!}
