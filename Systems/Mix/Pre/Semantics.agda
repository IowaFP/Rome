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
Row s = Σ Nat (Π (Ix varZ) s)

--------------------------------------------------------------------------------
-- Translating typed Rω to untyped Mix.
--
-- These "flat" translations become indices to the translation of typed Rω to typed
-- Mix terms.

-- read as "the translation of κ *has sort* ⟦ κ ⟧σ"
⟦_⟧σ : (κ : Rμ.Kind) → Term
⟦ ★ ⟧σ = 𝓤
⟦ L ⟧σ = ★
⟦ R[ κ ] ⟧σ = 𝓤
⟦ κ `→ κ₁ ⟧σ = ★

-- read as "the translation of κ to type ⟦ κ ⟧κ"
⟦_⟧κ : (κ : Rμ.Kind) →  Term
⟦ ★ ⟧κ = ★
⟦ L ⟧κ = ⊤
⟦ R[ κ ] ⟧κ = Row ⟦ κ ⟧κ
⟦ κ₁ `→ κ₂ ⟧κ = Π ⟦ κ₁ ⟧κ ⟦ κ₂ ⟧κ

⟦_⟧v : ∀ {Δ}{κ} → Rμ.TVar Δ κ → Term
⟦ Z ⟧v = varZ
⟦ S x ⟧v = varS ⟦ x ⟧v

⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Term
⟦ U ⟧τ = ⊤
⟦_⟧τ (tvar x) = ⟦ x ⟧v
  --
⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ ⟦ τ₂ ⟧τ
⟦ `∀ κ τ ⟧τ = Π ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ `λ κ τ ⟧τ = `λ ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ τ₁ ·[ τ₂ ] ⟧τ = ⟦ τ₁ ⟧τ · ⟦ τ₂ ⟧τ
  --
⟦ lab l ⟧τ = tt
⟦ _ ▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ _ R▹ τ ⟧τ = ⟪ Suc Zero ⦂ Nat , `λ (Ix varZ) ⟦ τ ⟧τ ⟫
⟦ ⌊ τ ⌋ ⟧τ = ⊤
⟦_⟧τ {Δ} ε = ⟪ Zero ⦂ Nat ,  `λ (Ix varZ) ⊤ ⟫
⟦ Π ρ ⟧τ = Π (Ix (fst ⟦ ρ ⟧τ)) ((snd ⟦ ρ ⟧τ) · varZ)
⟦ Σ ρ ⟧τ = Σ (Ix (fst ⟦ ρ ⟧τ)) ((snd ⟦ ρ ⟧τ) · varZ)
⟦ τ ·⌈ τ₁ ⌉ ⟧τ = {!!}
⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}
  --
⟦ π ⇒ τ ⟧τ = {!!}
  --
⟦ μ τ ⟧τ = {!!}
⟦ ν τ ⟧τ = {!!}

⟦_⟧ : ∀ {Δ}{Γ}{Φ}{τ} → Rμ.Term Δ Γ Φ τ → Term
⟦ M ⟧ = {!!}
