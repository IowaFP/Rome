-- {-# OPTIONS --safe #-}
module Rome.Both.Terms.GVars where

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars
open import Rome.Both.Terms.Syntax
open import Rome.Both.Types.Normal.Syntax

variable
  Γ Γ₁ Γ₂ Γ₃ : Env Δ ιΓ
  τ τ' υ υ' τ₁ τ₂ υ₁ υ₂  : NormalType Δ ★
  l l₁ l₂    : NormalType Δ L
  ℓ : Term Γ ⌊ l ⌋
  ℓ₁ : Term Γ ⌊ l₁ ⌋
  ℓ₂ : Term Γ ⌊ l₂ ⌋
  ρ ρ₁ ρ₂ ρ₃ : NormalType Δ R[ κ ]
  π π₁ π₂ π₃ : NormalPred Δ R[ κ ]
