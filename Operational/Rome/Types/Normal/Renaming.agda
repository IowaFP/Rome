module Operational.Rome.Types.Normal.Renaming where

open import Operational.Rome.Prelude
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

open import Operational.Rome.Types.Syntax
open import Operational.Rome.Types.Renaming using (↑ ; Renaming)
open import Operational.Rome.Types.Properties

open import Operational.Rome.Types.Normal.Syntax

--------------------------------------------------------------------------------
-- Normal Type renaming.

renNE : Renaming Δ₁ Δ₂ → NeutralType Δ₁ κ → NeutralType Δ₂ κ
ren : Renaming Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ

renNE ρ (` x) = ` (ρ x)
renNE ρ (τ₁ · τ₂) = renNE ρ τ₁ · ren ρ τ₂
renNE ρ (τ₁ ▹ τ₂) = ren ρ τ₁ ▹ renNE ρ τ₂

ren ρ Unit   = Unit
ren ρ (ne τ) = ne (renNE ρ τ)
ren ρ (`λ τ) = `λ (ren (↑ ρ) τ)
ren ρ (τ₁ `→ τ₂) = (ren ρ τ₁) `→ (ren ρ τ₂)
ren ρ (`∀ κ τ) = `∀ κ (ren (↑ ρ) τ)
ren ρ (μ τ) = μ (ren ρ τ)
ren ρ (Π τ) = Π (ren ρ τ)
ren ρ (Σ τ) = Σ (ren ρ τ)
ren ρ (lab x) = lab x
ren ρ (ℓ ▹ τ) = (ren ρ ℓ) ▹ (ren ρ τ)
ren ρ (ℓ R▹ τ) = (ren ρ ℓ) R▹ (ren ρ τ)
ren ρ ⌊ ℓ ⌋ = ⌊ (ren ρ ℓ) ⌋

weaken : NormalType Δ κ₂ → NormalType (Δ ,, κ₁) κ₂
weaken = ren S
