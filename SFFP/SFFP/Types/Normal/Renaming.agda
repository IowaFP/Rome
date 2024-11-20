module SFFP.Types.Normal.Renaming where

open import SFFP.Prelude
open import SFFP.Kinds.Syntax
open import SFFP.Kinds.GVars

open import SFFP.Types.Syntax
open import SFFP.Types.Renaming using (↑ ; Renaming)
open import SFFP.Types.Properties

open import SFFP.Types.Normal.Syntax

--------------------------------------------------------------------------------
-- Normal Type renaming.

renNE : Renaming Δ₁ Δ₂ → NeutralType Δ₁ κ → NeutralType Δ₂ κ
ren : Renaming Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ

renNE ρ (` x) = ` (ρ x)
renNE ρ (τ₁ · τ₂) = renNE ρ τ₁ · ren ρ τ₂

ren ρ (ne τ) = ne (renNE ρ τ)
ren ρ (`λ τ) = `λ (ren (↑ ρ) τ)
ren ρ (τ₁ `→ τ₂) = (ren ρ τ₁) `→ (ren ρ τ₂)
ren ρ (`∀ κ τ) = `∀ κ (ren (↑ ρ) τ)
ren ρ (μ τ) = μ (ren (↑ ρ) τ)

weaken : NormalType Δ κ₂ → NormalType (Δ ,, κ₁) κ₂
weaken = ren S
