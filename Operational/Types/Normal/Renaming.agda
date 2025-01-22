module Rome.Operational.Types.Normal.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (lift ; Renaming)
open import Rome.Operational.Types.Properties

open import Rome.Operational.Types.Normal.Syntax

--------------------------------------------------------------------------------
-- Normal Type renaming.


-- postulate
--     renNE : Renaming Δ₁ Δ₂ → NeutralType Δ₁ κ → NeutralType Δ₂ κ
--     ren : Renaming Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
--     renRow : Renaming Δ₁ Δ₂ → Row Δ₁ κ → Row Δ₂ κ

renNE : Renaming Δ₁ Δ₂ → NeutralType Δ₁ κ → NeutralType Δ₂ κ
ren : Renaming Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
renRow : Renaming Δ₁ Δ₂ → Row Δ₁ κ → Row Δ₂ κ

renNE ρ (` x) = ` (ρ x)
renNE ρ (τ₁ · τ₂) = renNE ρ τ₁ · ren ρ τ₂
renNE ρ (Π τ) = Π (renNE ρ τ)
renNE ρ (Σ τ) = Σ (renNE ρ τ)
renNE ρ (F <$> τ) = ren ρ F <$> (renNE ρ τ)

ren ρ Unit   = Unit
ren ρ (ne τ) = ne (renNE ρ τ)
ren ρ (row τ) = row (renRow ρ τ)
ren ρ (`λ τ) = `λ (ren (lift ρ) τ)
ren ρ (τ₁ `→ τ₂) = (ren ρ τ₁) `→ (ren ρ τ₂)
ren ρ (`∀ κ τ) = `∀ κ (ren (lift ρ) τ)
ren ρ (μ τ) = μ (ren ρ τ)
ren ρ (lab x) = lab x
ren ρ ⌊ ℓ ⌋ = ⌊ (ren ρ ℓ) ⌋
ren ρ (Π τ) = Π (renRow ρ τ)
ren ρ (ΠL τ) = ΠL (renRow ρ τ)
ren ρ (Σ τ) = Σ (renRow ρ τ)
ren ρ (ΣL τ) = ΣL (renRow ρ τ)

renRow ρ (l ▹ τ) = (ren ρ l) ▹ (ren ρ τ)

--------------------------------------------------------------------------------
-- Weakening

weaken : NormalType Δ κ₂ → NormalType (Δ ,, κ₁) κ₂
weaken = ren S

