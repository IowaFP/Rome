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
renPred : Renaming Δ₁ Δ₂ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]
-- renRow : Renaming Δ₁ Δ₂ → Row Δ₁ κ → Row Δ₂ κ


renNE ρ (` x) = ` (ρ x)
renNE ρ (τ₁ · τ₂) = renNE ρ τ₁ · ren ρ τ₂
renNE ρ (F <$> τ) = ren ρ F <$> (renNE ρ τ)

ren ρ Unit   = Unit
ren ρ (ne τ {g}) = ne (renNE ρ τ) {g}
ren ρ (l ▹ τ) = (ren ρ l) ▹ (ren ρ τ)
ren ρ (`λ τ) = `λ (ren (lift ρ) τ)
ren ρ (τ₁ `→ τ₂) = (ren ρ τ₁) `→ (ren ρ τ₂)
ren ρ (π ⇒ τ) = renPred ρ π ⇒ ren ρ τ
ren ρ (`∀ κ τ) = `∀ κ (ren (lift ρ) τ)
ren ρ (μ τ) = μ (ren ρ τ)
ren ρ (lab x) = lab x
ren ρ ⌊ ℓ ⌋ = ⌊ (ren ρ ℓ) ⌋
ren ρ (Π τ) = Π (ren ρ τ)
ren ρ (ΠL τ) = ΠL (ren ρ τ)
ren ρ (Σ τ) = Σ (ren ρ τ)
ren ρ (ΣL τ) = ΣL (ren ρ τ)

renPred ρ (ρ₁ · ρ₂ ~ ρ₃) = (ren ρ ρ₁) · (ren ρ ρ₂) ~ (ren ρ ρ₃)
renPred ρ (ρ₁ ≲ ρ₂) = (ren ρ ρ₁) ≲ (ren ρ ρ₂)

-- renRow ρ (l ▹ τ) = (ren ρ l) ▹ (ren ρ τ)

--------------------------------------------------------------------------------
-- Weakening

weaken : NormalType Δ κ₂ → NormalType (Δ ,, κ₁) κ₂
weaken = ren S


--------------------------------------------------------------------------------
-- η-expansion

-- This will take more thought
η-expand : NeutralType Δ (κ₁ `→ κ₂) → NormalType Δ (κ₁ `→ κ₂)
η-expand {κ₂ = ★} (` α) = `λ (ne ((` (S α)) · (ne (` Z) {ground = {!   !}})))
η-expand {κ₂ = L} (` α) = {!   !}
η-expand {κ₂ = κ₂ `→ κ₃} (` α) = {!   !}
η-expand {κ₂ = R[ κ₂ ]} (` α) = {!   !}
η-expand (n · τ) = {!   !}
