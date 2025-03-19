{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Normal.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (liftₖ ; Renamingₖ)

open import Rome.Operational.Types.Normal.Syntax

--------------------------------------------------------------------------------
-- Normal Type renaming.

renₖNE   : Renamingₖ Δ₁ Δ₂ → NeutralType Δ₁ κ → NeutralType Δ₂ κ
renₖNF     : Renamingₖ Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
renPredₖNF : Renamingₖ Δ₁ Δ₂ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]


renₖNE ρ (` x) = ` (ρ x)
renₖNE ρ (τ₁ · τ₂) = renₖNE ρ τ₁ · renₖNF ρ τ₂
renₖNE ρ (F <$> τ) = renₖNF ρ F <$> (renₖNE ρ τ)

renₖNF ρ ε   = ε
renₖNF ρ (ne τ {g}) = ne (renₖNE ρ τ) {g}
renₖNF ρ (l ▹ τ) = (renₖNF ρ l) ▹ (renₖNF ρ τ)
renₖNF ρ (`λ τ) = `λ (renₖNF (liftₖ ρ) τ)
renₖNF ρ (τ₁ `→ τ₂) = (renₖNF ρ τ₁) `→ (renₖNF ρ τ₂)
renₖNF ρ (π ⇒ τ) = renPredₖNF ρ π ⇒ renₖNF ρ τ
renₖNF ρ (`∀ τ) = `∀ (renₖNF (liftₖ ρ) τ)
renₖNF ρ (μ τ) = μ (renₖNF ρ τ)
renₖNF ρ (lab x) = lab x
renₖNF ρ ⌊ ℓ ⌋ = ⌊ (renₖNF ρ ℓ) ⌋
renₖNF ρ (Π τ) = Π (renₖNF ρ τ)
renₖNF ρ (ΠL τ) = ΠL (renₖNF ρ τ)
renₖNF ρ (Σ τ) = Σ (renₖNF ρ τ)
renₖNF ρ (ΣL τ) = ΣL (renₖNF ρ τ)

renPredₖNF ρ (ρ₁ · ρ₂ ~ ρ₃) = (renₖNF ρ ρ₁) · (renₖNF ρ ρ₂) ~ (renₖNF ρ ρ₃)
renPredₖNF ρ (ρ₁ ≲ ρ₂) = (renₖNF ρ ρ₁) ≲ (renₖNF ρ ρ₂)

-- renRow ρ (l ▹ τ) = (renₖNF ρ l) ▹ (renₖNF ρ τ)

--------------------------------------------------------------------------------
-- Weakening

weakenₖNF : NormalType Δ κ₂ → NormalType (Δ ,, κ₁) κ₂
weakenₖNF = renₖNF S

weakenₖNE : NeutralType Δ κ₂ → NeutralType (Δ ,, κ₁) κ₂
weakenₖNE = renₖNE S 

weakenPredₖNF : NormalPred Δ R[ κ₂ ] → NormalPred (Δ ,, κ₁) R[ κ₂ ]
weakenPredₖNF = renPredₖNF S
