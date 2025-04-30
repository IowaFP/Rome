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
renRowₖNF : Renamingₖ Δ₁ Δ₂ → SimpleRow NormalType Δ₁ R[ κ ] → SimpleRow NormalType Δ₂ R[ κ ]
renPredₖNF : Renamingₖ Δ₁ Δ₂ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]


renₖNE ρ (` x) = ` (ρ x)
renₖNE ρ (τ₁ · τ₂) = renₖNE ρ τ₁ · renₖNF ρ τ₂
renₖNE ρ (F <$> τ) = renₖNF ρ F <$> (renₖNE ρ τ)
renₖNE r (ρ₂ ─₁ ρ₁) = renₖNE r ρ₂ ─₁ (renₖNF r ρ₁)
renₖNE r (ρ₂ ─₂ ρ₁) = renₖNF r ρ₂ ─₂ (renₖNE r ρ₁)

renₖNF ρ (ne τ {g}) = ne (renₖNE ρ τ) {g}
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
renₖNF r ⦅ ρ ⦆ = ⦅ renRowₖNF r ρ ⦆

renPredₖNF ρ (ρ₁ · ρ₂ ~ ρ₃) = (renₖNF ρ ρ₁) · (renₖNF ρ ρ₂) ~ (renₖNF ρ ρ₃)
renPredₖNF ρ (ρ₁ ≲ ρ₂) = (renₖNF ρ ρ₁) ≲ (renₖNF ρ ρ₂)

renRowₖNF _ [] = []
renRowₖNF r ((l , τ) ∷ ρ) = (l , renₖNF r τ) ∷ renRowₖNF r ρ

renRowₖNF-isMap : ∀ (φ : Renamingₖ Δ₁ Δ₂) (xs : SimpleRow NormalType Δ₁ R[ κ ]) → 
                  renRowₖNF φ xs ≡ map (overᵣ (renₖNF φ)) xs
renRowₖNF-isMap φ [] = refl
renRowₖNF-isMap φ (x ∷ xs) = cong₂ _∷_ refl (renRowₖNF-isMap φ xs)

--------------------------------------------------------------------------------
-- Weakening

weakenₖNF : NormalType Δ κ₂ → NormalType (Δ ,, κ₁) κ₂
weakenₖNF = renₖNF S

weakenₖNE : NeutralType Δ κ₂ → NeutralType (Δ ,, κ₁) κ₂
weakenₖNE = renₖNE S 

weakenPredₖNF : NormalPred Δ R[ κ₂ ] → NormalPred (Δ ,, κ₁) R[ κ₂ ]
weakenPredₖNF = renPredₖNF S
