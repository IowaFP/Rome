{-# OPTIONS --safe #-}
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
orderedRenRowₖNF : (r : Renamingₖ Δ₁ Δ₂) → (xs : SimpleRow NormalType Δ₁ R[ κ ]) → NormalOrdered xs → 
                 NormalOrdered (renRowₖNF r xs)
nsrRenₖNF : ∀ (r : Renamingₖ Δ₁ Δ₂) (ρ₁ ρ₂ : NormalType Δ₁ R[ κ ]) → NotSimpleRow ρ₂ or NotSimpleRow ρ₁ → 
              NotSimpleRow (renₖNF r ρ₂) or NotSimpleRow (renₖNF r ρ₁)
nsrRenₖNF' : ∀ (r : Renamingₖ Δ₁ Δ₂) (ρ : NormalType Δ₁ R[ κ ]) → NotSimpleRow ρ → 
              NotSimpleRow (renₖNF r ρ)

¬idRenₖNF : ∀ (r : Renamingₖ Δ₁ Δ₂) (φ : NormalType Δ₁ (κ₁ `→ κ₂)) → 
              NotId φ → NotId (renₖNF r φ)

renₖNE r (` x) = ` (r x)
renₖNE ρ (τ₁ · τ₂) = renₖNE ρ τ₁ · renₖNF ρ τ₂


renₖNF ρ (ne τ {g}) = ne (renₖNE ρ τ) {g}
renₖNF ρ (`λ τ) = `λ (renₖNF (liftₖ ρ) τ)
renₖNF ρ (τ₁ `→ τ₂) = (renₖNF ρ τ₁) `→ (renₖNF ρ τ₂)
renₖNF ρ (π ⇒ τ) = renPredₖNF ρ π ⇒ renₖNF ρ τ
renₖNF ρ (`∀ τ) = `∀ (renₖNF (liftₖ ρ) τ)
renₖNF ρ (μ τ) = μ (renₖNF ρ τ)
renₖNF ρ (lab x) = lab x
renₖNF ρ ⌊ ℓ ⌋ = ⌊ (renₖNF ρ ℓ) ⌋
renₖNF ρ (Π τ) = Π (renₖNF ρ τ)
renₖNF ρ (Σ τ) = Σ (renₖNF ρ τ)
renₖNF r (⦅ ρ ⦆ oρ) = ⦅ renRowₖNF r ρ ⦆ (fromWitness (orderedRenRowₖNF r ρ (toWitness oρ)))
renₖNF ρ (l ▹ₙ τ) = renₖNE ρ l ▹ₙ (renₖNF ρ τ)
renₖNF r ((ρ₂ ─ ρ₁) {nsr}) = (renₖNF r ρ₂ ─ renₖNF r ρ₁) {nsr = fromWitness (nsrRenₖNF r ρ₁ ρ₂ (toWitness nsr))}
renₖNF ρ ((φ <$> x) ¬id) = (renₖNF ρ φ <$> renₖNE ρ x) (fromWitness (¬idRenₖNF ρ φ (toWitness ¬id)))

renPredₖNF ρ (ρ₁ · ρ₂ ~ ρ₃) = (renₖNF ρ ρ₁) · (renₖNF ρ ρ₂) ~ (renₖNF ρ ρ₃)
renPredₖNF ρ (ρ₁ ≲ ρ₂) = (renₖNF ρ ρ₁) ≲ (renₖNF ρ ρ₂)

renRowₖNF _ [] = []
renRowₖNF r ((l , τ) ∷ ρ) = (l , renₖNF r τ) ∷ renRowₖNF r ρ

nsrRenₖNF' r (ne x) nsr = tt
nsrRenₖNF' r (ρ ─ ρ₁) nsr = tt
nsrRenₖNF' r (x ▹ₙ ρ) nsr = tt
nsrRenₖNF' r ((φ <$> ρ) _) nsr = tt

nsrRenₖNF r ρ₁ ρ₂ (left x) = left (nsrRenₖNF' r ρ₂ x)
nsrRenₖNF r ρ₁ ρ₂ (right y) = right (nsrRenₖNF' r ρ₁ y) 

¬idRenₖNF r (`λ (ne (` (S α)))) ¬-id = tt
¬idRenₖNF r (`λ (ne (x · τ))) ¬-id = tt
¬idRenₖNF r (`λ ((φ <$> x) x₁)) ¬-id = tt
¬idRenₖNF r (`λ (`λ φ)) ¬-id = tt
¬idRenₖNF r (`λ (φ `→ φ₁)) ¬-id = tt
¬idRenₖNF r (`λ (`∀ φ)) ¬-id = tt
¬idRenₖNF r (`λ (μ φ)) ¬-id = tt
¬idRenₖNF r (`λ (π ⇒ φ)) ¬-id = tt
¬idRenₖNF r (`λ (⦅ ρ ⦆ oρ)) ¬-id = tt
¬idRenₖNF r (`λ (lab l)) ¬-id = tt
¬idRenₖNF r (`λ ⌊ φ ⌋) ¬-id = tt
¬idRenₖNF r (`λ (Π φ)) ¬-id = tt
¬idRenₖNF r (`λ (Σ φ)) ¬-id = tt
¬idRenₖNF r (`λ (φ ─ φ₁)) ¬-id = tt
¬idRenₖNF r (`λ (l ▹ₙ φ)) ¬-id = tt

orderedRenRowₖNF r [] oxs = tt
orderedRenRowₖNF r ((l , τ) ∷ []) oxs = tt
orderedRenRowₖNF r ((l₁ , τ) ∷ (l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , orderedRenRowₖNF r ((l₂ , υ) ∷ xs) oxs

renRowₖNF-isMap : ∀ (r : Renamingₖ Δ₁ Δ₂) (xs : SimpleRow NormalType Δ₁ R[ κ ]) → 
                  renRowₖNF r xs ≡ map (overᵣ (renₖNF r)) xs 
renRowₖNF-isMap r [] = refl
renRowₖNF-isMap r (x ∷ xs) = cong₂ _∷_ refl (renRowₖNF-isMap r xs)

--------------------------------------------------------------------------------
-- Weakening

weakenₖNF : NormalType Δ κ₂ → NormalType (Δ ,, κ₁) κ₂
weakenₖNF = renₖNF S

weakenₖNE : NeutralType Δ κ₂ → NeutralType (Δ ,, κ₁) κ₂
weakenₖNE = renₖNE S 

weakenPredₖNF : NormalPred Δ R[ κ₂ ] → NormalPred (Δ ,, κ₁) R[ κ₂ ]
weakenPredₖNF = renPredₖNF S
