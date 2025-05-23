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
-- renₖNEapp     : Renamingₖ Δ₁ Δ₂ → NeutralApp Δ₁ κ → NeutralApp Δ₂ κ

renₖNF     : Renamingₖ Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
renRowₖNF : Renamingₖ Δ₁ Δ₂ → SimpleRow NormalType Δ₁ R[ κ ] → SimpleRow NormalType Δ₂ R[ κ ]
renPredₖNF : Renamingₖ Δ₁ Δ₂ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]
orderedRenRowₖNF : (r : Renamingₖ Δ₁ Δ₂) → (xs : SimpleRow NormalType Δ₁ R[ κ ]) → NormalOrdered xs → 
                 NormalOrdered (renRowₖNF r xs)
-- isNormalRenₖNF : (r : Renamingₖ Δ₁ Δ₂) (τ : NormalType Δ₁ κ) → IsNormal τ → IsNormal (renₖNF r τ)


renₖNE r (` x) = ` (r x)
renₖNE ρ (τ₁ · τ₂) = renₖNE ρ τ₁ · renₖNF ρ τ₂
renₖNE ρ (r <$> x) = renₖNF ρ r <$> renₖNE ρ x

-- renₖNE r (app x) = app (renₖNEapp r x)
-- renₖNE r (ρ₂ ─₁ ρ₁) = renₖNE r ρ₂ ─₁ renₖNF r ρ₁
-- renₖNE r ((ρ₂ ─₂ ρ₁) {isNorm}) = (renₖNF r ρ₂ ─₂ renₖNE r ρ₁) {fromWitness (isNormalRenₖNF r ρ₂ (toWitness isNorm))}

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
-- renₖNF r (ρ <$> x ─₁ ρ₁) = (renₖNF r ρ) <$> (renₖNE r x) ─₁ (renₖNF r ρ₁)
renₖNF ρ (l ▹ₙ τ) = renₖNE ρ l ▹ₙ (renₖNF ρ τ)
-- renₖNF ρ (r <$> x) = renₖNF ρ r <$> renₖNE ρ x
-- renₖNF ρ (x ─₁ r) = renₖNE ρ x ─₁ renₖNF ρ r
-- renₖNF ρ (x ─₂ r) = (renₖNF ρ x ─₂ renₖNE ρ r) {isNormal = {!!}}
renₖNF r (ρ₂ ─ ρ₁) = (renₖNF r ρ₂ ─ renₖNF r ρ₁) {nsr = {!!}}
-- renₖNF ρ ([ x ▹ r ]─ r₁) = [ renₖNE ρ x ▹ renₖNF ρ r ]─ renₖNF ρ r₁

renPredₖNF ρ (ρ₁ · ρ₂ ~ ρ₃) = (renₖNF ρ ρ₁) · (renₖNF ρ ρ₂) ~ (renₖNF ρ ρ₃)
renPredₖNF ρ (ρ₁ ≲ ρ₂) = (renₖNF ρ ρ₁) ≲ (renₖNF ρ ρ₂)

renRowₖNF _ [] = []
renRowₖNF r ((l , τ) ∷ ρ) = (l , renₖNF r τ) ∷ renRowₖNF r ρ

-- isNormalRenₖNF r (`λ x) witness = tt
-- isNormalRenₖNF r (x `→ x₁) witness = tt
-- isNormalRenₖNF r (`∀ x) witness = tt
-- isNormalRenₖNF r (μ x) witness = tt
-- isNormalRenₖNF r (π ⇒ x) witness = tt
-- isNormalRenₖNF r (⦅ ρ ⦆ oρ) witness = tt
-- isNormalRenₖNF r (lab l) witness = tt
-- isNormalRenₖNF r ⌊ x ⌋ witness = tt
-- isNormalRenₖNF r (Π x) witness = tt
-- isNormalRenₖNF r (Σ x) witness = tt
-- isNormalRenₖNF r (l ▹ₙ τ) witness = tt
-- isNormalRenₖNF r (ρ <$> x ─ ρ₁) witness = tt

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
