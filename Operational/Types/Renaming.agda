module Rome.Operational.Types.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

--------------------------------------------------------------------------------
-- Type Renaming

Renamingₖ : KEnv → KEnv → Set
Renamingₖ Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → KVar Δ₂ κ

-- (extensional) equivalence of renamings
_≈_ : ∀ {Δ₁} (ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂) → Set
_≈_ {Δ₁ = Δ₁} ρ₁ ρ₂ = ∀ {κ} (x : KVar Δ₁ κ) → ρ₁ x ≡ ρ₂ x


-- ↑ing over binders.
liftₖ : Renamingₖ Δ₁ Δ₂ → Renamingₖ (Δ₁ ,, κ) (Δ₂ ,, κ)
liftₖ ρ Z = Z
liftₖ ρ (S x) = S (ρ x)

renₖ : Renamingₖ Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
renPredₖ : Renamingₖ Δ₁ Δ₂ → Pred Type Δ₁ R[ κ ] → Pred Type Δ₂ R[ κ ]
renRowₖ : Renamingₖ Δ₁ Δ₂ → SimpleRow Type Δ₁ R[ κ ] → SimpleRow Type Δ₂ R[ κ ]
labelsFixedByRen : (ρ : Renamingₖ Δ₁ Δ₂) → (sr : SimpleRow Type Δ₁ R[ κ ]) → labels (renRowₖ ρ sr) ≡ labels sr

renₖ ρ ε  = ε
renₖ ρ (` x) = ` (ρ x)
renₖ ρ (`λ τ) = `λ (renₖ (liftₖ ρ) τ)
renₖ ρ (τ₁ · τ₂) = (renₖ ρ τ₁) · (renₖ ρ τ₂)
renₖ ρ (τ₁ `→ τ₂) = (renₖ ρ τ₁) `→ (renₖ ρ τ₂)
renₖ ρ (π ⇒ τ) = renPredₖ ρ π ⇒ renₖ ρ τ 
renₖ ρ (`∀ τ) = `∀ (renₖ (liftₖ ρ) τ)
renₖ ρ (μ F) = μ (renₖ ρ F)
renₖ ρ (Π ) = Π 
renₖ ρ Σ = Σ
renₖ ρ (lab x) = lab x
renₖ ρ (l ▹ τ) = renₖ ρ l ▹ renₖ ρ τ
renₖ ρ ⌊ ℓ ⌋ = ⌊ (renₖ ρ ℓ) ⌋
renₖ ρ (f <$> m) = renₖ ρ f <$> renₖ ρ m
renₖ ρ (⦅ sr ⦆ noDup) = ⦅ renRowₖ ρ sr ⦆ (subst (λ x → True (noDup? x)) (sym (labelsFixedByRen ρ sr)) noDup) 

renRowₖ ρ (ℓ ▹ τ) = ℓ ▹ (renₖ ρ τ)
renRowₖ ρ ((ℓ ▹ τ ⸴ ρ₁)) = (ℓ ▹ (renₖ ρ τ) ⸴ renRowₖ ρ ρ₁) -- {subst (λ x → True (ℓ ∉? x)) (sym (labelsFixedByRen ρ ρ₁)) noDup}

labelsFixedByRen ρ (ℓ ▹ τ) = refl
labelsFixedByRen ρ (ℓ ▹ τ ⸴ ρ₁) rewrite labelsFixedByRen ρ ρ₁ = refl

renPredₖ ρ (ρ₁ · ρ₂ ~ ρ₃) = renₖ ρ ρ₁ · renₖ ρ ρ₂ ~ renₖ ρ ρ₃
renPredₖ ρ (ρ₁ ≲ ρ₂) = (renₖ ρ ρ₁) ≲ (renₖ ρ ρ₂) 

weakenₖ : Type Δ κ₂ → Type (Δ ,, κ₁) κ₂
weakenₖ = renₖ S

weakenRowₖ : SimpleRow Type Δ R[ κ₂ ] → SimpleRow Type (Δ ,, κ₁) R[ κ₂ ] 
weakenRowₖ = renRowₖ S 

--------------------------------------------------------------------------------
-- Just proving a petty point 

RenRowIsMap : (ρ : Renamingₖ Δ₁ Δ₂) → 
              (sr : SimpleRow Type Δ₁ R[ κ ]) → 
              renRowₖ ρ sr ≡ mapSimpleRow (renₖ ρ) sr
RenRowIsMap ρ (ℓ ▹ τ) = refl
RenRowIsMap ρ (ℓ ▹ τ ⸴ sr₁) rewrite RenRowIsMap ρ sr₁ = refl