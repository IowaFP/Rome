{-# OPTIONS --safe #-}
module Rome.Operational.Types.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

--------------------------------------------------------------------------------
-- Type Renaming

Renamingₖ : KEnv → KEnv → Set
Renamingₖ Δ₁ Δ₂ = ∀ {κ} → TVar Δ₁ κ → TVar Δ₂ κ

-- (extensional) equivalence of renamings
_≈_ : ∀ {Δ₁} (ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂) → Set
_≈_ {Δ₁ = Δ₁} ρ₁ ρ₂ = ∀ {κ} (x : TVar Δ₁ κ) → ρ₁ x ≡ ρ₂ x


-- lifting over binders.
liftₖ : Renamingₖ Δ₁ Δ₂ → Renamingₖ (Δ₁ ,, κ) (Δ₂ ,, κ)
liftₖ ρ Z = Z
liftₖ ρ (S x) = S (ρ x)

renₖ : Renamingₖ Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
renPredₖ : Renamingₖ Δ₁ Δ₂ → Pred Type Δ₁ R[ κ ] → Pred Type Δ₂ R[ κ ]
renRowₖ : Renamingₖ Δ₁ Δ₂ → SimpleRow Type Δ₁ R[ κ ] → SimpleRow Type Δ₂ R[ κ ]
orderedRenRowₖ : (r : Renamingₖ Δ₁ Δ₂) → (xs : SimpleRow Type Δ₁ R[ κ ]) → Ordered xs → 
                 Ordered (renRowₖ r xs)

renₖ r (` x) = ` (r x)
renₖ r (`λ τ) = `λ (renₖ (liftₖ r) τ)
renₖ r (τ₁ · τ₂) = (renₖ r τ₁) · (renₖ r τ₂)
renₖ r (τ₁ `→ τ₂) = (renₖ r τ₁) `→ (renₖ r τ₂)
renₖ r (π ⇒ τ) = renPredₖ r π ⇒ renₖ r τ 
renₖ r (`∀ τ) = `∀ (renₖ (liftₖ r) τ)
renₖ r (μ F) = μ (renₖ r F)
renₖ r (Π {notLabel = nl}) = Π {notLabel = nl}
renₖ r (Σ {notLabel = nl}) = Σ {notLabel = nl}
renₖ r (lab x) = lab x
renₖ r ⌊ ℓ ⌋ = ⌊ (renₖ r ℓ) ⌋
renₖ r (f <$> m) = renₖ r f <$> renₖ r m
renₖ r (⦅ xs ⦆ oxs) = ⦅ renRowₖ r xs ⦆ (fromWitness (orderedRenRowₖ r xs (toWitness oxs)))
renₖ r (ρ₂ ─ ρ₁) = renₖ r ρ₂ ─ renₖ r ρ₁
renₖ r (l ▹ τ) = renₖ r l ▹ renₖ r τ

renPredₖ ρ (ρ₁ · ρ₂ ~ ρ₃) = renₖ ρ ρ₁ · renₖ ρ ρ₂ ~ renₖ ρ ρ₃
renPredₖ ρ (ρ₁ ≲ ρ₂) = (renₖ ρ ρ₁) ≲ (renₖ ρ ρ₂) 

renRowₖ r [] = [] 
renRowₖ r ((l , τ) ∷ xs) = (l , renₖ r τ) ∷ renRowₖ r xs

orderedRenRowₖ r [] oxs = tt
orderedRenRowₖ r ((l , τ) ∷ []) oxs = tt
orderedRenRowₖ r ((l₁ , τ) ∷ (l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , orderedRenRowₖ r ((l₂ , υ) ∷ xs) oxs

weakenₖ : Type Δ κ₂ → Type (Δ ,, κ₁) κ₂
weakenₖ = renₖ S

weakenPredₖ : Pred Type Δ R[ κ₂ ] → Pred Type (Δ ,, κ₁) R[ κ₂ ]
weakenPredₖ = renPredₖ S

