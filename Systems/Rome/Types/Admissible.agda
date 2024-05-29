
module Rome.Types.Admissible where

open import Preludes.Level
open import Preludes.Data


open import Rome.Kinds
open import Rome.Types.Syntax
open import Rome.Types.Substitution

--------------------------------------------------------------------------------
-- Permissable types.

-- The unit type.
U : ∀ {ℓ ℓΔ}{Δ : KEnv ℓΔ} → Type Δ (★ ℓ)
U = ⌊ lab "unit" ⌋

-- The empty record.
∅ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ ℓ)
∅ = Π ε

-- The impossible variant.
⊥ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (★ ℓ)
⊥ = Σ ε

Σ₂ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ (R[ ★ ℓ `→ ★ ℓ ]) → Type Δ (★ ℓ `→ ★ ℓ)
Σ₂ {ℓ = ℓ} ρ = `λ (★ ℓ) (Σ ((K ρ) ·⌈ tvar Z ⌉))
