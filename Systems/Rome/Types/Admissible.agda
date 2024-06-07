
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

μΣ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → Type Δ R[ (★ ℓ) `→ (★ ℓ) ] → Type Δ (★ ℓ)
μΣ ρ = μ (Σ ρ)

--------------------------------------------------------------------------------
-- type of fmap : ∀ t s → F t → F s

FmapT : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → 
          Type Δ (★ ℓ `→ ★ ℓ) → 
          Type Δ (★ (lsuc ℓ))
FmapT {ℓ = ℓ} F = (`∀ (★ ℓ)            -- t
                  (`∀ (★ ℓ)            -- s
                      ((t `→ s) `→ (K² F ·[ t ]) `→  K² F ·[ s ])))
      where
        t = tvar (S Z)
        s = tvar Z
