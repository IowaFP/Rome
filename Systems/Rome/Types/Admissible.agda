
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

Functor : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → 
          Type Δ (((★ ℓ) `→ (★ ℓ)) `→ ★ (lsuc ℓ))
Functor {ℓ = ℓ} = `λ (★ ℓ `→ ★ ℓ) -- F
               (`∀ (★ ℓ)         -- t
               (`∀ (★ ℓ)         -- s
               ((t `→ s) `→ (F ·[ t ]) `→ F ·[ s ])))
      where
        F = tvar (S (S Z))
        t = tvar (S Z)
        s = tvar Z

-- FmapT-ρ : ∀ {ℓ ℓΔ} {Δ : KEnv ℓΔ} → 
--           Type Δ (R[ ★ ℓ `→ ★ ℓ ] `→ ★ (lsuc ℓ))
-- FmapT-ρ {ℓ = ℓ} = `λ (R[ ★ ℓ `→ ★ ℓ ]) (Π (⌈ FmapT ⌉· (tvar Z)))
