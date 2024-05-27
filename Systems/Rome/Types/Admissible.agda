{-# OPTIONS --safe #-}
module Rome.Types.Admissible where

open import Preludes.Level
open import Preludes.Data

open import Rome.GVars.Kinds
open import Rome.Kinds
open import Rome.Types.Syntax

--------------------------------------------------------------------------------
-- Permissable types.

-- The unit type.
U : ∀ {ℓ} → Type Δ (★ ℓ)
U = ⌊ lab "unit" ⌋

-- The empty record.
∅ : Type Δ (★ ℓ)
∅ = Π ε

-- The impossible variant.
⊥ : Type Δ (★ ℓ)
⊥ = Σ ε
