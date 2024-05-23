{-# OPTIONS --safe #-}
module ROmega.Types.Admissible where

open import Preludes.Level
open import Preludes.Data

open import ROmega.GVars.Kinds
open import ROmega.Kinds
open import ROmega.Types.Syntax

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
