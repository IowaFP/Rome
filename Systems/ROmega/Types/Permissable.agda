{-# OPTIONS --safe #-}
module ROmega.Types.Permissable where

open import Preludes.Level
open import Preludes.Data

open import ROmega.GVars.Kinds
open import ROmega.Kinds
open import ROmega.Types.Syntax

--------------------------------------------------------------------------------
-- Permissable types.

-- The empty record.
∅ : Type Δ (★ ℓ)
∅ = Π ε

-- The impossible variant.
⊥ : Type Δ (★ ℓ)
⊥ = Σ ε
