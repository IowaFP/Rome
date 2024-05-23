{-# OPTIONS --safe #-}
module ROmega.GVars.Kinds where

open import Preludes.Level
open import ROmega.Kinds.Syntax

--------------------------------------------------------------------------------
-- Generalized Vars.

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ι : Level
  ℓΔ ℓΓ ℓΦ ℓκ ℓκ₁ ℓκ₂ ℓκ₃ : Level
  -- The types below "depend" on levels above.
  -- In practice, Agda does not respect this dependency.
  -- E.g., if you use κ below, then κ will have type "Kind κ.ℓκ".
  -- In other words, Agda will instantiate a fresh variable κ.ℓκ, and,
  -- most importantly, ℓκ ≠ κ.ℓκ.
  -- (Heed this note wisely. It is very easy to make this mistake.)
  κ κ' : Kind ℓκ
  κ₁ : Kind ℓκ₁
  κ₂ : Kind ℓκ₂
  κ₃ : Kind ℓκ₃
  Δ : KEnv ℓΔ
