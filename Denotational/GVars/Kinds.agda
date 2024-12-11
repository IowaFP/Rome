module Rome.Denotational.GVars.Kinds where

open import Preludes.Level
open import Rome.Denotational.Kinds.Syntax

--------------------------------------------------------------------------------
-- Generalized Vars.

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ι : Level
  ℓΔ ℓL ℓΓ ℓΦ ℓκ ℓκ₁ ℓκ₂ ℓκ₃ ℓκ₄ ℓκ₅ : Level
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
  κ₄ : Kind ℓκ₄
  κ₅ : Kind ℓκ₅
  Δ : KEnv ℓΔ
