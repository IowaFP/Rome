module Rome.Both.IndexCalculus.GVars where

open import Rome.Prelude
open import Rome.Preludes.Level hiding (suc ; zero)

open import Rome.Both.IndexCalculus.Rows

--------------------------------------------------------------------------------
-- Generalized variables.

variable
  ℓ : Level
  A : Set ℓ
  ρ ρ₁ ρ₂ ρ₃ : Row {ℓ} A
