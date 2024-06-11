module IndexCalculus.GVars where

open import Prelude
open import Preludes.Level hiding (suc ; zero)

open import IndexCalculus.Rows

--------------------------------------------------------------------------------
-- Generalized variables.

variable
  ℓ : Level
  A : Set ℓ
  ρ ρ₁ ρ₂ ρ₃ : Row {ℓ} A
