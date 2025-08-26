module Rome.Both.IndexCalculus.Variants.Properties where

open import Rome.Prelude
open import Rome.Both.Preludes.Level hiding (suc ; zero)

open import Rome.Both.IndexCalculus.Rows
open import Rome.Both.IndexCalculus.Variants
open import Rome.Both.IndexCalculus.GVars

--------------------------------------------------------------------------------
-- inverse injection.

inj⁻¹ : ρ₁ · ρ₂ ~ ρ₃ → Σ ρ₃ → Σ ρ₁ or Σ ρ₂
inj⁻¹ (l , r) (i , P) with l i
... | left  (j , eq) rewrite sym eq = left (j , P )
... | right (j , eq) rewrite sym eq = right (j , P )

