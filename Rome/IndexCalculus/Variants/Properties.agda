{-# OPTIONS --allow-unsolved-metas #-}
module IndexCalculus.Variants.Properties where

open import Prelude
open import Preludes.Level hiding (suc ; zero)

open import IndexCalculus.Rows
open import IndexCalculus.Variants
open import IndexCalculus.GVars

--------------------------------------------------------------------------------
--

inj⁻¹ : ρ₁ · ρ₂ ~ ρ₃ → Σ ρ₃ → Σ ρ₁ or Σ ρ₂
inj⁻¹ (l , r) (i , P) with l i
... | left  (j , eq) rewrite sym eq = left (j , P )
... | right (j , eq) rewrite sym eq = right (j , P )

--------------------------------------------------------------------------------
--
