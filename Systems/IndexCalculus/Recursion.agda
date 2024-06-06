{-# OPTIONS --allow-unsolved-metas  #-}
module IndexCalculus.Recursion where

open import Preludes.Level
open import Preludes.Data
open import IndexCalculus.Rows
open import IndexCalculus.Variants
-- open import Preludes.Partiality

--------------------------------------------------------------------------------
-- Denoting recursive types.

{-# NO_POSITIVITY_CHECK #-}
data Mu {ℓ} (F : Set ℓ → Set ℓ)  : Set ℓ where
  In : F (Mu F) → Mu F

out : ∀ {ℓ} {F : Set ℓ → Set ℓ} → Mu F → F (Mu F)
out (In x) = x
