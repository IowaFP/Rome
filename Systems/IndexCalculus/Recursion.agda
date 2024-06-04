{-# OPTIONS --allow-unsolved-metas #-}
module IndexCalculus.Recursion where

open import Preludes.Level
open import Preludes.Data
open import IndexCalculus.Rows
open import IndexCalculus.Variants

--------------------------------------------------------------------------------
-- Gas'd representation of recursive types.

mu : ∀ {ℓ} → (F : Set ℓ → Set ℓ) → ℕ → Set ℓ
mu {ℓ} F ℕ.zero = ⊤
mu {ℓ} F (ℕ.suc n) = F (mu F n)
