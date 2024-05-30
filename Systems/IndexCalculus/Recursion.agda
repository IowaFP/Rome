{-# OPTIONS --allow-unsolved-metas #-}
module IndexCalculus.Recursion where

open import Preludes.Level
open import Preludes.Data
open import IndexCalculus.Rows
open import IndexCalculus.Variants

--------------------------------------------------------------------------------
-- Denoting recursive types.

Functor = λ ℓ → Set ℓ → Set ℓ

{-# NO_POSITIVITY_CHECK #-}
data  Mu {ℓ} (F : Functor ℓ) : Set ℓ where
  In : F (Mu F) → Mu F

--------------------------------------------------------------------------------
-- Eliminators.

MAlg : ∀ {ℓ} (F : Functor ℓ) (A : Set ℓ) → Set (lsuc ℓ)
MAlg {ℓ} F A = (∀ (R : Set ℓ) → (R → A) → F R → A)

{-# TERMINATING #-}
mcata : ∀ {ℓ} {F : Functor ℓ} {A : Set ℓ} → MAlg F A → Mu F → A
mcata {ℓ} {F} φ (In x) = φ (Mu F) (mcata φ) x 
