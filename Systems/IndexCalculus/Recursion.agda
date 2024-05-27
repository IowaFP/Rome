{-# OPTIONS --safe #-}
module IndexCalculus.Recursion where

open import Preludes.Level
open import Preludes.Data
open import IndexCalculus.Rows
open import IndexCalculus.Variants


data Mu {ℓ} : (Set ℓ → Set ℓ) → Set ℓ where
  In : (F : (Set ℓ → Set ℓ))  → Mu F

-- data Mu {ℓ} (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
--   In : ∀ (R : Set ℓ) → (R → Mu F) → F R → Mu F

-- initAlg : ∀ {ℓ} → (F : ∀ {ℓ} → Set ℓ → Set ℓ) → F {lsuc ℓ} (Mu F) → Mu {ℓ} F
-- initAlg {ℓ} F d = In {!!} {!λ x → x!} {!!}
