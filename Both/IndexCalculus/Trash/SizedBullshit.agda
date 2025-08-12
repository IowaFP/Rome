{-# OPTIONS --allow-unsolved-metas  --sized-types #-}
module Rome.Both.IndexCalculus.SizedBullshit where

open import Agda.Builtin.Size
open import Rome.Preludes.Level
open import Rome.Preludes.Data
open import Rome.Both.IndexCalculus.Rows
open import Rome.Both.IndexCalculus.Variants
-- open import Rome.Preludes.Partiality

--------------------------------------------------------------------------------
-- Denoting recursive types.

-- mu : ∀ {ℓ} (F : Set ℓ → Set ℓ) → ℕ → Set ℓ
-- mu F ℕ.zero = ⊤
-- mu F (ℕ.suc n) = F (mu F n)


-- data Mu {ℓ} (i : Size) (F : Set ℓ → Set ℓ)    : Set ℓ
record ∞Mu {ℓ} (i : Size) (F : Set ℓ → Set ℓ) : Set ℓ

-- data Mu {ℓ} i F where
--   In : F (∞Mu i F) → Mu i F

record ∞Mu {ℓ} i F where
  coinductive
  field
    force : {j : Size< i} → F (∞Mu j F)

