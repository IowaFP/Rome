{-# OPTIONS --safe #-}
module F.Kinds.Syntax where

open import Agda.Primitive
open import Level

--------------------------------------------------------------------------------
-- Kinds.

data Kind : Level → Set where
  ★ : (ℓ : Level) → Kind ℓ

-- type synonyms
lone ltwo lthree : Level
lone   = lsuc lzero
ltwo   = lsuc lone
lthree = lsuc ltwo

★₀ = ★ lzero
★₁ = ★ lone
★₂ = ★ ltwo

--------------------------------------------------------------------------------
-- Kinding environments.

data KEnv : Level → Set where
  ε    : KEnv lzero
  _,_  : ∀ {ℓ ι} → KEnv ℓ → Kind ι → KEnv (ℓ ⊔ ι)
