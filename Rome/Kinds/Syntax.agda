module Rome.Kinds.Syntax where

open import Preludes.Level
open import Rome.GVars.Levels

--------------------------------------------------------------------------------
-- Kinds.

data Kind : Level → Set where
  ★ : (ℓ : Level) → Kind ℓ
  _`→_ : Kind ℓ₁ → Kind ℓ₂ → Kind (ℓ₁ ⊔ ℓ₂)
  L : (ℓ : Level) → Kind ℓ
  R[_] : Kind ℓ → Kind ℓ

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
  _،_  : KEnv ℓ₁ → Kind ℓ₂ → KEnv (ℓ₁ ⊔ ℓ₂)

infixl 5 _،_
