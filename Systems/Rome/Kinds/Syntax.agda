{-# OPTIONS --safe #-}
module Rome.Kinds.Syntax where

--------------------------------------------------------------------------------
-- Kinds.

data Kind : Set where
  ★ : Kind
  L : Kind
  R[_] : Kind → Kind
  _`→_ : Kind → Kind → Kind

data Star : Kind → Set where
  ★ : Star ★
  _`→_ : ∀ {κ₁ κ₂} → Star κ₁ → Star κ₂ → Star (κ₁ `→ κ₂)

--------------------------------------------------------------------------------
-- Kinding environments.

data KEnv : Set where
  ε    : KEnv
  _,_  : KEnv → Kind → KEnv
