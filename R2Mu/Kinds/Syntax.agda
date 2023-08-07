{-# OPTIONS --safe #-}
module R2Mu.Kinds.Syntax where

--------------------------------------------------------------------------------
-- Kinds.

data Kind₁ : Set where
  ★ : Kind₁
  L : Kind₁

data Kind₂ : Set where
  `_ : Kind₁ → Kind₂
  _`→_ : Kind₁ → Kind₂ → Kind₂
  R[_] : Kind₂ → Kind₂

Kind = Kind₂


--------------------------------------------------------------------------------
-- Kinding environments.

data KEnv : Set where
  ε    : KEnv
  _,_  : KEnv → Kind₂ → KEnv
