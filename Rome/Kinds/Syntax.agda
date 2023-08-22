{-# OPTIONS --safe #-}
module Rome.Kinds.Syntax where

--------------------------------------------------------------------------------
-- Kinds.

data Kind : Set where
  ★ : Kind
  L : Kind
  R[_] : Kind → Kind
  _`→_ : Kind → Kind → Kind

--------------------------------------------------------------------------------
-- Kinding environments.

data KEnv : Set where
  ε    : KEnv
  _,_  : KEnv → Kind → KEnv
