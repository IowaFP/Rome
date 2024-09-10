module Rωμ.Kinds.Syntax where

--------------------------------------------------------------------------------
-- Kinds.

data Kind : Set where
  ★ : Kind
  _`→_ : Kind → Kind → Kind
  L : Kind
  R[_] : Kind → Kind

--------------------------------------------------------------------------------
-- Kinding environments.

data KEnv : Set where
  ε    : KEnv
  _،_  : KEnv → Kind → KEnv

infixl 5 _،_
