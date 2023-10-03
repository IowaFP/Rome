module Mix.Kinds.Syntax where

open import Data.Nat

--------------------------------------------------------------------------------
-- Kinds.

data Kind : Set where
  ★ : Kind
  _`→_ : Kind → Kind → Kind
  Fin : ℕ → Kind

--------------------------------------------------------------------------------
-- Environments.

data KEnv : Set where
  ε : KEnv
  _,_ : KEnv → Kind → KEnv
