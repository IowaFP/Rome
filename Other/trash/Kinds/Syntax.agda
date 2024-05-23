module Mix.Kinds.Syntax where

open import Preludes.Data

--------------------------------------------------------------------------------
-- Kinds.

data Kind : Set where
  ★     : Kind
  _`→_ : Kind → Kind → Kind
  Nat   : Kind

-- --------------------------------------------------------------------------------
-- -- Environments.

data KEnv : Set where
  ε : KEnv
  _,_ : KEnv → Kind → KEnv

