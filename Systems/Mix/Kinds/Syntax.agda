module Mix.Kinds.Syntax where

open import Data.Nat

data Fin : ℕ → Set where
  fzero : Fin 1
  fsucc : ∀ {n} → Fin n → Fin (suc n)


--------------------------------------------------------------------------------
-- Kinds.

data Kind : Set where
  ★    : Kind
  _`→_ : Kind → Kind → Kind
  Ix   : ℕ    → Kind
  ∃i   : Kind → Kind

-- --------------------------------------------------------------------------------
-- -- Environments.

data KEnv : Set where
  ε : KEnv
  _,_ : KEnv → Kind → KEnv
