module Operational.Rome.Kinds.Syntax where


--------------------------------------------------------------------------------
-- 2.1 Kinds

data Kind : Set where
  ★     : Kind
  L     : Kind
  _`→_ : Kind → Kind → Kind
  R[_]  : Kind → Kind

infixr 5 _`→_

--------------------------------------------------------------------------------
-- 2.2 contexts

data KEnv : Set where
  ε : KEnv
  _,,_ : KEnv → Kind → KEnv


--------------------------------------------------------------------------------
-- 2.3 Type variables

private
  variable
    Δ Δ₁ Δ₂ Δ₃ : KEnv
    κ κ₁ κ₂ : Kind

data KVar : KEnv → Kind → Set where
  Z : KVar (Δ ,, κ) κ
  S : KVar Δ κ₁ → KVar (Δ ,, κ₂) κ₁
