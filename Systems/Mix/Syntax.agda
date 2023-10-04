module Mix.Syntax where

open import Data.Nat

--------------------------------------------------------------------------------
-- Type syntax of Mix without kind-type stratification.

data TEnv : Set

data Type : Set
data TVar : (Δ : TEnv) → (Type Δ) → Set

data TEnv where
  ε : TEnv
  _,_ : (Δ : TEnv) → Type → TEnv


data TVar where
    Z : ∀ {Δ} {τ} → TVar (Δ , τ) τ
    S : ∀ {Δ} {τ τ'} → TVar (Δ , τ') τ

data Type where
  ★ : Type
  _`→_ : Type → Type → Type
  Fin : Type → Type
  Nat : Type
  `∀ : Type → Type → Type
  `∃ : Type → Type → Type
  ⊤ : Type
  
  
  
-- ----------------------------------------
  -- ⊤     : Type Δ ★
  -- tvar  : TVar Δ κ → Type Δ κ
  -- _`→_  : Type Δ ★ → Type Δ ★ → Type Δ ★
  -- `∀    : ∀ {Δ} (κ : Kind) →
  --         Type (Δ , κ) ★ → Type Δ ★
  -- `λ    : ∀ {Δ} (κ₁ : Kind) →
  --         Type (Δ , κ₁) κ₂ → Type Δ (κ₁ `→ κ₂)
  -- _·[_] : Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
  --         Type Δ κ₂
  -- -- N.b. can also restrict existential quantification be over only indices.
  -- `∃    : ∀ {Δ} (κ : Kind) →
  --         Type (Δ , κ) ★ → Type Δ ★
  -- _∼_   : Type Δ ★ → Type Δ ★ → Type Δ ★
  -- μ     : Type Δ (★ `→ ★) → Type Δ ★
  -- υ     : Type Δ (★ `→ ★) → Type Δ ★
