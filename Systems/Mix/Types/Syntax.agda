module Mix.Types.Syntax where

open import Data.Nat

open import Mix.Kinds.Syntax
  


--------------------------------------------------------------------------------
-- Var business.

data TVar : KEnv → Kind → Set where
    Z : ∀ {Δ} {κ} → TVar (Δ , κ) κ
    S : ∀ {Δ} {κ κ'} → TVar Δ κ → TVar (Δ , κ') κ

--------------------------------------------------------------------------------

private
  variable
    κ κ' κ₁ κ₂ : Kind
    Δ Δ₁ Δ₂ : KEnv

data Type : KEnv → Kind → Set where
-- ----------------------------------------
  ⊤     : Type Δ ★
  tvar  : TVar Δ κ → Type Δ κ
  _`→_  : Type Δ ★ → Type Δ ★ → Type Δ ★
  `∀    : ∀ {Δ} (κ : Kind) →
          Type (Δ , κ) ★ → Type Δ ★
  `λ    : ∀ {Δ} (κ₁ : Kind) →
          Type (Δ , κ₁) κ₂ → Type Δ (κ₁ `→ κ₂)
  _·[_] : Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
          Type Δ κ₂
  -- N.b. can also restrict existential quantification be over only indices.
  `∃    : ∀ {Δ} (κ : Kind) →
          Type (Δ , κ) ★ → Type Δ ★
  _∼_   : Type Δ ★ → Type Δ ★ → Type Δ ★
  μ     : Type Δ (★ `→ ★) → Type Δ ★
  υ     : Type Δ (★ `→ ★) → Type Δ ★
-- ----------------------------------------
  Ix    :  (n : Type Δ Nat) → Type Δ ★
  Zero  : Type Δ Nat
  Suc  : Type Δ Nat

postulate
  weaken : Type Δ κ → Type (Δ , κ') κ



-- len : Type Δ → ℕ
