module Mix.Spec where

open import Data.Nat
open import Data.Product using (_×_ ; _,_)

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

data TVar : KEnv → Kind → Set where
    Z : ∀ {Δ} {κ} → TVar (Δ , κ) κ
    S : ∀ {Δ} {κ κ'} → TVar (Δ , κ') κ

--------------------------------------------------------------------------------
-- Types.

private
  variable
    κ κ₁ κ₂ : Kind
    Δ Δ₁ Δ₂ : KEnv

data Type : KEnv → Kind → Set where
-- ----------------------------------------
  ⊤ : Type Δ ★
  tvar : TVar Δ κ → Type Δ κ
  _`→_ : Type Δ ★ → Type Δ ★ → Type Δ ★
  `∀ : Type (Δ , κ) ★ → Type Δ ★
  `λ : Type (Δ , κ₁) κ₂ → Type Δ (κ₁ `→ κ₂)
  _·[_] : Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
          Type Δ κ₂
  `∃i : (n : ℕ) → Type (Δ , Fin n) ★ → Type Δ ★

--------------------------------------------------------------------------------
-- Type reduction.

-- data _—→_ : Type Δ₁ κ₁ → Type Δ₂ κ₂ : Set where
--   β : ∀ ? → ((`λ τ) ·[ υ ] —→ (substitution here))



  

     


  
