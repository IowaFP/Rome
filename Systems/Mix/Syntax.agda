module Mix.Syntax where

open import Preludes.Data

--------------------------------------------------------------------------------
-- Kinds.
-- #############################################################################
--------------------------------------------------------------------------------

data Kind : Set where
  ★    : Kind
  _`→_ : Kind → Kind → Kind
  Ix   : ∀ {n} → Fin n → Kind

data KEnv : Set where
  ε : KEnv
  _,_ : KEnv → Kind → KEnv

--------------------------------------------------------------------------------
-- Types.
-- #############################################################################
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Var business.

data TVar : KEnv → Kind → Set where
    Z : ∀ {Δ} {κ} → TVar (Δ , κ) κ
    S : ∀ {Δ} {κ κ'} → TVar Δ κ → TVar (Δ , κ') κ

private
  variable
    κ κ₁ κ₂ : Kind
    Δ Δ₁ Δ₂ : KEnv

data Type : KEnv → Kind → Set where
-- ----------------------------------------
  ⊤     : Type Δ ★
  tvar  : TVar Δ κ → Type Δ κ
  _`→_  : Type Δ ★ → Type Δ ★ → Type Δ ★
  -- The type of dependent index functions
  `∀    : ∀ {Δ} (κ : Kind) →
          Type (Δ , κ) ★ → Type Δ ★
  `λ    : ∀ {Δ} (κ₁ : Kind) →
          Type (Δ , κ₁) κ₂ → Type Δ (κ₁ `→ κ₂)
  _·[_] : Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
          Type Δ κ₂
  -- N.b. can also restrict existential quantification to be over only indices.
  `∃    : ∀ {Δ} (κ : Kind) →
          Type (Δ , κ) ★ → Type Δ ★
  _∼_   : Type Δ ★ → Type Δ ★ → Type Δ ★
  μ     : Type Δ (★ `→ ★) → Type Δ ★
  υ     : Type Δ (★ `→ ★) → Type Δ ★
  Ix    :  ∀ {n} → Fin n → Type Δ ★
  Row   :  ∀ {n} → (Fin n → Type Δ ★) → Type Δ ★

data Env (Δ : KEnv) : Set where
  ε : Env Δ
  _,_ : ∀ {κ} → Env Δ → Type Δ κ → Env Δ


data Var : ∀ {Δ} {κ} → Env Δ → Type Δ κ → Set where
    Z    : ∀ {Δ} {Γ : Env Δ} {τ : Type Δ ★} → Var (Γ , τ) τ
    S    : ∀ {Δ} {Γ : Env Δ} {τ υ : Type Δ ★} → 
             Var Γ τ  → Var Γ τ → Var (Γ , υ) τ


--------------------------------------------------------------------------------
-- Terms.
-- #############################################################################
--------------------------------------------------------------------------------

private
  variable
    Γ : Env Δ
    τ : Type Δ ★

postulate
  weakΓ : Env Δ → Env (Δ , κ)

data Term : ∀ (Δ : KEnv) → (Γ : Env Δ) → Type Δ ★ → Set where
  var : Var Γ τ →
        ----------
        Term Δ Γ τ

  `λ : (τ υ : Type Δ ★) → Term Δ (Γ , τ) υ →
       -------------------------------------
       Term Δ Γ (τ `→ υ)

  -- dependent index introduction.
  `Λ : ∀ {Δ : KEnv} {Γ : Env Δ}
         (κ : Kind) {τ : Type (Δ , κ) ★} →
  
         Term (Δ , κ) (weakΓ Γ) τ →
         ----------------------------------------------------
         Term Δ Γ (`∀ κ τ)
  

  




