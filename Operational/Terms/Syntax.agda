module Rome.Operational.Terms.Syntax where

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution

--------------------------------------------------------------------------------
-- 2.8 Term contexts.

data Context : KEnv → Set where
  ε : Context ε
  _,,_ : Context Δ → (κ : Kind) → Context (Δ ,, κ)
  _,_  : Context Δ → Type Δ ★ → Context Δ

private
  variable
    Γ : Context Δ

--------------------------------------------------------------------------------
-- 2.9 Term vars

data Var : Context Δ → Type Δ ★ → Set where
  Z : {τ : Type Δ ★} → Var (Γ , τ) τ
  S : {τ₁ τ₂ : Type Δ ★} → Var Γ τ₁ → Var (Γ , τ₂) τ₁
  T : {τ : Type Δ ★} → Var Γ τ → Var (Γ ,, κ) (weaken τ)

--------------------------------------------------------------------------------
-- 2.10 Terms

private
  variable
    τ υ τ₁ τ₂ : Type Δ ★
    ℓ ℓ₁ ℓ₂   : Type Δ L
    

data Term {Δ} Γ : Type Δ ★ → Set where
  ------------------------------------------------------------
  -- Lambda calculus.
  ` : ∀ {τ} →
 
      Var Γ τ → 
      --------
      Term Γ τ

  `λ : ∀ {τ₁ τ₂} → 

       Term (Γ , τ₁) τ₂ → 
       --------------
       Term Γ (τ₁ `→ τ₂)

  _·_ : ∀ {τ₁ τ₂} → 

       Term Γ (τ₁ `→ τ₂) → 
       Term Γ τ₁ → 
       ---------
       Term Γ τ₂
  
  ------------------------------------------------------------
  -- System Fω

  Λ : ∀ {τ} →

      Term (Γ ,, κ) τ →
      -----------
      Term Γ (`∀ κ τ)

  _·[_] : ∀ {τ₂} → 
  
          Term Γ (`∀ κ τ₂) →
          (τ₁ : Type Δ κ) → 
          ----------------
          Term Γ (τ₂ β[ τ₁ ])

  ------------------------------------------------------------
  -- Recursive types

  roll : 
         ∀ F → 
         Term Γ (F · μ F) → 
         -----------------
         Term Γ (μ F)

  unroll : 
           ∀ F → 
           Term Γ (μ F) → 
           --------------
           Term Γ (F ·  μ F)

  ------------------------------------------------------------
  -- Qualified types
  
  -- ...

  ------------------------------------------------------------
  -- Rω labels

  -- labels
  lab : 

        ∀ (l : Type Δ L) →
        -------------------
        Term Γ ⌊ l ⌋

  ------------------------------------------------------------
  -- Rω records

  -- Record singleton formation
  _Π▹_ : 
          (M₁ : Term Γ ⌊ ℓ ⌋) (M₂ : Term Γ υ) →
          ----------------------------------------
          Term Γ (Π (ℓ ▹ υ))

  -- Record singleton elimination
  _Π/_ :
          (M₁ : Term Γ (Π (ℓ ▹ υ))) (M₂ : Term Γ ⌊ ℓ ⌋) →
          ----------------------------------------
          Term Γ υ

  ------------------------------------------------------------
  -- Rω variants

  -- Record singleton formation
  _Σ▹_ : 
          (M₁ : Term Γ ⌊ ℓ ⌋) (M₂ : Term Γ υ) →
          ----------------------------------------
          Term Γ (Σ (ℓ ▹ υ))

  -- Record singleton elimination
  _Σ/_ :
          (M₁ : Term Γ (Σ (ℓ ▹ υ))) (M₂ : Term Γ ⌊ ℓ ⌋) →
          ----------------------------------------
          Term Γ υ

  

