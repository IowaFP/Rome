module Mix.Terms.Syntax where

open import Data.Nat

data Type : Set where

data TEnv : Set where

data Env : TEnv → Set where

private 
  variable
    Δ : TEnv
    Γ : Env Δ

data Var : Env → Type → Set where
  Z : ∀ {Δ} {τ} → Var ε
data Term : Env → Type → Set where
  var : ℕ → Term Δ Γ
  
