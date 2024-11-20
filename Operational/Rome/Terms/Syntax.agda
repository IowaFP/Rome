module Operational.Rome.Terms.Syntax where

open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

open import Operational.Rome.Types.Syntax
open import Operational.Rome.Types.Renaming
open import Operational.Rome.Types.Substitution

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

data Term {Δ} Γ : Type Δ ★ → Set where
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

  Λ : ∀ {τ} →

      Term (Γ ,, κ) τ →
      -----------
      Term Γ (`∀ κ τ)

  _·[_] : ∀ {τ₂} → 
  
          Term Γ (`∀ κ τ₂) →
          (τ₁ : Type Δ κ) → 
          ----------------
          Term Γ (τ₂ β[ τ₁ ])

  roll : 
         ∀ τ → 
         Term Γ (τ β[ μ τ ]) → 
         -----------------
         Term Γ (μ τ)

  unroll : 
         ∀ τ → 
         Term Γ (μ τ) → 
         --------------
         Term Γ (τ β[ μ τ ])
