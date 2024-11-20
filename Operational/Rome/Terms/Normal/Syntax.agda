module Operational.Rome.Terms.Normal.Syntax where

open import Operational.Rome.Prelude
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

open import Operational.Rome.Types.Normal.Syntax
open import Operational.Rome.Types.Normal.Renaming
open import Operational.Rome.Types.Normal.Substitution

--------------------------------------------------------------------------------
-- 3.7 Terms with normal types

data Context : KEnv → Set where
  ε : Context ε
  _,,_ : Context Δ → (κ : Kind) → Context (Δ ,, κ)
  _,_  : Context Δ → NormalType Δ ★ → Context Δ


data Var : Context Δ → NormalType Δ ★ → Set where
  Z : ∀ {Γ} {τ : NormalType Δ ★} → Var (Γ , τ) τ
  S : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → Var Γ τ₁  → Var (Γ , τ₂) τ₁
  T : ∀ {Γ} {τ : NormalType Δ ★} → Var Γ τ → Var (Γ ,, κ) (weaken τ)

data NormalTerm {Δ} Γ : NormalType Δ ★ → Set where
  ` : ∀ {τ} →
 
      Var Γ τ → 
      --------
      NormalTerm Γ τ

  `λ : ∀ {τ₁ τ₂} → 

       NormalTerm (Γ , τ₁) τ₂ → 
       --------------
       NormalTerm Γ (τ₁ `→ τ₂)

  _·_ : ∀ {τ₁ τ₂} → 

       NormalTerm Γ (τ₁ `→ τ₂) → 
       NormalTerm Γ τ₁ → 
       ---------
       NormalTerm Γ τ₂

  Λ : ∀ {τ} →

      NormalTerm (Γ ,, κ) τ →
      -----------
      NormalTerm Γ (`∀ κ τ)

  _·[_] : ∀ {τ₂} → 
  
          NormalTerm Γ (`∀ κ τ₂) →
          (τ₁ : NormalType Δ κ) → 
          ----------------
          NormalTerm Γ (τ₂ β[ τ₁ ])

  roll : 
         ∀ τ → 
         NormalTerm Γ (τ β[ μ τ ]) → 
         -----------------
         NormalTerm Γ (μ τ)

  unroll : 
         ∀ τ → 
         NormalTerm Γ (μ τ) → 
         --------------
         NormalTerm Γ (τ β[ μ τ ])

--------------------------------------------------------------------------------
-- helpers.

convVar : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → Var Γ τ₁ → Var Γ τ₂
convVar refl v = v

conv : ∀ {Γ} {τ₁ τ₂ : NormalType Δ ★} → τ₁ ≡ τ₂ → NormalTerm Γ τ₁ → NormalTerm Γ τ₂
conv refl M = M
