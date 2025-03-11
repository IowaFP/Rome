module Rome.Operational.Terms.Semantics.Reduction where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax

import Rome.Operational.Types as Types
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.Substitution

open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Terms.GVars


--------------------------------------------------------------------------------
-- Values

data Value {Δ} {Γ : Context Δ} : ∀ {τ : NormalType Δ ★} → Term Γ τ → Set where
  V-λ : ∀ {τ₁ τ₂} 
          (M : Term (Γ , τ₂) τ₁) → 
          Value (`λ M)

  V-Λ : ∀ {τ} 
          (M : Term (Γ ,, κ) τ) → 
          Value (Λ M)

  V-roll : ∀ (F : NormalType Δ (★ `→ ★)) 
             {M : Term Γ (F ·' (μ F))} → 
             Value M → 
             Value (roll F M)

  V-# : ∀ {l : Label} →  
          Value (# l)

  V-Π   : ∀ {l : NormalType Δ L} {υ : NormalType Δ ★} → 
            (ℓ : Term Γ ⌊ l ⌋) → (M : Term Γ υ) → 

            Value M → 
            ---------------------
            Value (ℓ Π▹ M)

  V-Σ   : ∀ {l : NormalType Δ L} {τ : NormalType Δ ★} → 
            (ℓ : Term Γ ⌊ l ⌋) → (M : Term Γ τ) → 

            Value M → 
            ---------------------
            Value (ℓ Σ▹ M)

--------------------------------------------------------------------------------
-- Small step semantics.

infixr 0 _—→_
data _—→_ : ∀ {τ} → Term Γ τ → Term Γ τ → Set where
  -- congruence rules
  ξ-·1 : ∀ {τ₁ τ₂} {M₁ M₂ : Term Γ (τ₁ `→ τ₂)} {N : Term Γ τ₁} →
           M₁ —→ M₂ →
           -----------------
           M₁ · N —→ M₂ · N

  ξ-Λ : ∀ {τ} {M₁ M₂ : Term (Γ ,, κ) τ} →
         M₁ —→ M₂ →
         -----------------------
         (Λ M₁) —→ (Λ M₂)

  ξ-·[] : ∀ {τ} {τ'} {M₁ M₂ : Term Γ (`∀ κ τ)} →
            M₁ —→ M₂ →
            ------------------------
            M₁ ·[ τ' ] —→ M₂ ·[ τ' ]

  ξ-unroll : ∀ {F} {M₁ M₂ : Term Γ (μ F)} →
               M₁ —→ M₂ →
               -----------------------
               unroll F M₁ —→ unroll F M₂

  ξ-roll : ∀ {F} {M₁ M₂ : Term Γ (F ·' (μ F))} →
             M₁ —→ M₂ →
             -----------------------
             roll F M₁ —→ roll F M₂

  ξ-Π▹ : ∀ {l : NormalType Δ L} {τ : NormalType Δ ★} → 
            (M₁ M₂ : Term Γ τ) (ℓ : Term Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (ℓ Π▹ M₁) —→ (ℓ Π▹ M₂)

  ξ-Π/₁ : ∀ {l : NormalType Δ L} {τ : NormalType Δ ★} → 
            (M₁ M₂ : Term Γ (Π (l ▹ τ))) (ℓ : Term Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Π/ ℓ) —→ (M₂ Π/ ℓ)        

  ξ-Σ▹ : ∀ {l : NormalType Δ L} {τ : NormalType Δ ★} → 
            (M₁ M₂ : Term Γ τ) (ℓ : Term Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (ℓ Σ▹ M₁) —→ (ℓ Σ▹ M₂)

  ξ-Σ/₁ : ∀ {l : NormalType Δ L} {τ : NormalType Δ ★} → 
            (M₁ M₂ : Term Γ (Σ (l ▹ τ))) (ℓ : Term Γ ⌊ l ⌋)  → 

             M₁ —→ M₂ → 
             -----------------------
             (M₁ Σ/ ℓ) —→ (M₂ Σ/ ℓ)    

  -- computational rules
  β-λ : ∀ {τ₁ τ₂} {M : Term (Γ , τ₁) τ₂} {N : Term Γ τ₁} →
          
          -----------------------
          (`λ M) · N —→ M β[ N ]

  β-Λ : ∀ {τ₁ : NormalType Δ κ} {τ₂} {M : Term (Γ ,, κ) τ₂}  →

          --------------------------
          Λ M ·[ τ₁ ] —→ M β·[ τ₁ ]

  β-roll : ∀ {F} {M : Term Γ (F ·' μ F)} →

             -------------------------
             unroll F (roll F M) —→ M

  β-Π/ :  ∀ {l : NormalType Δ L} {τ : NormalType Δ ★} → 
            (M : Term Γ τ) (ℓ₁ ℓ₂ : Term Γ ⌊ l ⌋) → 

             Value M →
             -----------------------
             ((ℓ₁ Π▹ M) Π/ ℓ₂) —→ M

  β-Σ/ :  ∀ {l : NormalType Δ L} {τ : NormalType Δ ★} → 
            (M : Term Γ τ) (ℓ₁ ℓ₂ : Term Γ ⌊ l ⌋) → 

             Value M →
             -----------------------
             ((ℓ₁ Σ▹ M) Σ/ ℓ₂) —→ M

