module Rome.Operational.Types.Properties.Substitution where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution

postulate
  ↻-sub-ren : ∀ {ρ : Renaming Δ₁ Δ₂}{σ : Substitution Δ₂ Δ₃}
                (τ : Type Δ₁ κ) → sub (σ ∘ ρ) τ ≡ sub σ (ren ρ τ)
  
  sub-id : ∀ (τ : Type Δ κ) → sub ` τ ≡ τ 
  sub-comp : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₂ Δ₃}
                (τ : Type Δ₁ κ) → sub (sub σ₂ ∘ σ₁) τ ≡ sub σ₂ (sub σ₁ τ)
  sub-cong : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₁ Δ₂} →
                (∀ (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
                (τ : Type Δ₁ κ) → sub σ₁ τ ≡ sub σ₂ τ

  -- ren⋆-sub⋆         : ∀{ϕ ψ Θ}{σ : Sub⋆ ϕ ψ}{ρ : Ren⋆ ψ Θ}{J}(A : ϕ ⊢⋆ J)
  --                      → sub (ren ρ ∘ σ) A ≡ ren⋆ ρ (sub⋆ σ A)