{-# OPTIONS --safe #-}
module Rome.Operational.Types.Pre.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars


data Pred (Δ : KEnv) : Set 
data Type (Δ : KEnv) : Set 
data Pred Δ where
    _·_~_ : (ρ₁ ρ₂ ρ₃ : Type Δ) → Pred Δ 
    _≲_ : (ρ₁ ρ₂ : Type Δ) → Pred Δ

data Type Δ where
    ` :  KVar Δ κ  → Type Δ 
    `λ : ∀ (τ : Type (Δ ,, κ₁)) → Type Δ
    _·_ : (τ₁ : Type Δ) → (τ₂ : Type Δ) → Type Δ
    _`→_ : (τ₁ : Type Δ) →(τ₂ : Type Δ) → Type Δ
    `∀    : {κ : Kind} → (τ : Type (Δ ,, κ)) → Type Δ
    μ     : (φ : Type Δ) → Type Δ
    _⇒_ : (π : Pred Δ) → (τ : Type Δ) → Type Δ       
    lab : (l : Label) → Type Δ
    ⌊_⌋ : (τ : Type Δ) → Type Δ
    _▹_ : (l : Type Δ) → (τ : Type Δ) → Type Δ
    _<$>_ : (φ : Type Δ) → (τ : Type Δ) → Type Δ
    Π     : Type Δ
    Σ     : Type Δ
    _─_ : Type Δ → Type Δ → Type Δ 