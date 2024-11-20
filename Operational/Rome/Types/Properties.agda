module Operational.Rome.Types.Properties where

open import Operational.Rome.Prelude
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars
open import Operational.Rome.Types.Syntax
open import Operational.Rome.Types.Renaming
open import Operational.Rome.Types.Substitution

--------------------------------------------------------------------------------
-- ↑ing respects congruence, identities, and composition.
--

↑-id : ∀ (x : KVar (Δ ,, κ₂) κ₁) → ↑ id x ≡ x
↑-id Z = refl
↑-id (S x) = refl

↑-comp : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
            ∀ (x : KVar (Δ₁ ,, κ₂) κ₁) → ↑ (ρ₂ ∘ ρ₁) x ≡ ↑ ρ₂ (↑ ρ₁ x)
↑-comp ρ₁ ρ₂ Z = refl
↑-comp ρ₁ ρ₂ (S x) = refl

↑-cong : ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} → (ρ₁ ≈ ρ₂) → 
              (x : KVar (Δ₁ ,, κ₂) κ) → ↑ ρ₁ x ≡ ↑ ρ₂ x
↑-cong eq Z = refl
↑-cong eq (S x) = cong S (eq x)


--------------------------------------------------------------------------------
-- Renaming respects congruence, identities, and composition.

ren-cong :  ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
              (τ : Type Δ₁ κ) → ren ρ₁ τ ≡ ren ρ₂ τ
ren-cong eq (` x) rewrite eq x = refl
ren-cong eq (`λ τ) rewrite ren-cong (↑-cong eq) τ = refl 
ren-cong eq (τ₁ · τ₂) rewrite ren-cong eq τ₁ | ren-cong eq τ₂ = refl
ren-cong eq (τ₁ `→ τ₂) rewrite ren-cong eq τ₁ | ren-cong eq τ₂ = refl
ren-cong eq (`∀ κ τ) rewrite ren-cong (↑-cong eq) τ = refl 
ren-cong eq (μ F) rewrite ren-cong eq F = refl 
ren-cong eq (Π τ) rewrite ren-cong eq τ = refl 
ren-cong eq (Σ τ) rewrite ren-cong eq τ = refl 
ren-cong eq (lab _) = refl
ren-cong eq (τ₁ ▹ τ₂) rewrite 
    ren-cong eq τ₁
  | ren-cong eq τ₂ = refl
ren-cong eq (τ₁ R▹ τ₂) rewrite
    ren-cong eq τ₁
  | ren-cong eq τ₂ = refl
ren-cong eq ⌊ τ ⌋ rewrite ren-cong eq τ = refl

ren-id : ∀ (τ : Type Δ κ) → ren id τ ≡ τ
ren-id (` x) = refl
ren-id (`λ τ) rewrite ren-cong ↑-id τ | ren-id τ = refl 
ren-id (τ₁ · τ₂) rewrite ren-id τ₁ | ren-id τ₂ = refl
ren-id (τ₁ `→ τ₂) rewrite ren-id τ₁ | ren-id τ₂ = refl
ren-id (`∀ κ τ) rewrite ren-cong ↑-id τ | ren-id τ = refl
ren-id (μ F) rewrite ren-id F = refl
ren-id (Π τ) rewrite ren-id τ = refl
ren-id (Σ τ) rewrite ren-id τ = refl
ren-id (lab _) = refl
ren-id (τ₁ ▹ τ₂) rewrite 
    ren-id τ₁
  | ren-id τ₂ = refl
ren-id (τ₁ R▹ τ₂) rewrite
    ren-id τ₁
  | ren-id τ₂ = refl
ren-id ⌊ τ ⌋ rewrite ren-id τ = refl


ren-comp : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
           ∀ (τ : Type Δ₁ κ) → ren (ρ₂ ∘ ρ₁) τ ≡ ren ρ₂ (ren ρ₁ τ)
ren-comp ρ₁ ρ₂ (` x) = refl
ren-comp ρ₁ ρ₂ (Π ρ) rewrite ren-comp ρ₁ ρ₂ ρ = refl
ren-comp ρ₁ ρ₂ (Σ ρ) rewrite ren-comp ρ₁ ρ₂ ρ = refl
ren-comp ρ₁ ρ₂ (`λ τ)  rewrite
  trans (ren-cong (↑-comp ρ₁ ρ₂) τ) (ren-comp (↑ ρ₁) (↑ ρ₂) τ) = refl
ren-comp ρ₁ ρ₂ (τ₁ · τ₂) rewrite
    ren-comp ρ₁ ρ₂ τ₁ 
  | ren-comp ρ₁ ρ₂ τ₂ = refl
ren-comp ρ₁ ρ₂ (τ₁ `→ τ₂) rewrite
    ren-comp ρ₁ ρ₂ τ₁ 
  | ren-comp ρ₁ ρ₂ τ₂ = refl
ren-comp ρ₁ ρ₂ (`∀ κ τ) rewrite
  (trans (ren-cong (↑-comp ρ₁ ρ₂) τ) (ren-comp (↑ ρ₁) (↑ ρ₂) τ)) = refl
ren-comp ρ₁ ρ₂ (μ F) rewrite
  ren-comp ρ₁ ρ₂ F = refl
ren-comp ρ₁ ρ₂ (lab _) = refl
ren-comp ρ₁ ρ₂ (τ₁ ▹ τ₂) rewrite
    ren-comp ρ₁ ρ₂ τ₁ 
  | ren-comp ρ₁ ρ₂ τ₂ = refl
ren-comp ρ₁ ρ₂ (τ₁ R▹ τ₂) rewrite
    ren-comp ρ₁ ρ₂ τ₁ 
  | ren-comp ρ₁ ρ₂ τ₂ = refl
ren-comp ρ₁ ρ₂ ⌊ τ ⌋ rewrite
    ren-comp ρ₁ ρ₂ τ = refl
