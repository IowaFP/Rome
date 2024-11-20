module SFFP.Types.Properties where

open import SFFP.Prelude
open import SFFP.Kinds.Syntax
open import SFFP.Kinds.GVars
open import SFFP.Types.Syntax
open import SFFP.Types.Renaming
open import SFFP.Types.Substitution



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
ren-cong eq (μ τ) rewrite ren-cong (↑-cong eq) τ = refl 

ren-id : ∀ (τ : Type Δ κ) → ren id τ ≡ τ
ren-id (` x) = refl
ren-id (`λ τ) rewrite ren-cong ↑-id τ | ren-id τ = refl 
ren-id (τ₁ · τ₂) rewrite ren-id τ₁ | ren-id τ₂ = refl
ren-id (τ₁ `→ τ₂) rewrite ren-id τ₁ | ren-id τ₂ = refl
ren-id (`∀ κ τ) rewrite ren-cong ↑-id τ | ren-id τ = refl
ren-id (μ τ) rewrite ren-cong ↑-id τ | ren-id τ = refl

ren-comp : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
           ∀ (τ : Type Δ₁ κ) → ren (ρ₂ ∘ ρ₁) τ ≡ ren ρ₂ (ren ρ₁ τ)
ren-comp ρ₁ ρ₂ (` x) = refl
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
ren-comp ρ₁ ρ₂ (μ τ) rewrite
  (trans (ren-cong (↑-comp ρ₁ ρ₂) τ) (ren-comp (↑ ρ₁) (↑ ρ₂) τ)) = refl
