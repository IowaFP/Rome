module Rome.Operational.Types.Properties.Substitution where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution

--------------------------------------------------------------------------------
-- ↑ing respects congruence, identities, and composition.
--

lift-id : ∀ (x : KVar (Δ ,, κ₂) κ₁) → lift id x ≡ x
lift-id Z = refl
lift-id (S x) = refl

lift-comp : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
            ∀ (x : KVar (Δ₁ ,, κ₂) κ₁) → lift (ρ₂ ∘ ρ₁) x ≡ lift ρ₂ (lift ρ₁ x)
lift-comp ρ₁ ρ₂ Z = refl
lift-comp ρ₁ ρ₂ (S x) = refl

lift-cong : ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} → (ρ₁ ≈ ρ₂) → 
              (x : KVar (Δ₁ ,, κ₂) κ) → lift ρ₁ x ≡ lift ρ₂ x
lift-cong eq Z = refl
lift-cong eq (S x) = cong S (eq x)


--------------------------------------------------------------------------------
-- Renaming respects congruence, identities, and composition.

ren-cong :  ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
              (τ : Type Δ₁ κ) → ren ρ₁ τ ≡ ren ρ₂ τ
ren-cong eq Unit = refl
ren-cong eq (` x) rewrite eq x = refl
ren-cong eq (`λ τ) rewrite ren-cong (lift-cong eq) τ = refl 
ren-cong eq (τ₁ · τ₂) rewrite ren-cong eq τ₁ | ren-cong eq τ₂ = refl
ren-cong eq (τ₁ `→ τ₂) rewrite ren-cong eq τ₁ | ren-cong eq τ₂ = refl
ren-cong eq (`∀ κ τ) rewrite ren-cong (lift-cong eq) τ = refl 
ren-cong eq (μ F) rewrite ren-cong eq F = refl 
ren-cong eq Π = refl 
ren-cong eq Σ = refl 
ren-cong eq (lab _) = refl
ren-cong eq `▹` = refl
ren-cong eq ⌊ τ ⌋ rewrite ren-cong eq τ = refl
ren-cong eq (f <$> a) rewrite ren-cong eq f | ren-cong eq a = refl
-- ren-cong eq (τ ↑) rewrite ren-cong eq τ = refl

ren-id : ∀ (τ : Type Δ κ) → ren id τ ≡ τ
ren-id Unit = refl
ren-id (` x) = refl
ren-id (`λ τ) rewrite ren-cong lift-id τ | ren-id τ = refl 
ren-id (τ₁ · τ₂) rewrite ren-id τ₁ | ren-id τ₂ = refl
ren-id (τ₁ `→ τ₂) rewrite ren-id τ₁ | ren-id τ₂ = refl
ren-id (`∀ κ τ) rewrite ren-cong lift-id τ | ren-id τ = refl
ren-id (μ F) rewrite ren-id F = refl
ren-id Π = refl
ren-id Σ = refl
ren-id (lab _) = refl
ren-id `▹` = refl
ren-id ⌊ τ ⌋ rewrite ren-id τ = refl
-- ren-id (↑ τ) rewrite ren-id τ = refl
ren-id (f <$> a) rewrite ren-id f | ren-id a = refl


ren-comp : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
           ∀ (τ : Type Δ₁ κ) → ren (ρ₂ ∘ ρ₁) τ ≡ ren ρ₂ (ren ρ₁ τ)
ren-comp _ _   Unit = refl
ren-comp ρ₁ ρ₂ (` x) = refl
ren-comp ρ₁ ρ₂ Π = refl
ren-comp ρ₁ ρ₂ Σ = refl
ren-comp ρ₁ ρ₂ (`λ τ)  rewrite
  trans (ren-cong (lift-comp ρ₁ ρ₂) τ) (ren-comp (lift ρ₁) (lift ρ₂) τ) = refl
ren-comp ρ₁ ρ₂ (τ₁ · τ₂) rewrite
    ren-comp ρ₁ ρ₂ τ₁ 
  | ren-comp ρ₁ ρ₂ τ₂ = refl
ren-comp ρ₁ ρ₂ (τ₁ `→ τ₂) rewrite
    ren-comp ρ₁ ρ₂ τ₁ 
  | ren-comp ρ₁ ρ₂ τ₂ = refl
ren-comp ρ₁ ρ₂ (`∀ κ τ) rewrite
  (trans (ren-cong (lift-comp ρ₁ ρ₂) τ) (ren-comp (lift ρ₁) (lift ρ₂) τ)) = refl
ren-comp ρ₁ ρ₂ (μ F) rewrite
  ren-comp ρ₁ ρ₂ F = refl
ren-comp ρ₁ ρ₂ (lab _) = refl
ren-comp ρ₁ ρ₂ `▹` = refl
ren-comp ρ₁ ρ₂ ⌊ τ ⌋ rewrite
    ren-comp ρ₁ ρ₂ τ = refl
ren-comp ρ₁ ρ₂ (f <$> a) rewrite ren-comp ρ₁ ρ₂ f | ren-comp ρ₁ ρ₂ a = refl
