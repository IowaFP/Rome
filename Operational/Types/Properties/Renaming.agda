module Rome.Operational.Types.Properties.Renaming where

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
ren-cong-pred : ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                  (π : Pred Δ₁ R[ κ ]) → renPred ρ₁ π ≡ renPred ρ₂ π
ren-cong eq Unit = refl
ren-cong eq (` x) rewrite eq x = refl
ren-cong eq (`λ τ) rewrite ren-cong (lift-cong eq) τ = refl 
ren-cong eq (τ₁ · τ₂) rewrite ren-cong eq τ₁ | ren-cong eq τ₂ = refl
ren-cong eq (τ₁ `→ τ₂) rewrite ren-cong eq τ₁ | ren-cong eq τ₂ = refl
ren-cong eq (π ⇒ τ) rewrite ren-cong-pred eq π | ren-cong eq τ = refl
ren-cong eq (`∀ κ τ) rewrite ren-cong (lift-cong eq) τ = refl 
ren-cong eq (μ F) rewrite ren-cong eq F = refl 
ren-cong eq Π = refl 
ren-cong eq Σ = refl 
ren-cong eq (lab _) = refl
ren-cong eq (l ▹ τ) rewrite ren-cong eq l | ren-cong eq τ = refl
ren-cong eq ⌊ τ ⌋ rewrite ren-cong eq τ = refl
ren-cong eq (f <$> a) rewrite ren-cong eq f | ren-cong eq a = refl

ren-cong-pred eq (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite ren-cong eq ρ₁ | ren-cong eq ρ₂ | ren-cong eq ρ₃ = refl
ren-cong-pred eq (ρ₁ ≲ ρ₂) 
  rewrite ren-cong eq ρ₁ | ren-cong eq ρ₂ = refl

ren-id : ∀ (τ : Type Δ κ) → ren id τ ≡ τ
ren-id-pred : ∀ (π : Pred Δ R[ κ ]) → renPred id π ≡ π
ren-id Unit = refl
ren-id (` x) = refl
ren-id (`λ τ) rewrite ren-cong lift-id τ | ren-id τ = refl 
ren-id (τ₁ · τ₂) rewrite ren-id τ₁ | ren-id τ₂ = refl
ren-id (τ₁ `→ τ₂) rewrite ren-id τ₁ | ren-id τ₂ = refl
ren-id (π ⇒ ρ) rewrite ren-id-pred π | ren-id ρ  = refl
ren-id (`∀ κ τ) rewrite ren-cong lift-id τ | ren-id τ = refl
ren-id (μ F) rewrite ren-id F = refl
ren-id Π = refl
ren-id Σ = refl
ren-id (lab _) = refl
ren-id (l ▹ τ) rewrite ren-id l | ren-id τ = refl
ren-id ⌊ τ ⌋ rewrite ren-id τ = refl
-- ren-id (↑ τ) rewrite ren-id τ = refl
ren-id (f <$> a) rewrite ren-id f | ren-id a = refl

ren-id-pred (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite ren-id ρ₁ | ren-id ρ₂ | ren-id ρ₃ = refl
ren-id-pred (ρ₁ ≲ ρ₂)
  rewrite ren-id ρ₁ | ren-id ρ₂ = refl 


ren-comp : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
           ∀ (τ : Type Δ₁ κ) → ren (ρ₂ ∘ ρ₁) τ ≡ ren ρ₂ (ren ρ₁ τ)
ren-comp-pred : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
                ∀ (π : Pred Δ₁ R[ κ ]) → renPred (ρ₂ ∘ ρ₁) π ≡ renPred ρ₂ (renPred ρ₁ π)
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
ren-comp ρ₁ ρ₂ (l ▹ τ) rewrite ren-comp ρ₁ ρ₂ l | ren-comp ρ₁ ρ₂ τ = refl
ren-comp ρ₁ ρ₂ ⌊ τ ⌋ rewrite
    ren-comp ρ₁ ρ₂ τ = refl
ren-comp ρ₁ ρ₂ (f <$> a) rewrite ren-comp ρ₁ ρ₂ f | ren-comp ρ₁ ρ₂ a = refl
ren-comp ρ₁ ρ₂ (π ⇒ τ) rewrite ren-comp-pred ρ₁ ρ₂ π | ren-comp ρ₁ ρ₂ τ = refl

ren-comp-pred ρ ρ' (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite ren-comp ρ ρ' ρ₁ | ren-comp ρ ρ' ρ₂ | ren-comp ρ ρ' ρ₃ = refl
ren-comp-pred ρ ρ' (ρ₁ ≲ ρ₂)
  rewrite ren-comp ρ ρ' ρ₁ | ren-comp ρ ρ' ρ₂ = refl 

↻-lift-weaken : ∀ {κ'} (ρ : Renaming Δ₁ Δ₂) (τ : Type Δ₁ κ) → 
                ren (lift {κ = κ'} ρ) (ren S τ) ≡ ren S (ren ρ τ)
↻-lift-weaken {κ' = κ'} ρ τ rewrite sym (ren-comp (S {κ₂ = κ'}) (lift ρ) τ) | ren-comp ρ (S {κ₂ = κ'}) τ = refl
