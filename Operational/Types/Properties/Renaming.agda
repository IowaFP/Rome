module Rome.Operational.Types.Properties.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence

--------------------------------------------------------------------------------
-- ↑ing respects congruence, identities, and composition.
--

liftₖ-id : ∀ (x : KVar (Δ ,, κ₂) κ₁) → liftₖ id x ≡ x
liftₖ-id Z = refl
liftₖ-id (S x) = refl

liftₖ-comp : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) → 
            ∀ (x : KVar (Δ₁ ,, κ₂) κ₁) → liftₖ (ρ₂ ∘ ρ₁) x ≡ liftₖ ρ₂ (liftₖ ρ₁ x)
liftₖ-comp ρ₁ ρ₂ Z = refl
liftₖ-comp ρ₁ ρ₂ (S x) = refl

liftₖ-cong : ∀ {ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂} → (ρ₁ ≈ ρ₂) → 
              (x : KVar (Δ₁ ,, κ₂) κ) → liftₖ ρ₁ x ≡ liftₖ ρ₂ x
liftₖ-cong eq Z = refl
liftₖ-cong eq (S x) = cong S (eq x)


--------------------------------------------------------------------------------
-- Renamingₖ respects congruence, identities, and composition.

renₖ-cong :  ∀ {ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
              (τ : Type Δ₁ κ) → renₖ ρ₁ τ ≡ renₖ ρ₂ τ
renₖ-cong-pred : ∀ {ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                  (π : Pred Δ₁ R[ κ ]) → renPredₖ ρ₁ π ≡ renPredₖ ρ₂ π
renₖ-cong eq ε = refl
renₖ-cong eq (` x) rewrite eq x = refl
renₖ-cong eq (`λ τ) rewrite renₖ-cong (liftₖ-cong eq) τ = refl 
renₖ-cong eq (τ₁ · τ₂) rewrite renₖ-cong eq τ₁ | renₖ-cong eq τ₂ = refl
renₖ-cong eq (τ₁ `→ τ₂) rewrite renₖ-cong eq τ₁ | renₖ-cong eq τ₂ = refl
renₖ-cong eq (π ⇒ τ) rewrite renₖ-cong-pred eq π | renₖ-cong eq τ = refl
renₖ-cong eq (`∀ κ τ) rewrite renₖ-cong (liftₖ-cong eq) τ = refl 
renₖ-cong eq (μ F) rewrite renₖ-cong eq F = refl 
renₖ-cong eq Π = refl 
renₖ-cong eq Σ = refl 
renₖ-cong eq (lab _) = refl
renₖ-cong eq (l ▹ τ) rewrite renₖ-cong eq l | renₖ-cong eq τ = refl
renₖ-cong eq ⌊ τ ⌋ rewrite renₖ-cong eq τ = refl
renₖ-cong eq (f <$> a) rewrite renₖ-cong eq f | renₖ-cong eq a = refl

renₖ-cong-pred eq (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₖ-cong eq ρ₁ | renₖ-cong eq ρ₂ | renₖ-cong eq ρ₃ = refl
renₖ-cong-pred eq (ρ₁ ≲ ρ₂) 
  rewrite renₖ-cong eq ρ₁ | renₖ-cong eq ρ₂ = refl

renₖ-id : ∀ (τ : Type Δ κ) → renₖ id τ ≡ τ
renₖ-id-pred : ∀ (π : Pred Δ R[ κ ]) → renPredₖ id π ≡ π
renₖ-id ε = refl
renₖ-id (` x) = refl
renₖ-id (`λ τ) rewrite renₖ-cong liftₖ-id τ | renₖ-id τ = refl 
renₖ-id (τ₁ · τ₂) rewrite renₖ-id τ₁ | renₖ-id τ₂ = refl
renₖ-id (τ₁ `→ τ₂) rewrite renₖ-id τ₁ | renₖ-id τ₂ = refl
renₖ-id (π ⇒ ρ) rewrite renₖ-id-pred π | renₖ-id ρ  = refl
renₖ-id (`∀ κ τ) rewrite renₖ-cong liftₖ-id τ | renₖ-id τ = refl
renₖ-id (μ F) rewrite renₖ-id F = refl
renₖ-id Π = refl
renₖ-id Σ = refl
renₖ-id (lab _) = refl
renₖ-id (l ▹ τ) rewrite renₖ-id l | renₖ-id τ = refl
renₖ-id ⌊ τ ⌋ rewrite renₖ-id τ = refl
-- renₖ-id (↑ τ) rewrite renₖ-id τ = refl
renₖ-id (f <$> a) rewrite renₖ-id f | renₖ-id a = refl

renₖ-id-pred (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₖ-id ρ₁ | renₖ-id ρ₂ | renₖ-id ρ₃ = refl
renₖ-id-pred (ρ₁ ≲ ρ₂)
  rewrite renₖ-id ρ₁ | renₖ-id ρ₂ = refl 


renₖ-comp : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) → 
           ∀ (τ : Type Δ₁ κ) → renₖ (ρ₂ ∘ ρ₁) τ ≡ renₖ ρ₂ (renₖ ρ₁ τ)
renₖ-comp-pred : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) → 
                ∀ (π : Pred Δ₁ R[ κ ]) → renPredₖ (ρ₂ ∘ ρ₁) π ≡ renPredₖ ρ₂ (renPredₖ ρ₁ π)
renₖ-comp _ _   ε = refl
renₖ-comp ρ₁ ρ₂ (` x) = refl
renₖ-comp ρ₁ ρ₂ Π = refl
renₖ-comp ρ₁ ρ₂ Σ = refl
renₖ-comp ρ₁ ρ₂ (`λ τ)  rewrite
  trans (renₖ-cong (liftₖ-comp ρ₁ ρ₂) τ) (renₖ-comp (liftₖ ρ₁) (liftₖ ρ₂) τ) = refl
renₖ-comp ρ₁ ρ₂ (τ₁ · τ₂) rewrite
    renₖ-comp ρ₁ ρ₂ τ₁ 
  | renₖ-comp ρ₁ ρ₂ τ₂ = refl
renₖ-comp ρ₁ ρ₂ (τ₁ `→ τ₂) rewrite
    renₖ-comp ρ₁ ρ₂ τ₁ 
  | renₖ-comp ρ₁ ρ₂ τ₂ = refl
renₖ-comp ρ₁ ρ₂ (`∀ κ τ) rewrite
  (trans (renₖ-cong (liftₖ-comp ρ₁ ρ₂) τ) (renₖ-comp (liftₖ ρ₁) (liftₖ ρ₂) τ)) = refl
renₖ-comp ρ₁ ρ₂ (μ F) rewrite
  renₖ-comp ρ₁ ρ₂ F = refl
renₖ-comp ρ₁ ρ₂ (lab _) = refl
renₖ-comp ρ₁ ρ₂ (l ▹ τ) rewrite renₖ-comp ρ₁ ρ₂ l | renₖ-comp ρ₁ ρ₂ τ = refl
renₖ-comp ρ₁ ρ₂ ⌊ τ ⌋ rewrite
    renₖ-comp ρ₁ ρ₂ τ = refl
renₖ-comp ρ₁ ρ₂ (f <$> a) rewrite renₖ-comp ρ₁ ρ₂ f | renₖ-comp ρ₁ ρ₂ a = refl
renₖ-comp ρ₁ ρ₂ (π ⇒ τ) rewrite renₖ-comp-pred ρ₁ ρ₂ π | renₖ-comp ρ₁ ρ₂ τ = refl

renₖ-comp-pred ρ ρ' (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₖ-comp ρ ρ' ρ₁ | renₖ-comp ρ ρ' ρ₂ | renₖ-comp ρ ρ' ρ₃ = refl
renₖ-comp-pred ρ ρ' (ρ₁ ≲ ρ₂)
  rewrite renₖ-comp ρ ρ' ρ₁ | renₖ-comp ρ ρ' ρ₂ = refl 

↻-liftₖ-weaken : ∀ {κ'} (ρ : Renamingₖ Δ₁ Δ₂) (τ : Type Δ₁ κ) → 
                renₖ (liftₖ {κ = κ'} ρ) (renₖ S τ) ≡ renₖ S (renₖ ρ τ)
↻-liftₖ-weaken {κ' = κ'} ρ τ rewrite sym (renₖ-comp (S {κ₂ = κ'}) (liftₖ ρ) τ) | renₖ-comp ρ (S {κ₂ = κ'}) τ = refl
