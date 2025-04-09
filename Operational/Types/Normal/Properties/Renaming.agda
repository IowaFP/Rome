{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Normal.Properties.Renaming where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Renaming 

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming


--------------------------------------------------------------------------------
-- Renaming respects congruence of Renamings

renₖNE-cong :  ∀ {ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                (τ : NeutralType Δ₁ κ) → renₖNE ρ₁ τ ≡ renₖNE ρ₂ τ
renₖNF-cong    :  ∀ {ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                (τ : NormalType Δ₁ κ) → renₖNF ρ₁ τ ≡ renₖNF ρ₂ τ
renₖNF-cong-row    :  ∀ {ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                (ρ : SimpleRow NormalType Δ₁ R[ κ ]) → renRowₖNF ρ₁ ρ ≡ renRowₖNF ρ₂ ρ
renₖNF-cong-pred : ∀ {ρ₁ ρ₂ : Renamingₖ Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                (r : NormalPred Δ₁ R[ κ ]) → renPredₖNF ρ₁ r ≡ renPredₖNF ρ₂ r

-- renₖNF-cong-row eq (l ▹ τ) rewrite renₖNF-cong eq l | renₖNF-cong eq τ = refl

renₖNE-cong eq (` x) rewrite eq x = refl
renₖNE-cong eq (ν · τ) rewrite
    renₖNE-cong eq ν
  | renₖNF-cong eq τ = refl
-- renₖNE-cong eq (Π τ) rewrite renₖNE-cong eq τ = refl 
-- renₖNE-cong eq (Σ τ) rewrite renₖNE-cong eq τ = refl 
renₖNE-cong eq (x <$> τ) rewrite renₖNF-cong eq x | renₖNE-cong eq τ = refl

renₖNF-cong eq (ne ν) rewrite 
  renₖNE-cong eq ν = refl
renₖNF-cong eq (`λ τ) rewrite 
  renₖNF-cong (liftₖ-cong eq) τ = refl 
renₖNF-cong eq (τ₁ `→ τ₂) rewrite 
    renₖNF-cong eq τ₁ 
  | renₖNF-cong eq τ₂ = refl
renₖNF-cong eq (π ⇒ τ) rewrite 
    renₖNF-cong-pred eq π 
  | renₖNF-cong eq τ = refl  
renₖNF-cong eq (`∀ τ) rewrite 
  renₖNF-cong (liftₖ-cong eq) τ = refl 
renₖNF-cong eq (μ τ) rewrite renₖNF-cong eq τ = refl
-- renₖNF-cong eq ε = refl
renₖNF-cong eq (lab x) = refl
renₖNF-cong eq ⌊ τ ⌋ rewrite renₖNF-cong eq τ = refl
-- renₖNF-cong eq (l ▹ τ) rewrite renₖNF-cong eq l | renₖNF-cong eq τ = refl
renₖNF-cong eq (Π x) rewrite renₖNF-cong eq x = refl
renₖNF-cong eq (ΠL x) rewrite renₖNF-cong eq x = refl
renₖNF-cong eq (Σ x) rewrite renₖNF-cong eq x = refl
renₖNF-cong eq (ΣL x) rewrite renₖNF-cong eq x = refl
renₖNF-cong eq ⦅ ρ ⦆ rewrite renₖNF-cong-row eq ρ = refl

renₖNF-cong-pred eq (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₖNF-cong eq ρ₁ | renₖNF-cong eq ρ₂ | renₖNF-cong eq ρ₃ = refl
renₖNF-cong-pred eq (ρ₁ ≲ ρ₂) 
  rewrite renₖNF-cong eq ρ₁ | renₖNF-cong eq ρ₂ = refl

renₖNF-cong-row eq [] = refl
renₖNF-cong-row eq (τ ∷ ρ) rewrite renₖNF-cong eq τ | renₖNF-cong-row eq ρ = refl

--------------------------------------------------------------------------------
-- Renamingₖ preserves identities (functor law #1)
renₖNF-id    : ∀ (τ : NormalType Δ κ) → renₖNF id τ ≡ τ
renₖNE-id : ∀ (τ : NeutralType Δ κ) → renₖNE id τ ≡ τ
renₖNF-id-row : ∀ (r : SimpleRow NormalType Δ R[ κ ]) → renRowₖNF id r ≡ r
renₖNF-id-pred : ∀ (τ : NormalPred Δ R[ κ ]) → renPredₖNF id τ ≡ τ

-- renₖNF-id-row (l ▹ τ) rewrite renₖNF-id l | renₖNF-id τ  = refl

renₖNE-id (` x) = refl
renₖNE-id (τ₁ · τ₂) rewrite
    renₖNE-id τ₁
  | renₖNF-id τ₂ = refl
-- renₖNE-id (Π τ) rewrite renₖNE-id τ = refl
-- renₖNE-id (Σ τ) rewrite renₖNE-id τ = refl
renₖNE-id (x <$> τ) rewrite renₖNF-id x | renₖNE-id τ = refl 

renₖNF-id (ne ν) rewrite renₖNE-id ν = refl
renₖNF-id (`λ τ) rewrite 
    renₖNF-cong liftₖ-id τ 
  | renₖNF-id τ = refl 
renₖNF-id (τ₁ `→ τ₂) rewrite 
    renₖNF-id τ₁ 
  | renₖNF-id τ₂ = refl
renₖNF-id (π ⇒ τ) rewrite 
    renₖNF-id-pred π 
  | renₖNF-id τ = refl  
renₖNF-id (`∀ τ) rewrite 
    renₖNF-cong liftₖ-id τ 
  | renₖNF-id τ = refl
renₖNF-id (μ τ) rewrite renₖNF-id τ = refl
-- renₖNF-id ε = refl
renₖNF-id (lab x) = refl
renₖNF-id ⌊ τ ⌋ rewrite renₖNF-id τ = refl
-- renₖNF-id (l ▹ τ) rewrite renₖNF-id l | renₖNF-id τ  = refl
renₖNF-id (Π x)  rewrite renₖNF-id x  = refl 
renₖNF-id (ΠL x) rewrite renₖNF-id x  = refl 
renₖNF-id (Σ x)  rewrite renₖNF-id x  = refl 
renₖNF-id (ΣL x) rewrite renₖNF-id x  = refl
renₖNF-id ⦅ ρ ⦆ rewrite renₖNF-id-row ρ = refl
renₖNF-id-pred (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₖNF-id ρ₁ | renₖNF-id ρ₂ | renₖNF-id ρ₃ = refl
renₖNF-id-pred (ρ₁ ≲ ρ₂) 
  rewrite renₖNF-id ρ₁ | renₖNF-id ρ₂ = refl

renₖNF-id-row [] = refl
renₖNF-id-row (τ ∷ ρ) rewrite renₖNF-id τ | renₖNF-id-row ρ = refl

--------------------------------------------------------------------------------
-- Renamingₖ preserves Composition (functor law #2)

renₖNF-comp     : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) → 
                  (τ : NormalType Δ₁ κ) → renₖNF (ρ₂ ∘ ρ₁) τ ≡ renₖNF ρ₂ (renₖNF ρ₁ τ)
renₖNE-comp  : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) → 
                (τ : NeutralType Δ₁ κ) → renₖNE (ρ₂ ∘ ρ₁) τ ≡ renₖNE ρ₂ (renₖNE ρ₁ τ)
renₖNF-comp-row :  ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) → 
                  (r : SimpleRow NormalType Δ₁ R[ κ ]) → renRowₖNF (ρ₂ ∘ ρ₁) r ≡ renRowₖNF ρ₂ (renRowₖNF ρ₁ r)
renₖNF-comp-pred :  ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) → 
                   (π : NormalPred Δ₁ R[ κ ]) → renPredₖNF (ρ₂ ∘ ρ₁) π ≡ renPredₖNF ρ₂ (renPredₖNF ρ₁ π)

renₖNE-comp ρ₁ ρ₂ (` x) = refl
renₖNE-comp ρ₁ ρ₂ (ν · τ) rewrite
    renₖNE-comp ρ₁ ρ₂ ν
  | renₖNF-comp ρ₁ ρ₂ τ = refl
renₖNE-comp ρ₁ ρ₂ (x <$> τ) rewrite renₖNF-comp ρ₁ ρ₂ x  | renₖNE-comp ρ₁ ρ₂ τ  = refl

renₖNF-comp ρ₁ ρ₂ (ne ν) rewrite renₖNE-comp ρ₁ ρ₂ ν  = refl
renₖNF-comp ρ₁ ρ₂ (`λ τ)  rewrite
  trans (renₖNF-cong (liftₖ-comp ρ₁ ρ₂) τ) (renₖNF-comp (liftₖ ρ₁) (liftₖ ρ₂) τ) = refl
renₖNF-comp ρ₁ ρ₂ (τ₁ `→ τ₂) rewrite
    renₖNF-comp ρ₁ ρ₂ τ₁ 
  | renₖNF-comp ρ₁ ρ₂ τ₂ = refl
renₖNF-comp ρ₁ ρ₂ (π ⇒ τ) rewrite
    renₖNF-comp-pred ρ₁ ρ₂ π 
  | renₖNF-comp ρ₁ ρ₂ τ = refl  
renₖNF-comp ρ₁ ρ₂ (`∀ τ) rewrite
  (trans (renₖNF-cong (liftₖ-comp ρ₁ ρ₂) τ) (renₖNF-comp (liftₖ ρ₁) (liftₖ ρ₂) τ)) = refl
renₖNF-comp ρ₁ ρ₂ (μ τ) rewrite renₖNF-comp ρ₁ ρ₂ τ = refl
-- renₖNF-comp ρ₁ ρ₂ ε = refl
renₖNF-comp ρ₁ ρ₂ (lab x) = refl 
renₖNF-comp ρ₁ ρ₂ ⌊ τ ⌋ rewrite renₖNF-comp ρ₁ ρ₂ τ = refl 
-- renₖNF-comp ρ₁ ρ₂ (l ▹ τ) rewrite renₖNF-comp ρ₁ ρ₂ l | renₖNF-comp ρ₁ ρ₂ τ = refl
renₖNF-comp ρ₁ ρ₂ (Π x)  rewrite renₖNF-comp ρ₁ ρ₂ x = refl
renₖNF-comp ρ₁ ρ₂ (ΠL x) rewrite renₖNF-comp ρ₁ ρ₂ x = refl
renₖNF-comp ρ₁ ρ₂ (Σ x)  rewrite renₖNF-comp ρ₁ ρ₂ x = refl
renₖNF-comp ρ₁ ρ₂ (ΣL x) rewrite renₖNF-comp ρ₁ ρ₂ x = refl
renₖNF-comp ρ₁ ρ₂ ⦅ ρ ⦆ rewrite renₖNF-comp-row ρ₁ ρ₂ ρ = refl



renₖNF-comp-pred ρ ρ' (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₖNF-comp ρ ρ' ρ₁ | renₖNF-comp ρ ρ' ρ₂ | renₖNF-comp ρ ρ' ρ₃ = refl
renₖNF-comp-pred ρ ρ' (ρ₁ ≲ ρ₂) 
  rewrite renₖNF-comp ρ ρ' ρ₁ | renₖNF-comp ρ ρ' ρ₂ = refl

renₖNF-comp-row r₁ r₂ [] = refl
renₖNF-comp-row r₁ r₂ (τ ∷ ρ) rewrite renₖNF-comp r₁ r₂ τ | renₖNF-comp-row r₁ r₂ ρ = refl

--------------------------------------------------------------------------------
-- Weakening commutes with renaming

↻-weakenₖNF-renₖNF  : ∀ {κ'} (ρ : Renamingₖ Δ₁ Δ₂) (τ : NormalType Δ₁ κ) → 
                renₖNF (liftₖ {κ = κ'} ρ) (renₖNF S τ) ≡ renₖNF S (renₖNF ρ τ)
↻-weakenₖNF-renₖNF  {κ' = κ'} ρ τ 
  rewrite 
    sym (renₖNF-comp (S {κ₂ = κ'}) (liftₖ ρ) τ) 
  | renₖNF-comp ρ (S {κ₂ = κ'}) τ = refl

↻-weakenPredₖNF-renPredₖNF  : ∀ {κ'} (ρ : Renamingₖ Δ₁ Δ₂) (π : NormalPred Δ₁ R[ κ ]) → 
                renPredₖNF (liftₖ {κ = κ'} ρ) (renPredₖNF S π) ≡ renPredₖNF S (renPredₖNF ρ π)
↻-weakenPredₖNF-renPredₖNF {κ' = κ'} ρ (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite 
    ↻-weakenₖNF-renₖNF {κ' = κ'} ρ ρ₁ 
  | ↻-weakenₖNF-renₖNF {κ' = κ'} ρ ρ₂ 
  | ↻-weakenₖNF-renₖNF {κ' = κ'} ρ ρ₃ = refl
↻-weakenPredₖNF-renPredₖNF {κ' = κ'} ρ (ρ₁ ≲ ρ₂)
  rewrite 
    ↻-weakenₖNF-renₖNF {κ' = κ'} ρ ρ₁ 
  | ↻-weakenₖNF-renₖNF {κ' = κ'} ρ ρ₂ = refl

--------------------------------------------------------------------------------
-- Renamingₖ commutes with embedding

↻-ren-⇑ : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → (τ : NormalType Δ₁ κ) → 
          ⇑ (renₖNF ρ τ) ≡ renₖ ρ (⇑ τ)
↻-ren-⇑Row : ∀ (r : Renamingₖ Δ₁ Δ₂) → (ρ : SimpleRow NormalType Δ₁ R[ κ ]) → 
          ⇑Row (renRowₖNF r ρ) ≡ renRowₖ r (⇑Row ρ)
↻-ren-⇑NE : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → (τ : NeutralType Δ₁ κ) → 
          ⇑NE (renₖNE ρ τ) ≡ renₖ ρ (⇑NE τ)
↻-ren-⇑Pred : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → (π : NormalPred Δ₁ R[ κ ]) → 
            ⇑Pred (renPredₖNF ρ π) ≡ renPredₖ ρ (⇑Pred π)      

-- ↻-ren-⇑ ρ ε = refl
↻-ren-⇑ ρ (ne x) = ↻-ren-⇑NE ρ x
↻-ren-⇑ ρ (`λ τ) = cong `λ (↻-ren-⇑ (liftₖ ρ) τ)
↻-ren-⇑ ρ (τ₁ `→ τ₂) = cong₂ _`→_ (↻-ren-⇑ ρ τ₁) (↻-ren-⇑ ρ τ₂) 
↻-ren-⇑ ρ (`∀ τ) = cong (`∀) (↻-ren-⇑ (liftₖ ρ) τ)
↻-ren-⇑ ρ (μ τ) = cong μ (↻-ren-⇑ ρ τ)
↻-ren-⇑ ρ (π ⇒ τ) = cong₂ _⇒_ (↻-ren-⇑Pred ρ π) (↻-ren-⇑ ρ τ)
↻-ren-⇑ ρ (lab l) = refl
↻-ren-⇑ ρ ⌊ τ ⌋ = cong ⌊_⌋ (↻-ren-⇑ ρ τ)
-- ↻-ren-⇑ ρ (l ▹ τ) = cong₂ _▹_ (↻-ren-⇑ ρ l) (↻-ren-⇑ ρ τ)
↻-ren-⇑ ρ (Π r) = cong (λ x → Π · x) (↻-ren-⇑ ρ r) 
↻-ren-⇑ ρ (ΠL r) = cong (λ x → Π · x) (↻-ren-⇑ ρ r)
↻-ren-⇑ ρ (Σ r)  = cong (λ x → Σ · x) (↻-ren-⇑ ρ r)
↻-ren-⇑ ρ (ΣL r) = cong (λ x → Σ · x) (↻-ren-⇑ ρ r)
↻-ren-⇑ r ⦅ ρ ⦆ = cong ⦅_⦆ (↻-ren-⇑Row r ρ)

↻-ren-⇑NE ρ (` α) = refl
↻-ren-⇑NE ρ (τ₁ · τ₂) = cong₂ _·_ (↻-ren-⇑NE ρ τ₁) (↻-ren-⇑ ρ τ₂)
↻-ren-⇑NE ρ (φ <$> τ) = cong₂ _<$>_ (↻-ren-⇑ ρ φ) (↻-ren-⇑NE ρ τ)

↻-ren-⇑Pred ρ (ρ₁ · ρ₂ ~ ρ₃) rewrite 
    ↻-ren-⇑ ρ ρ₁ 
  | ↻-ren-⇑ ρ ρ₂
  | ↻-ren-⇑ ρ ρ₃ = refl
↻-ren-⇑Pred ρ (ρ₁ ≲ ρ₂) = cong₂ _≲_ (↻-ren-⇑ ρ ρ₁) (↻-ren-⇑ ρ ρ₂)

↻-ren-⇑Row r [] = refl
↻-ren-⇑Row r (τ ∷ ρ) rewrite ↻-ren-⇑ r τ | ↻-ren-⇑Row r ρ = refl


