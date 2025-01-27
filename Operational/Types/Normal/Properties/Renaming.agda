module Rome.Operational.Types.Normal.Properties.Renaming where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open TypeProps using (lift-cong ; lift-id ; lift-comp)
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal

--------------------------------------------------------------------------------
-- Renaming respects congruence of Renamings

ren-cong-ne :  ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                (τ : NeutralType Δ₁ κ) → renNE ρ₁ τ ≡ renNE ρ₂ τ
ren-cong    :  ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                (τ : NormalType Δ₁ κ) → ren ρ₁ τ ≡ ren ρ₂ τ
ren-cong-row : ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                (r : Row Δ₁ R[ κ ]) → renRow ρ₁ r ≡ renRow ρ₂ r
ren-cong-pred : ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ≈ ρ₂ → 
                (r : NormalPred Δ₁ R[ κ ]) → renPred ρ₁ r ≡ renPred ρ₂ r

ren-cong-row eq (l ▹ τ) rewrite ren-cong eq l | ren-cong eq τ = refl

ren-cong-ne eq (` x) rewrite eq x = refl
ren-cong-ne eq (ν · τ) rewrite
    ren-cong-ne eq ν
  | ren-cong eq τ = refl
ren-cong-ne eq (Π τ) rewrite ren-cong-ne eq τ = refl 
ren-cong-ne eq (Σ τ) rewrite ren-cong-ne eq τ = refl 
ren-cong-ne eq (x <$> τ) rewrite ren-cong eq x | ren-cong-ne eq τ = refl

ren-cong eq (ne ν) rewrite 
  ren-cong-ne eq ν = refl
ren-cong eq (`λ τ) rewrite 
  ren-cong (TypeProps.lift-cong eq) τ = refl 
ren-cong eq (τ₁ `→ τ₂) rewrite 
    ren-cong eq τ₁ 
  | ren-cong eq τ₂ = refl
ren-cong eq (π ⇒ τ) rewrite 
    ren-cong-pred eq π 
  | ren-cong eq τ = refl  
ren-cong eq (`∀ κ τ) rewrite 
  ren-cong (TypeProps.lift-cong eq) τ = refl 
ren-cong eq (μ τ) rewrite ren-cong eq τ = refl
ren-cong eq Unit = refl
ren-cong eq (lab x) = refl
ren-cong eq ⌊ τ ⌋ rewrite ren-cong eq τ = refl
ren-cong eq (row x) rewrite ren-cong-row eq x = refl
ren-cong eq (Π x) rewrite ren-cong-row eq x = refl
ren-cong eq (ΠL x) rewrite ren-cong-row eq x = refl
ren-cong eq (Σ x) rewrite ren-cong-row eq x = refl
ren-cong eq (ΣL x) rewrite ren-cong-row eq x = refl

ren-cong-pred eq (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite ren-cong eq ρ₁ | ren-cong eq ρ₂ | ren-cong eq ρ₃ = refl
ren-cong-pred eq (ρ₁ ≲ ρ₂) 
  rewrite ren-cong eq ρ₁ | ren-cong eq ρ₂ = refl

--------------------------------------------------------------------------------
-- Renaming preserves identities (functor law #1)
ren-id    : ∀ (τ : NormalType Δ κ) → ren id τ ≡ τ
ren-id-ne : ∀ (τ : NeutralType Δ κ) → renNE id τ ≡ τ
ren-id-row : ∀ (r : Row Δ R[ κ ]) → renRow id r ≡ r
ren-id-pred : ∀ (τ : NormalPred Δ R[ κ ]) → renPred id τ ≡ τ

ren-id-row (l ▹ τ) rewrite ren-id l | ren-id τ  = refl

ren-id-ne (` x) = refl
ren-id-ne (τ₁ · τ₂) rewrite
    ren-id-ne τ₁
  | ren-id τ₂ = refl
ren-id-ne (Π τ) rewrite ren-id-ne τ = refl
ren-id-ne (Σ τ) rewrite ren-id-ne τ = refl
ren-id-ne (x <$> τ) rewrite ren-id x | ren-id-ne τ = refl 

ren-id (ne ν) rewrite ren-id-ne ν = refl
ren-id (`λ τ) rewrite 
    ren-cong lift-id τ 
  | ren-id τ = refl 
ren-id (τ₁ `→ τ₂) rewrite 
    ren-id τ₁ 
  | ren-id τ₂ = refl
ren-id (π ⇒ τ) rewrite 
    ren-id-pred π 
  | ren-id τ = refl  
ren-id (`∀ κ τ) rewrite 
    ren-cong lift-id τ 
  | ren-id τ = refl
ren-id (μ τ) rewrite ren-id τ = refl
ren-id Unit = refl
ren-id (lab x) = refl
ren-id ⌊ τ ⌋ rewrite ren-id τ = refl
ren-id (row x) rewrite ren-id-row x = refl
ren-id (Π x)  rewrite ren-id-row x  = refl 
ren-id (ΠL x) rewrite ren-id-row x  = refl 
ren-id (Σ x)  rewrite ren-id-row x  = refl 
ren-id (ΣL x) rewrite ren-id-row x  = refl

ren-id-pred (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite ren-id ρ₁ | ren-id ρ₂ | ren-id ρ₃ = refl
ren-id-pred (ρ₁ ≲ ρ₂) 
  rewrite ren-id ρ₁ | ren-id ρ₂ = refl

--------------------------------------------------------------------------------
-- Renaming preserves Composition (functor law #2)

ren-comp     : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
                  (τ : NormalType Δ₁ κ) → ren (ρ₂ ∘ ρ₁) τ ≡ ren ρ₂ (ren ρ₁ τ)
ren-comp-ne  : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
                (τ : NeutralType Δ₁ κ) → renNE (ρ₂ ∘ ρ₁) τ ≡ renNE ρ₂ (renNE ρ₁ τ)
ren-comp-row :  ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
                  (r : Row Δ₁ R[ κ ]) → renRow (ρ₂ ∘ ρ₁) r ≡ renRow ρ₂ (renRow ρ₁ r)
ren-comp-pred :  ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
                   (π : NormalPred Δ₁ R[ κ ]) → renPred (ρ₂ ∘ ρ₁) π ≡ renPred ρ₂ (renPred ρ₁ π)

ren-comp-ne ρ₁ ρ₂ (` x) = refl
ren-comp-ne ρ₁ ρ₂ (ν · τ) rewrite
    ren-comp-ne ρ₁ ρ₂ ν
  | ren-comp ρ₁ ρ₂ τ = refl
ren-comp-ne ρ₁ ρ₂ (Π τ)    rewrite ren-comp-ne ρ₁ ρ₂ τ = refl
ren-comp-ne ρ₁ ρ₂ (Σ τ)    rewrite ren-comp-ne ρ₁ ρ₂ τ = refl
ren-comp-ne ρ₁ ρ₂ (x <$> τ) rewrite ren-comp ρ₁ ρ₂ x  | ren-comp-ne ρ₁ ρ₂ τ  = refl

ren-comp ρ₁ ρ₂ (ne ν) rewrite ren-comp-ne ρ₁ ρ₂ ν  = refl
ren-comp ρ₁ ρ₂ (`λ τ)  rewrite
  trans (ren-cong (lift-comp ρ₁ ρ₂) τ) (ren-comp (lift ρ₁) (lift ρ₂) τ) = refl
ren-comp ρ₁ ρ₂ (τ₁ `→ τ₂) rewrite
    ren-comp ρ₁ ρ₂ τ₁ 
  | ren-comp ρ₁ ρ₂ τ₂ = refl
ren-comp ρ₁ ρ₂ (π ⇒ τ) rewrite
    ren-comp-pred ρ₁ ρ₂ π 
  | ren-comp ρ₁ ρ₂ τ = refl  
ren-comp ρ₁ ρ₂ (`∀ κ τ) rewrite
  (trans (ren-cong (lift-comp ρ₁ ρ₂) τ) (ren-comp (lift ρ₁) (lift ρ₂) τ)) = refl
ren-comp ρ₁ ρ₂ (μ τ) rewrite ren-comp ρ₁ ρ₂ τ = refl
ren-comp ρ₁ ρ₂ Unit = refl
ren-comp ρ₁ ρ₂ (lab x) = refl
ren-comp ρ₁ ρ₂ ⌊ τ ⌋ rewrite ren-comp ρ₁ ρ₂ τ = refl 
ren-comp ρ₁ ρ₂ (row x) rewrite ren-comp-row ρ₁ ρ₂ x = refl
ren-comp ρ₁ ρ₂ (Π x)  rewrite ren-comp-row ρ₁ ρ₂ x = refl
ren-comp ρ₁ ρ₂ (ΠL x) rewrite ren-comp-row ρ₁ ρ₂ x = refl
ren-comp ρ₁ ρ₂ (Σ x)  rewrite ren-comp-row ρ₁ ρ₂ x = refl
ren-comp ρ₁ ρ₂ (ΣL x) rewrite ren-comp-row ρ₁ ρ₂ x = refl

ren-comp-row ρ₁ ρ₂ (l ▹ τ) rewrite ren-comp ρ₁ ρ₂ l | ren-comp ρ₁ ρ₂ τ = refl

ren-comp-pred ρ ρ' (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite ren-comp ρ ρ' ρ₁ | ren-comp ρ ρ' ρ₂ | ren-comp ρ ρ' ρ₃ = refl
ren-comp-pred ρ ρ' (ρ₁ ≲ ρ₂)
  rewrite ren-comp ρ ρ' ρ₁ | ren-comp ρ ρ' ρ₂ = refl