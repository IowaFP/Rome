{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.SynAna where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Normal.Syntax

open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Properties.Equivalence
open import Rome.Operational.Types.Properties.Substitution

open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

open import Rome.Operational.Containment

--------------------------------------------------------------------------------
-- The types of the bodies of syn and ana

SynT : Type Δ R[ κ ] → Type Δ (κ `→ ★) → Type Δ ★
SynT ρ φ = `∀ (`∀ (((` (S Z) ▹ ` Z) ≲ (weakenₖ (weakenₖ ρ))) ⇒ (⌊ ` (S Z) ⌋ `→ (weakenₖ (weakenₖ φ) · ` Z))))

AnaT : Type Δ R[ κ ] → Type Δ (κ `→ ★) → Type Δ ★ → Type Δ ★
AnaT ρ φ τ = `∀ (`∀ (((` (S Z) ▹ ` Z) ≲ (weakenₖ (weakenₖ ρ))) ⇒ (⌊ ` (S Z) ⌋ `→ (weakenₖ (weakenₖ φ) · ` Z) `→ weakenₖ (weakenₖ τ))))

--------------------------------------------------------------------------------
-- SynT and AnaT respects type equality

SynT-cong : ∀ {ρ₁ ρ₂ : Type Δ R[ κ ]} {φ₁ φ₂ : Type Δ (κ `→ ★)} → ρ₁ ≡ ρ₂ → φ₁ ≡ φ₂ → 
            SynT ρ₁ φ₁ ≡ SynT ρ₂ φ₂
SynT-cong eq₁ eq₂ = 
  cong `∀ (cong `∀ (cong₂ _⇒_ 
    (cong₂ _≲_ refl (cong (weakenₖ ∘ weakenₖ) eq₁)) (cong₂ _`→_ refl (cong₂ _·_ (cong (weakenₖ ∘ weakenₖ) eq₂) refl))))


AnaT-cong : ∀ {ρ₁ ρ₂ : Type Δ R[ κ ]} {φ₁ φ₂ : Type Δ (κ `→ ★)} {τ₁ τ₂ : Type Δ ★} → 
              ρ₁ ≡ ρ₂ → φ₁ ≡ φ₂ → τ₁ ≡ τ₂ → 
              AnaT ρ₁ φ₁ τ₁ ≡ AnaT ρ₂ φ₂ τ₂
AnaT-cong eq₁ eq₂ eq₃ = 
  cong `∀ (cong `∀ (cong₂ _⇒_
    (cong₂ _≲_ refl (cong (weakenₖ ∘ weakenₖ) eq₁)) 
    (cong₂ _`→_
      refl 
      (cong₂ _`→_
        (cong₂ _·_ (cong (weakenₖ ∘ weakenₖ) eq₂) refl) 
        (cong (weakenₖ ∘ weakenₖ) eq₃)))))

--------------------------------------------------------------------------------
-- SynT and AnaT respects type equivalence

SynT-cong-≡t : ∀ {ρ₁ ρ₂ : Type Δ R[ κ ]} {φ₁ φ₂ : Type Δ (κ `→ ★)} → ρ₁ ≡t ρ₂ → φ₁ ≡t φ₂ → 
            SynT ρ₁ φ₁ ≡t SynT ρ₂ φ₂
SynT-cong-≡t eq₁ eq₂ = 
  eq-∀ (eq-∀ (eq-⇒ 
    (eq-refl eq-≲ (renₖ-≡t S (renₖ-≡t S eq₁))) 
    (eq-→ 
      eq-refl 
      (eq-· 
        (renₖ-≡t S (renₖ-≡t S eq₂)) 
        eq-refl))))

AnaT-cong-≡t : ∀ {ρ₁ ρ₂ : Type Δ R[ κ ]} {φ₁ φ₂ : Type Δ (κ `→ ★)} {τ₁ τ₂ : Type Δ ★} → 
              ρ₁ ≡t ρ₂ → φ₁ ≡t φ₂ → τ₁ ≡t τ₂ → 
              AnaT ρ₁ φ₁ τ₁ ≡t AnaT ρ₂ φ₂ τ₂
AnaT-cong-≡t eq₁ eq₂ eq₃ = 
  eq-∀ (eq-∀ (eq-⇒ 
    (eq-refl eq-≲ (renₖ-≡t S (renₖ-≡t S eq₁))) 
    (eq-→ 
      eq-refl 
      (eq-→ 
        (eq-· (renₖ-≡t S (renₖ-≡t S eq₂)) eq-refl) 
        (renₖ-≡t S (renₖ-≡t S eq₃))))))


--------------------------------------------------------------------------------
-- Renaming commutes over syn and ana

doublelift : ∀ {κ₁ κ₂} (r : Renamingₖ Δ₁ Δ₂) (τ : Type Δ₁ κ) → 
               renₖ (liftₖ {κ = κ₁} (liftₖ {κ = κ₂} r)) (weakenₖ (weakenₖ τ)) ≡ 
               weakenₖ (weakenₖ (renₖ r τ))
doublelift r τ = 
  trans 
    (↻-liftₖ-weaken (liftₖ r) (weakenₖ τ)) 
    (cong (renₖ S) (↻-liftₖ-weaken r τ)) 

↻-ren-syn : ∀ (r : Renamingₖ Δ₁ Δ₂) (ρ : Type Δ₁ R[ κ ]) (φ : Type Δ₁ (κ `→ ★)) → 
              renₖ r (SynT ρ φ) ≡ SynT (renₖ r ρ) (renₖ r φ)
↻-ren-syn r ρ φ = 
  cong `∀ (cong `∀ (cong₂ _⇒_ (cong₂ _≲_ refl 
    (doublelift r ρ)) 
  (cong₂ _`→_ refl (cong₂ _·_ 
    (doublelift r φ) refl))))

↻-ren-ana : ∀ (r : Renamingₖ Δ₁ Δ₂) (ρ : Type Δ₁ R[ κ ]) (φ : Type Δ₁ (κ `→ ★)) (τ : Type Δ₁ ★) → 
              renₖ r (AnaT ρ φ τ) ≡ AnaT (renₖ r ρ) (renₖ r φ) (renₖ r τ)
↻-ren-ana r ρ φ τ = 
  cong `∀ (cong `∀ (cong₂ _⇒_ (cong₂ _≲_ refl 
    (doublelift r ρ)) 
  (cong₂ _`→_ refl (cong₂ _`→_ 
    (cong₂ _·_ (doublelift r φ) refl) 
    (doublelift r τ)))))

--------------------------------------------------------------------------------
-- Substitution commutes over syn and ana

doublelifts : ∀ {κ₁ κ₂} (σ : Substitutionₖ Δ₁ Δ₂) (τ : Type Δ₁ κ) → 
               subₖ (liftsₖ {κ = κ₁} (liftsₖ {κ = κ₂} σ)) (weakenₖ (weakenₖ τ)) ≡ 
               weakenₖ (weakenₖ (subₖ σ τ))
doublelifts σ τ = 
  trans 
    (↻-liftsₖ-weaken (liftsₖ σ) (renₖ S τ)) 
    (cong (renₖ S) (↻-liftsₖ-weaken σ τ))

↻-sub-syn : ∀ (σ : Substitutionₖ Δ₁ Δ₂) (ρ : Type Δ₁ R[ κ ]) (φ : Type Δ₁ (κ `→ ★)) → 
            SynT (subₖ σ ρ) (subₖ σ φ) ≡ 
            subₖ σ (SynT ρ φ)
↻-sub-syn σ ρ φ = 
  cong `∀ (cong `∀ (cong₂ _⇒_ (cong₂ _≲_ refl 
    (sym (doublelifts σ ρ))) 
  (cong₂ _`→_ refl (cong₂ _·_ 
    (sym (doublelifts σ φ)) refl))))

↻-sub-ana : ∀ (σ : Substitutionₖ Δ₁ Δ₂) (ρ : Type Δ₁ R[ κ ]) (φ : Type Δ₁ (κ `→ ★)) (τ : Type Δ₁ ★) → 
            AnaT (subₖ σ ρ) (subₖ σ φ) (subₖ σ τ) ≡ 
            subₖ σ (AnaT ρ φ τ) 
↻-sub-ana σ ρ φ τ = 
  cong `∀ (cong `∀ (cong₂ _⇒_ (cong₂ _≲_ refl 
    (sym (doublelifts σ ρ))) 
  (cong₂ _`→_ refl (cong₂ _`→_ 
    (cong₂ _·_ (sym (doublelifts σ φ)) refl) 
    (sym (doublelifts σ τ))))))




