{-# OPTIONS --safe #-}
module Rome.Operational.Types.Normal.SynAna where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Equivalence.Relation

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution

open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Equivalence.Properties
open import Rome.Operational.Types.Properties.Substitution

open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

open import Rome.Operational.Containment

--------------------------------------------------------------------------------
-- The types of the bodies of syn and ana

-- 
SynT' : NormalType Δ R[ κ ] → NormalType Δ (κ `→ ★) → NormalType Δ ★
SynT' {κ = κ} ρ φ = ⇓ (SynT (⇑ ρ) (⇑ φ))
  -- `∀ 
  --   (`∀ {κ = κ} 
  --       (((` (S Z) ▹ₙ η-norm (` Z)) ≲ (weakenₖNF (weakenₖNF ρ))) ⇒ 
  --         (⌊ ne (` (S Z)) ⌋ `→ 
  --           (weakenₖNF (weakenₖNF φ) ·' η-norm (` Z)))))
-- 

AnaT' : NormalType Δ R[ κ ] → NormalType Δ (κ `→ ★) → NormalType Δ ★ → NormalType Δ ★
AnaT' {κ = κ} ρ φ τ = ⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))
-- `∀ (`∀ {κ = κ} (((` (S Z) ▹ₙ η-norm (` Z)) ≲ (weakenₖNF (weakenₖNF ρ))) ⇒ (⌊ η-norm (` (S Z)) ⌋ `→ (weakenₖNF (weakenₖNF φ) ·' η-norm (` Z)) `→ weakenₖNF (weakenₖNF τ))))

