{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Stability where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal
open import Rome.Operational.Types.Normal.Properties.Postulates
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Completeness

--------------------------------------------------------------------------------
-- - stability : ⇑ is right-inverse to ⇓ 
--     or, ⇓ is a split-monomorphism/section.
-- - stabilityNE : reflect ∘ ⇑NE  = reflectNE
--   or, round trips from neutral semantic terms to semantic terms are preserved.

stability   : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ
stabilityNE : ∀ (τ : NeutralType Δ κ) → reflect (⇑NE τ) (idEnv {Δ}) ≡ reflectNE τ

stabilityNE {κ = ★} (` x) = refl
stabilityNE {κ = L} (` x) = refl
stabilityNE {κ = κ `→ κ₁} (` x) = refl
stabilityNE {κ = R[ κ ]} (` x) = refl
stabilityNE {Δ} {★} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = refl
stabilityNE {Δ} {L} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = refl
stabilityNE {Δ} {κ `→ κ₁} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = refl
stabilityNE {Δ} {R[ κ ]} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = refl    
stabilityNE (_▹_ {★} l τ) rewrite stability l | stability τ | ren-id l = refl
stabilityNE (_▹_ {L} l τ) rewrite stability l | stability τ | ren-id l = refl
stabilityNE (_▹_ {κ `→ κ₁} l τ) rewrite stability l | stability τ | ren-id l = {! !}
-- Bad!!!!
stabilityNE (_▹_ {R[ κ ]} l τ) rewrite stability l | stability τ | ren-id l = {! !}
stabilityNE {κ = ★} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = L} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = κ `→ κ₁} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ ★ ]} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ L ]} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ κ `→ κ₁ ]} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ R[ κ ] ]} (Π τ) rewrite stabilityNE τ = refl
stabilityNE {κ = ★} (Σ τ) rewrite stabilityNE τ = refl
stabilityNE {κ = L} (Σ τ) rewrite stabilityNE τ = refl
stabilityNE {κ = κ `→ κ₁} (Σ τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ ★ ]} (Σ τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ L ]} (Σ τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ κ `→ κ₁ ]} (Σ τ) rewrite stabilityNE τ = refl
stabilityNE {κ = R[ R[ κ ] ]} (Σ τ) rewrite stabilityNE τ = refl

stability Unit = refl
stability {κ = ★} (ne x) = stabilityNE x
stability {κ = L} (ne x) = stabilityNE x
stability {κ = κ `→ κ₁} (ne x) = cong reify (stabilityNE x)
stability {κ = R[ ★ ]} (ne x) = stabilityNE x
stability {κ = R[ L ]} (ne x) = stabilityNE x
stability {κ = R[ κ `→ κ₁ ]} (ne x) = {! !}
stability {κ = R[ R[ κ ] ]} (ne x) = {! !}
stability {κ = κ₁ `→ κ₂} (`λ τ) = 
  cong `λ 
    (trans 
        (reify-≋ 
            (idext (λ { Z → reflectNE-≋ refl
                          ; (S α) → ↻-renSem-reflectNE S (` α)}) (⇑ τ)))
        (stability τ))
stability (`∀ κ τ) = 
    cong (`∀ κ) 
        ((trans 
            (reify-≋ 
                (idext (λ { Z → reflectNE-≋ refl 
                              ; (S α) → ↻-renSem-reflectNE S (` α)}) (⇑ τ)))
            (stability τ)))
stability (μ (ne x)) rewrite stabilityNE x = refl
stability (μ (`λ τ)) rewrite stability (`λ τ) = cong μ refl
stability (μ (Π▹ l τ)) = {!   !}
stability (μ (Σ▹ l τ)) = {!   !}
-- More problems!!!
-- We have goal:
--  ne (Π (l ▹ Unit)) ≡ Π▹ l Unit
-- Noncanonicity!!! Just get fucking rid of Π▹!!!
stability {κ = κ} (Π▹ l Unit) rewrite ren-id (reflect (⇑ l) (λ x → reflectNE (` x))) | stability l  = {!   !}
stability {κ = κ} (Π▹ l (ne x)) = {!   !}
stability {κ = κ} (Π▹ l (`λ τ)) = {!   !}
stability {κ = κ} (Π▹ l (τ `→ τ₁)) = {!   !}
stability {κ = κ} (Π▹ l (`∀ κ₁ τ)) = {!   !}
stability {κ = κ} (Π▹ l (μ τ)) = {!   !}
stability {κ = κ} (Π▹ l (lab x)) = {!   !}
stability {κ = κ} (Π▹ l ⌊ τ ⌋) = {!   !}
stability {κ = κ} (Π▹ l (Π▹ τ τ₁)) = {!   !}
stability {κ = κ} (Π▹ l (Σ▹ τ τ₁)) = {!   !}
stability (Σ▹ l τ) = {!  !}
stability (lab x) = refl
stability ⌊ τ ⌋ rewrite stability τ = refl
stability (τ₁ `→ τ₂) rewrite stability τ₁ | stability τ₂ = refl

--------------------------------------------------------------------------------
-- idempotency

idempotency : ∀ (τ : Types.Type Δ κ) → (⇑ (⇓ (⇑ (⇓ τ)))) ≡ ⇑ (⇓ τ)
idempotency τ rewrite stability (⇓ τ) = refl

--------------------------------------------------------------------------------
-- surjectivity
--   

surjectivity : ∀ (τ : NormalType Δ κ) → ∃[ υ ] (⇓ υ ≡ τ)
surjectivity τ = ( ⇑ τ , stability τ ) 

 