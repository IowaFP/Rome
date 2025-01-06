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

-- This is all fairly *not* trivial
stabilityNE {κ = ★} (` x) = refl
stabilityNE {κ = L} (` x) = refl
stabilityNE {κ = κ `→ κ₁} (` x) = refl
stabilityNE {κ = R[ κ ]} (` x) = refl
stabilityNE (τ · x) = {! !}
stabilityNE (_▹_ {★} l τ) rewrite stability l | stability τ | ren-id l = refl
stabilityNE (_▹_ {L} l τ) rewrite stability l | stability τ | ren-id l = refl
stabilityNE (_▹_ {κ `→ κ₁} l τ) rewrite stability l | stability τ | ren-id l = {! !}
-- Bad!!!!
stabilityNE (_▹_ {R[ κ ]} l τ) rewrite stability l | stability τ | ren-id l = {! !}
stabilityNE (Π τ) = {! !}
stabilityNE (Σ τ) = {! !}

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
stability (μ (Π▹ τ τ₁)) = {!   !}
stability (μ (Σ▹ τ τ₁)) = {!   !}
stability (Π▹ τ τ₁) = {!  !}
stability (Σ▹ τ τ₁) = {!  !}
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

