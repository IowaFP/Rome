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

-- ▵-stable : ∀ {l : NormalType Δ L} {τ : NeutralType Δ κ} → 
--            (l ▵ reflectNE τ) ≡ reflectNE (l ▹ τ)
-- ▵-stable {l = l} {τ} = {!!}

-- This is all fairly *not* trivial
stabilityNE {κ = ★} (` x) = refl
stabilityNE {κ = ★} (τ · x) = {!!}
stabilityNE {κ = ★} (Π τ) = {!!}
stabilityNE {κ = ★} (Σ τ) = {!!}
stabilityNE {κ = L} (` x) = refl
stabilityNE {κ = L} (τ · x) = {!!}
stabilityNE {κ = L} (Π τ) = {!!}
stabilityNE {κ = L} (Σ τ) = {!!}
stabilityNE {κ = κ₁ `→ κ₂} (` x) = refl
stabilityNE {κ = κ₁ `→ κ₂} (τ · x) = {!!}
stabilityNE {κ = κ₁ `→ κ₂} (Π τ) = {!!}
stabilityNE {κ = κ₁ `→ κ₂} (Σ τ) = {!!}
stabilityNE {κ = R[ ★ ]} (` x) = refl
stabilityNE {κ = R[ ★ ]} (τ · x) = {!!}
stabilityNE {κ = R[ ★ ]} (x ▹ τ) rewrite stability x | stability τ | ren-id x = refl
stabilityNE {κ = R[ ★ ]} (Π τ) = {!!}
stabilityNE {κ = R[ ★ ]} (Σ τ) = {!!}
stabilityNE {κ = R[ L ]} (` x) = refl
stabilityNE {κ = R[ L ]} (τ · x) = {!!}
stabilityNE {κ = R[ L ]} (x ▹ τ) = {!!}
stabilityNE {κ = R[ L ]} (Π τ) = {!!}
stabilityNE {κ = R[ L ]} (Σ τ) = {!!}
stabilityNE {κ = R[ κ₁ `→ κ₂ ]} (` x) = refl
stabilityNE {κ = R[ κ₁ `→ κ₂ ]} (τ · x) = {!!}
stabilityNE {κ = R[ κ₁ `→ κ₂ ]} (x ▹ τ) = {!!}
stabilityNE {κ = R[ κ₁ `→ κ₂ ]} (Π τ) = {!!}
stabilityNE {κ = R[ κ₁ `→ κ₂ ]} (Σ τ) = {!!}
stabilityNE {κ = R[ R[ κ ] ]} τ = {!!}

stability Unit = refl
stability {κ = ★} (ne x) = stabilityNE x
stability {κ = L} (ne x) = stabilityNE x
stability {κ = κ `→ κ₁} (ne x) = cong reify (stabilityNE x)
stability {κ = R[ ★ ]} (ne x) = stabilityNE x
stability {κ = R[ L ]} (ne x) = stabilityNE x
stability {κ = R[ κ `→ κ₁ ]} (ne x) = {!!}
stability {κ = R[ R[ κ ] ]} (ne x) = {!!}
stability (`λ τ) = {!!}
stability (τ₁ `→ τ₂) = {!!}
stability (`∀ κ τ) = {!!}
stability (μ τ) = {!!}
stability (lab x) = refl
stability ⌊ τ ⌋ = {!!}
stability (Π▹ τ τ₁) = {!!}
stability (Σ▹ τ τ₁) = {!!}


--------------------------------------------------------------------------------
-- idempotency

idempotency : ∀ (τ : Types.Type Δ κ) → (⇑ (⇓ (⇑ (⇓ τ)))) ≡ ⇑ (⇓ τ)
idempotency τ rewrite stability (⇓ τ) = refl

--------------------------------------------------------------------------------
-- surjectivity
--   

surjectivity : ∀ (τ : NormalType Δ κ) → ∃[ υ ] (⇓ υ ≡ τ)
surjectivity τ = ⟨ ⇑ τ , stability τ ⟩ 

