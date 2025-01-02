{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Theorems.Completeness where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

import Rome.Operational.Types as Types
import Rome.Operational.Types.Properties as TypeProps
open import Rome.Operational.Types.Renaming using (Renaming ; _≈_ ; lift)

open import Rome.Operational.Types.Normal
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- Completeness of type normalization


-- Completeness relation on semantic types
_≋_ : SemType Δ κ → SemType Δ κ → Set
SemExtensionality : ∀ {Δ₁} {κ₁} {κ₂} (F G : SemFunction Δ₁ κ₁ κ₂) → Set
Uniform : SemFunction Δ κ₁ κ₂ → Set

_≋_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = κ₁ `→ κ₂} (left x) (left y) = x ≡ y
_≋_ {κ = κ₁ `→ κ₂} (left x) (right y) = ⊥
_≋_ {κ = κ₁ `→ κ₂} (right y) (left x) = ⊥
_≋_ {Δ₁} {κ = κ₁ `→ κ₂} (right ⟨ cs₁ , F ⟩) (right ⟨ cs₂ , G ⟩) = 
  cs₁ ≡ cs₂ × Uniform F × Uniform G × SemExtensionality {Δ₁} F G
 
_≋_ {κ = R[ ★ ]} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = R[ L ]} τ₁ τ₂ = τ₁ ≡ τ₂
_≋_ {κ = R[ κ `→ κ₁ ]} (left x) (left y) = x ≡ y
_≋_ {κ = R[ κ `→ κ₁ ]} (left x) (right y) = ⊥
_≋_ {κ = R[ κ `→ κ₁ ]} (right x) (left y) = ⊥
_≋_ {κ = R[ κ `→ κ₁ ]} (right ⟨ l₁ , F ⟩) (right ⟨ l₂ , G ⟩) = {!!}
_≋_ {κ = R[ R[ κ ] ]} τ₁ τ₂ = {!!}

SemExtensionality {Δ₁} {κ₁} {κ₂} F G = 
  ∀ {Δ₂} (ρ : Renaming Δ₁ Δ₂) {V₁ V₂ : SemType Δ₂ κ₁} → 
  V₁ ≋ V₂ → F ρ V₁ ≋ G ρ V₂

Uniform F = {!!}

--------------------------------------------------------------------------------
-- Need:
-- - idext
-- - reflectCR
-- - ren⊧-reflect
-- - reifyCR
