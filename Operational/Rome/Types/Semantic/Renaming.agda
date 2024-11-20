module Operational.Rome.Types.Semantic.Renaming where

open import Operational.Rome.Prelude
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

open import Operational.Rome.Types.Syntax
open import Operational.Rome.Types.Renaming using (↑ ; Renaming)
open import Operational.Rome.Types.Properties

open import Operational.Rome.Types.Normal.Syntax
open import Operational.Rome.Types.Normal.Renaming

open import Operational.Rome.Types.Semantic.Syntax

--------------------------------------------------------------------------------
-- Renaming semantic types.

renSem : Renaming Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renSem {κ = ★} ρ τ = ren ρ τ
renSem {κ = L} ρ τ = ren ρ τ
renSem {κ = R[ κ' ]} ρ τ = ren ρ τ
renSem {κ = κ `→ κ₁} ρ (left τ) = left (renNE ρ τ)
renSem {κ = κ `→ κ₁} ρ (right F) = right λ ρ' → F (ρ' ∘ ρ)

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem = renSem S
