module SFFP.Types.Semantic.Renaming where

open import SFFP.Prelude
open import SFFP.Kinds.Syntax
open import SFFP.Kinds.GVars

open import SFFP.Types.Syntax
open import SFFP.Types.Renaming using (↑ ; Renaming)
open import SFFP.Types.Properties

open import SFFP.Types.Normal.Syntax
open import SFFP.Types.Normal.Renaming

open import SFFP.Types.Semantic.Syntax

--------------------------------------------------------------------------------
-- Renaming semantic types.

renSem : Renaming Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renSem {κ = ★} ρ τ = ren ρ τ
renSem {κ = κ `→ κ₁} ρ (left τ) = left (renNE ρ τ)
renSem {κ = κ `→ κ₁} ρ (right F) = right λ ρ' → F (ρ' ∘ ρ)

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem = renSem S
