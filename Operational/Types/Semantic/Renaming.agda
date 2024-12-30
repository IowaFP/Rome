{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (lift ; Renaming)
open import Rome.Operational.Types.Properties

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming

open import Rome.Operational.Types.Semantic.Syntax

--------------------------------------------------------------------------------
-- Renaming semantic types.

renC : Renaming Δ₁ Δ₂ → Congruence Δ₁ → Congruence Δ₂
renC ρ (Π x) = Π (ren ρ x)
renC ρ (Σ x) = Σ (ren ρ x)

renCs : Renaming Δ₁ Δ₂ → List (Congruence Δ₁) → List (Congruence Δ₂)
renCs ρ = map (renC ρ)

renSem : Renaming Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renSem {κ = ★} ρ τ = ren ρ τ
renSem {κ = L} ρ τ = ren ρ τ
renSem {κ = κ `→ κ₁} ρ (left τ) = left (renNE ρ τ)
renSem {κ = κ `→ κ₁} ρ (right ⟨ [] , F ⟩) = right ⟨ [] , (λ ρ' → F (ρ' ∘ ρ)) ⟩
renSem {κ = κ `→ κ₁} ρ (right ⟨ cs , F ⟩) = right ⟨ renCs ρ cs , ((λ ρ' → F (ρ' ∘ ρ))) ⟩

renSem {κ = R[ κ' ]} ρ τ = {!!} -- ren ρ τ -- renSem-R {κ = κ'} {0} ρ τ 

--------------------------------------------------------------------------------
-- Weakening

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem {Δ} {κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ
