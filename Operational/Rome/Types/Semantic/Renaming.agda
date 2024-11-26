{-# OPTIONS --allow-unsolved-metas #-}
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

renC : Renaming Δ₁ Δ₂ → Congruence Δ₁ κ → Congruence Δ₂ κ
renC ρ nil = nil
renC ρ (x ▹) = ren ρ x ▹
renC ρ (x R▹) = ren ρ x R▹
renC ρ Π     = Π
-- renC ρ Σ     = Σ
-- renC ρ R     = R

-- renCs : Renaming Δ₁ Δ₂ → Congruence Δ₁ → Congruences Δ₂
-- renCs ρ [] = []
-- renCs ρ (x ∷ xs) = renC ρ x ∷ renCs ρ xs

renSem : Renaming Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renSem-R : Renaming Δ₁ Δ₂ → SemType-R Δ₁ κ → SemType-R Δ₂ κ
renSem {κ = ★} ρ τ = ren ρ τ
renSem {κ = L} ρ τ = ren ρ τ
renSem {κ = R[ κ' ]} ρ τ = {!!} -- ren ρ τ -- renSem-R {κ = κ'} {0} ρ τ 
renSem {κ = κ `→ κ₁} ρ (left τ) = left (renNE ρ τ)
renSem {κ = κ `→ κ₁} ρ (right ⟨ w , F ⟩) = right ⟨ renC ρ w , (λ ρ' → F (ρ' ∘ ρ)) ⟩

renSem-R {κ = ★} ρ τ = ren ρ τ
renSem-R {κ = L} ρ τ = ren ρ τ
renSem-R {κ = κ₁ `→ κ₂} ρ (left τ) = left (renNE ρ τ)
renSem-R {κ = κ₁ `→ κ₂} ρ (right ⟨ w , F ⟩) = right ⟨ renC ρ w , (λ ρ' → F (ρ' ∘ ρ)) ⟩
renSem-R {κ = R[ κ ]} ρ τ = {!!}

--------------------------------------------------------------------------------
-- Weakening

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem {Δ} {κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ
