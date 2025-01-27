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

renKripke : Renaming Δ₁ Δ₂ → KripkeFunction Δ₁ κ₁ κ₂ → KripkeFunction Δ₂ κ₁ κ₂
renKripke {Δ₁} ρ F {Δ₂} = λ ρ' → F (ρ' ∘ ρ) 

renSem : Renaming Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renSem-R : Renaming Δ₁ Δ₂ → SemType Δ₁ R[ κ ] → SemType Δ₂ R[ κ ]

renSem {κ = ★} ρ τ = ren ρ τ
renSem {κ = L} ρ τ = ren ρ τ
renSem {κ = κ `→ κ₁} ρ (left τ) = left (renNE ρ τ)
renSem {κ = κ `→ κ₁} ρ (right F) = right (renKripke ρ F)

renSem {κ = R[ κ ]} ρ τ = renSem-R ρ τ
renSem-R {κ = ★} ρ τ = ren ρ τ 
renSem-R {κ = L} ρ τ = ren ρ τ 
renSem-R {κ = κ `→ κ₁} ρ (left τ) = left (renNE ρ τ)
renSem-R {κ = κ `→ κ₁} ρ (right (l , left x)) = right (ren ρ l , left (renNE ρ x))
renSem-R {κ = κ `→ κ₁} ρ (right (l , right F)) = right (ren ρ l , right (renKripke ρ F))
renSem-R {κ = R[ κ ]} ρ (left τ) = left (renNE ρ τ) 
renSem-R {κ = R[ κ ]} ρ (right (l , τ)) = right (ren ρ l , renSem ρ τ)

-- --------------------------------------------------------------------------------
-- -- Weakening

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem {Δ} {κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ

--------------------------------------------------------------------------------
-- Functor laws for renaming as a functorial action

renSem-id : ∀ (V : SemType Δ κ) → renSem id V ≡ V 
renSem-id V = {!   !}


renSem-comp : ∀ (V : SemType Δ₁ κ) (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
             (renSem (ρ₂ ∘ ρ₁) V) ≡ (renSem ρ₂ (renSem ρ₁ V))
renSem-comp {κ = κ} V ρ₁ ρ₂ = {!   !}
 
