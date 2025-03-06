{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax

--------------------------------------------------------------------------------
-- Renaming semantic types.

renKripke : Renamingₖ Δ₁ Δ₂ → KripkeFunction Δ₁ κ₁ κ₂ → KripkeFunction Δ₂ κ₁ κ₂
renKripke {Δ₁} ρ F {Δ₂} = λ ρ' → F (ρ' ∘ ρ) 

renSem : Renamingₖ Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ

renSem {κ = ★} ρ τ = renₖNF ρ τ
renSem {κ = L} ρ τ = renₖNF ρ τ
renSem {κ = κ `→ κ₁} ρ F = renKripke ρ F
renSem {κ = R[ κ ]} ρ (just (left x)) = just (left (renₖNE ρ x))
renSem {κ = R[ κ ]} ρ (just (right (l , τ))) = just (right (renₖNF ρ l , renSem ρ τ))
renSem {κ = R[ κ ]} ρ nothing = nothing

--------------------------------------------------------------------------------
-- Weakening

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem {Δ} {κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ

--------------------------------------------------------------------------------
-- Functor laws for renaming as a functorial action

renSem-id : ∀ (V : SemType Δ κ) → renSem id V ≡ V 
renSem-id {κ = ★} V = renₖNF-id V
renSem-id {κ = L} V = renₖNF-id V
renSem-id {κ = κ `→ κ₁} F = refl
renSem-id {κ = R[ κ ]} (just (left x)) = cong (just ∘ left) (renₖNE-id x) -- renₖNE-id x
renSem-id {κ = R[ κ ]} (just (right (l , τ))) = cong (just ∘ right) (cong₂ _,_ (renₖNF-id l) (renSem-id τ)) -- renₖNE-id x
renSem-id {κ = R[ κ ]} nothing = refl

renSem-comp : ∀ (ρ₁ : Renamingₖ Δ₁ Δ₂) (ρ₂ : Renamingₖ Δ₂ Δ₃) (V : SemType Δ₁ κ) → 
             (renSem (ρ₂ ∘ ρ₁) V) ≡ (renSem ρ₂ (renSem ρ₁ V))
renSem-comp {κ = ★} ρ₁ ρ₂ V = renₖNF-comp _ _ _
renSem-comp {κ = L} ρ₁ ρ₂ V = renₖNF-comp _ _ _
renSem-comp {κ = κ `→ κ₁} ρ₁ ρ₂ F = refl
renSem-comp {κ = R[ κ ]} ρ₁ ρ₂ (just (left x)) = cong (just ∘ left) (renₖNE-comp _ _ _)
renSem-comp {κ = R[ κ ]} ρ₁ ρ₂ (just (right (l , τ))) = cong (just ∘ right) (cong₂ _,_ (renₖNF-comp _ _ _) (renSem-comp _ _ _))
renSem-comp {κ = R[ κ ]} ρ₁ ρ₂ nothing = refl

