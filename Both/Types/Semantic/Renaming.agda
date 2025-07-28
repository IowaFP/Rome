{-# OPTIONS --safe #-}
module Rome.Both.Types.Semantic.Renaming where

open import Rome.Both.Prelude
open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Renaming

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Properties.Renaming

open import Rome.Both.Types.Semantic.Syntax

open import Data.List.Properties using (map-id ; map-cong; map-∘)
import Data.List.Relation.Unary.All as All
open All using (All)

--------------------------------------------------------------------------------
-- Renaming semantic types.

renKripke : Renamingₖ Δ₁ Δ₂ → KripkeFunction Δ₁ κ₁ κ₂ → KripkeFunction Δ₂ κ₁ κ₂
renKripke {Δ₁} ρ F {Δ₂} = λ ρ' → F (ρ' ∘ ρ) 

renSem : Renamingₖ Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renRow : Renamingₖ Δ₁ Δ₂ → 
         Row (SemType Δ₁ κ) → 
         Row (SemType Δ₂ κ)

orderedRenRow : ∀ {n} {P : Fin n → Label × SemType Δ₁ κ} → (r : Renamingₖ Δ₁ Δ₂) → 
                OrderedRow' n P → OrderedRow' n (λ i → (P i .fst) , renSem r (P i .snd))

nrRenSem :  ∀ (r : Renamingₖ Δ₁ Δ₂) → (ρ : RowType Δ₁ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
             NotRow ρ → NotRow (renSem r ρ)
nrRenSem' : ∀ (r : Renamingₖ Δ₁ Δ₂) → (ρ₂ ρ₁ : RowType Δ₁ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
             NotRow ρ₂ or NotRow ρ₁ → NotRow (renSem r ρ₂) or NotRow (renSem r ρ₁)

renSem {κ = ★} r τ = renₖNF r τ
renSem {κ = L} r τ = renₖNF r τ
renSem {κ = κ `→ κ₁} r F = renKripke r F
renSem {κ = R[ κ ]} r (φ <$> x) = (λ r' → φ (r' ∘ r)) <$> (renₖNE r x)
renSem {κ = R[ κ ]} r (l ▹ τ) = (renₖNE r l) ▹ renSem r τ
renSem {κ = R[ κ ]} r (row (n , P) q) = row (n , ( map₂ (renSem r) ∘ P)) (orderedRenRow r q)
renSem {κ = R[ κ ]} r ((ρ₂ ─ ρ₁) {nr}) = (renSem r ρ₂ ─ renSem r ρ₁) {nr = nrRenSem' r ρ₂ ρ₁ nr}

nrRenSem' r ρ₂ ρ₁ (left x) = left (nrRenSem r ρ₂ x)
nrRenSem' r ρ₂ ρ₁ (right y) = right (nrRenSem r ρ₁ y)

nrRenSem r (x ▹ x₁) nr = tt
nrRenSem r (ρ ─ ρ₁) nr = tt
nrRenSem r (φ <$> ρ) nr = tt

orderedRenRow {n = zero} {P} r o = tt
orderedRenRow {n = suc zero} {P} r o = tt
orderedRenRow {n = suc (suc n)} {P} r (l₁<l₂ , o) =  l₁<l₂  , (orderedRenRow {n = suc n} {P ∘ fsuc} r o)

renRow φ (n , P) = n , map₂ (renSem φ) ∘ P 

--------------------------------------------------------------------------------
-- Weakening

weakenSem : SemType Δ κ₁ → SemType (Δ ,, κ₂) κ₁
weakenSem {Δ} {κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ
