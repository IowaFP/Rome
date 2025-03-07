{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Normal.Properties.Eta-expansion where


open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types
open import Rome.Operational.Types.Properties.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Eta-expansion

open import Rome.Operational.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- Eta expansion commutes with renaming

--------------------------------------------------------------------------------
-- 

reify-reflect-η : ∀ (x : NeutralType Δ κ) → 
                  reify (reflect x) ≡ η-norm x
reify-reflect-η {κ = ★} x = refl
reify-reflect-η {κ = L} x = refl
reify-reflect-η {κ = ★ `→ ★} x = refl
reify-reflect-η {κ = ★ `→ L} x = refl
reify-reflect-η {κ = ★ `→ κ₂ `→ κ₃} x = cong `λ (reify-reflect-η (renₖNE S x · ne (` Z) tt))
reify-reflect-η {κ = ★ `→ R[ κ₂ ]} x = refl
reify-reflect-η {κ = L `→ ★} x = refl
reify-reflect-η {κ = L `→ L} x = refl
reify-reflect-η {κ = L `→ κ₂ `→ κ₃} x = cong `λ (reify-reflect-η (renₖNE S x · ne (` Z) tt))
reify-reflect-η {κ = L `→ R[ κ₂ ]} x = refl
reify-reflect-η {κ = (κ₁ `→ κ₂) `→ ★} x = {!   !}
reify-reflect-η {κ = (κ₁ `→ κ₂) `→ L} x = {!   !}
reify-reflect-η {κ = (κ₁ `→ κ₂) `→ κ₃ `→ κ₄} x = {!   !}
reify-reflect-η {κ = (κ₁ `→ κ₂) `→ R[ κ₃ ]} x = {!   !}
reify-reflect-η {κ = R[ κ₁ ] `→ ★} x = refl
reify-reflect-η {κ = R[ κ₁ ] `→ L} x = refl
reify-reflect-η {κ = R[ κ₁ ] `→ κ₂ `→ κ₃} x = cong `λ (reify-reflect-η (renₖNE S x · ne (` Z) tt))
reify-reflect-η {κ = R[ κ₁ ] `→ R[ κ₂ ]} x = refl
reify-reflect-η {κ = R[ κ ]} x = refl      

↻-ren-η-norm : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → (x : KVar Δ₁ κ) → renₖNF ρ (η-norm (` x)) ≡ (η-norm (` (ρ x)))
↻-ren-η-norm {κ = ★} ρ x = refl
↻-ren-η-norm {κ = L} ρ x = refl
↻-ren-η-norm {κ = κ₁ `→ κ₂} ρ x with arrow? κ₁ | arrow? κ₂
↻-ren-η-norm {Δ₂ = _} {(κ₁ `→ κ₂) `→ κ₃ `→ κ₄} ρ x | yes p | yes q = {!  !}
↻-ren-η-norm {Δ₂ = _} {κ₁ `→ κ₂ `→ κ₃} ρ x | no p | yes d = {!  !}
↻-ren-η-norm {Δ₂ = _} {(κ₁ `→ κ₃) `→ κ₂} ρ x | yes p | no d = {!  !}
... | no p     | no d  = refl
↻-ren-η-norm {κ = R[ κ ]} ρ x = refl
