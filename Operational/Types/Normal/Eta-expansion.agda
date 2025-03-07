{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Normal.Eta-expansion where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming

--------------------------------------------------------------------------------
-- η-expansion

η-expand : NeutralType Δ (κ₁ `→ κ₂) → NormalType Δ (κ₁ `→ κ₂)
η-expand {κ₁ = κ₁} {κ₂ = κ₂} f with arrow? κ₁ | arrow? κ₂
... | no p | no q = `λ (ne (weakenₖNE f · ne (` Z) (fromWitness (¬Arrow→Ground p))) (fromWitness (¬Arrow→Ground q)))
η-expand {κ₁ = κ₁ `→ κ₂} {κ₂ = κ₃ `→ κ₄} f | yes p | yes q = 
  `λ (η-expand (weakenₖNE f · (η-expand (` Z))))
η-expand {κ₁ = κ₁} {κ₂ = κ₂ `→ κ₃} f | no p | yes q =
 `λ (η-expand (weakenₖNE f · (ne (` Z) (fromWitness (¬Arrow→Ground p)))))
η-expand {κ₁ = κ₁ `→ κ₃} {κ₂ = κ₂} f | yes p | no q = 
  `λ (ne (weakenₖNE f · (η-expand (` Z))) (fromWitness (¬Arrow→Ground q)))

η-norm : NeutralType Δ κ → NormalType Δ κ 
η-norm {κ = ★} x = ne x tt
η-norm {κ = L} x = ne x tt
η-norm {κ = κ `→ κ₁} x = η-expand x
η-norm {κ = R[ κ ]} x = ne x tt

