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
η-expand {κ₁ = κ₁} {κ₂ = κ₂} f  with ground? κ₁ | ground? κ₂ 
... | yes p  | yes q = `λ (ne (weakenₖNE f · ne (` Z) {ground = fromWitness p}) {fromWitness q})
η-expand {κ₁ = κ₁ `→ κ₂} {κ₂ = κ₃} f | no p | yes q = 
    `λ (ne (weakenₖNE f · (η-expand (` Z))) {fromWitness q})
η-expand {κ₁ = κ₁} {κ₂ = κ₂ `→ κ₃} f | yes p | no q = 
    `λ (η-expand (weakenₖNE f · (ne (` Z) {ground = fromWitness p})))
η-expand {κ₁ = κ₁ `→ κ₂} {κ₂ = κ₃ `→ κ₄} f | no p | no q = 
    `λ (η-expand (weakenₖNE f · (η-expand (` Z))))
η-expand {κ₁ = κ₁} {κ₂ = ★} x | yes p | no q = ⊥-elim (q tt)
η-expand {κ₁ = κ₁} {κ₂ = L} x | yes p | no q = ⊥-elim (q tt)
η-expand {κ₁ = κ₁} {κ₂ = R[ κ₂ ]} x | yes p | no q = ⊥-elim (q tt)
η-expand {κ₁ = ★} {κ₂ = κ₂} x | no p | yes q = ⊥-elim (p tt)
η-expand {κ₁ = L} {κ₂ = κ₂} x | no p | yes q = ⊥-elim (p tt)
η-expand {κ₁ = R[ κ₁ ]} {κ₂ = κ₂} x | no p | yes q = ⊥-elim (p tt)
η-expand {κ₁ = ★} {κ₂ = ★} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = ★} {κ₂ = L} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = ★} {κ₂ = κ₂ `→ κ₃} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = ★} {κ₂ = R[ κ₂ ]} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = L} {κ₂ = ★} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = L} {κ₂ = L} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = L} {κ₂ = κ₂ `→ κ₃} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = L} {κ₂ = R[ κ₂ ]} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = κ₁ `→ κ₂} {κ₂ = ★} x | no p | no q = ⊥-elim (q tt)
η-expand {κ₁ = κ₁ `→ κ₂} {κ₂ = L} x | no p | no q = ⊥-elim (q tt)
η-expand {κ₁ = κ₁ `→ κ₂} {κ₂ = R[ κ₃ ]} x | no p | no q = ⊥-elim (q tt)
η-expand {κ₁ = R[ κ₁ ]} {κ₂ = ★} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = R[ κ₁ ]} {κ₂ = L} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = R[ κ₁ ]} {κ₂ = κ₂ `→ κ₃} x | no p | no q = ⊥-elim (p tt)
η-expand {κ₁ = R[ κ₁ ]} {κ₂ = R[ κ₂ ]} x | no p | no q = ⊥-elim (p tt)

η-norm : NeutralType Δ κ → NormalType Δ κ 
η-norm {κ = ★} x = ne x
η-norm {κ = L} x = ne x
η-norm {κ = κ `→ κ₁} x = η-expand x
η-norm {κ = R[ κ ]} x = ne x

