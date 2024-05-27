{-# OPTIONS --safe #-}
module ROmega.Terms.Admissible where

open import Preludes.Level

open import ROmega.Kinds
open import ROmega.Types
open import ROmega.Terms.Syntax
open import ROmega.Types.Substitution
open import ROmega.Equivalence.Syntax
open import ROmega.Entailment.Syntax
open import ROmega.GVars.Kinds

--------------------------------------------------------------------------------
-- admissable rules.

prj▹ : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {Ł : Type Δ (L ℓ)} 
       {τ : Type Δ (★ ℓκ)} {ρ : Type Δ R[ ★ ℓκ ]} →          
        Term Δ Φ Γ (Π ρ) → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
        ------------------------------------------
        Term Δ Φ Γ (Ł ▹ τ)
prj▹ r e = Π⁻¹ (prj r e)          

inj▹ : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ} {Ł : Type Δ (L ℓ)} 
       {τ : Type Δ (★ ℓκ)} {ρ : Type Δ R[ ★ ℓκ ]} →
        Term Δ Φ Γ (Ł ▹ τ) → Ent Δ Φ ((Ł R▹ τ) ≲ ρ) →
        ---------------------------------------------
        Term Δ Φ Γ (Σ ρ)
inj▹ s e = inj (Σ s) e

u : {Γ : Env Δ ℓΓ} {Φ : PEnv Δ ℓΦ}  → 
    Term Δ Φ Γ (U {ℓ = ℓ})
u = lab (lab "unit")
  
