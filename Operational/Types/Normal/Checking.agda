{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Normal.Checking where 

open import Rome.Operational.Prelude 

open import Rome.Operational.Kinds.Syntax 
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Kinds.Decidability

open import Rome.Operational.Types.Syntax

open import Rome.Operational.Types.Normal.Syntax

open import Rome.Operational.Types.Semantic.NBE 


import Rome.Operational.Types.Pre.Syntax as Pre 
open Pre.Type
open Pre.Pred

open import Rome.Operational.Types.Checking 

open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness


checksNF? : ∀ (κ : Kind) (Δ : KEnv) (τ : Pre.Type Δ) → Dec (Σ[ τ' ∈ NormalType Δ κ ] (forget (⇑ τ') ≡ τ))
checksNF? κ Δ τ with checks? κ Δ τ
... | yes (τ' , eq) = yes (⇓ τ' , trans (cong forget {!   !}) eq)
... | no p  = {! c  !}

