module Rome.Operational.Terms.Examples.Uninhabitable? where

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Terms.Syntax

--------------------------------------------------------------------------------
-- 

ℓ ℓ₁ ℓ₂ ℓ₃ : Type Δ L
ℓ  = lab "l"
ℓ₁ = lab "l1"
ℓ₂ = lab "l2"
ℓ₃ = lab "l3"

shit₁ : Type Δ ★
shit₁ = Π (Π (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

shit  : ∀ {Γ} → Term Γ shit₁
shit = {!!}
