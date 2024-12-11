module Rome.Operational.Kinds.Stratification where

open import Agda.Primitive

open import Rome.Operational.Kinds.Syntax
import Rome.Kinds.Syntax as Stratified


stratify-kind : Kind → (ℓ : Level) → Stratified.Kind ℓ
stratify-kind ★ ℓ = Stratified.★ ℓ
stratify-kind L ℓ = Stratified.L ℓ
stratify-kind (κ₁ `→ κ₂) ℓ = (stratify-kind κ₁ ℓ) Stratified.`→ (stratify-kind κ₂ ℓ)
stratify-kind R[ κ ] ℓ = Stratified.R[ (stratify-kind κ ℓ) ]
