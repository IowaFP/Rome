module Rome.RelatingSemantics.Types.Substitution where 

open import Rome.RelatingSemantics.Prelude
open import Rome.RelatingSemantics.Kinds.Syntax
open import Rome.RelatingSemantics.Kinds.GVars
open import Rome.RelatingSemantics.Types.Syntax
open import Rome.RelatingSemantics.Types.Renaming

--------------------------------------------------------------------------------
-- η-normalization of neutral types

η-expand : NeutralType Δ κ → NormalType Δ κ 
η-expand {κ = ★} (` α) = ne (` α)
η-expand {κ = L} (` α) = ne (` α)
η-expand {κ = κ₁ `→ κ₂} (` α) = {!!}
η-expand {κ = R[ κ ]} (` α) = {!!}
η-expand (n · τ) = {!!}

--------------------------------------------------------------------------------
-- Normality preserving type substitution

Substitutionₖ : KEnv ι₁ → KEnv ι₂ → Set
Substitutionₖ Δ₁ Δ₂ = ∀ {ι}{κ : Kind ι} → TVar Δ₁ κ → NormalType Δ₂ κ

-- lifting a substitution over binders.
liftsₖ :  Substitutionₖ Δ₁ Δ₂ → Substitutionₖ (Δ₁ ,, κ) (Δ₂ ,, κ)
liftsₖ σ Z = η-expand (` Z)
liftsₖ σ (S x) = weakenₖNF (σ x)
