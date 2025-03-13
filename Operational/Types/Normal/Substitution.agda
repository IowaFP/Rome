{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Normal.Substitution where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Equivalence

--------------------------------------------------------------------------------
-- Normality preserving Type Substitution

SubstitutionₖNF : KEnv → KEnv → Set
SubstitutionₖNF Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → NormalType Δ₂ κ

-- ↑ing a substitution over binders.
liftsₖNF :  SubstitutionₖNF Δ₁ Δ₂ → SubstitutionₖNF (Δ₁ ,, κ) (Δ₂ ,, κ)
liftsₖNF {κ = κ} σ Z = η-norm (` Z)
liftsₖNF σ (S x) = weakenₖNF (σ x)

-- Identity substitution (s.t. substₖNF idSubst x = (idSubst x))
idSubst : SubstitutionₖNF Δ Δ
idSubst = η-norm ∘ `

-- Effectively: denormalize `n`, substitute, then normalize.
subₖNF : SubstitutionₖNF Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
subₖNF σ n = ⇓ (subₖ (⇑ ∘ σ) (⇑ n))

subPredₖNF : SubstitutionₖNF Δ₁ Δ₂ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]
subPredₖNF σ = mapPred (subₖNF σ)

-- Extend the substitution with a NormalType
extendₖNF : SubstitutionₖNF Δ₁ Δ₂ → (A : NormalType Δ₂ κ) → SubstitutionₖNF (Δ₁ ,, κ) Δ₂
extendₖNF σ A Z = A
extendₖNF σ A (S x) = σ x

-- Single variable substitution is a special case of simultaneous substitution.
_βₖNF[_] : NormalType (Δ ,, κ₁) κ₂ → NormalType Δ κ₁ → NormalType Δ κ₂
τ₁ βₖNF[ τ₂ ] = subₖNF (extendₖNF idSubst τ₂) τ₁

-- Application *is* β-substitution due to canonicity of arrow kinded types
_·'_ : NormalType Δ (κ₁ `→ κ₂) → NormalType Δ κ₁ → NormalType Δ κ₂
`λ f ·' v = f βₖNF[ v ]

-- hold my beer 
_<$>'_ : NormalType Δ (κ₁ `→ κ₂) → NormalType Δ R[ κ₁ ] → NormalType Δ R[ κ₂ ]
f <$>' ne x = ne (f <$> x)
f <$>' ε = ε
f <$>' (l ▹ τ) = l ▹ (f ·' τ)


