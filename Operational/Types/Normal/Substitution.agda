{-# OPTIONS --safe #-}
module Rome.Operational.Types.Normal.Substitution where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.SynAna
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Equivalence.Relation

--------------------------------------------------------------------------------
-- Normality preserving Type Substitution

SubstitutionₖNF : KEnv → KEnv → Set
SubstitutionₖNF Δ₁ Δ₂ = ∀ {κ} → TVar Δ₁ κ → NormalType Δ₂ κ

-- lifting a substitution over binders.
liftsₖNF :  SubstitutionₖNF Δ₁ Δ₂ → SubstitutionₖNF (Δ₁ ,, κ) (Δ₂ ,, κ)
liftsₖNF {κ = κ} σ Z = η-norm (` Z)
liftsₖNF σ (S x) = weakenₖNF (σ x)

-- Identity substitution (s.t. substₖNF idSubst x = (idSubst x))
idSubst : SubstitutionₖNF Δ Δ
idSubst = η-norm ∘ `

-- Effectively: denormalize `n`, substitute, then normalize.
subₖNF : SubstitutionₖNF Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
subₖNF σ n = ⇓ (subₖ (⇑ ∘ σ) (⇑ n))

subₖNE : SubstitutionₖNF Δ₁ Δ₂ → NeutralType Δ₁ κ → NormalType Δ₂ κ
subₖNE σ n = ⇓ (subₖ (⇑ ∘ σ) (⇑NE n))

subRowₖNF : SubstitutionₖNF Δ₁ Δ₂ → SimpleRow NormalType Δ₁ R[ κ ] → SimpleRow NormalType Δ₂ R[ κ ]
subRowₖNF σ n = ⇓Row (subRowₖ (⇑ ∘ σ) (⇑Row n))

subPredₖNF : SubstitutionₖNF Δ₁ Δ₂ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]
subPredₖNF σ = mapPred (subₖNF σ)

-- Extend the substitution with a NormalType
extendₖNF : SubstitutionₖNF Δ₁ Δ₂ → (A : NormalType Δ₂ κ) → SubstitutionₖNF (Δ₁ ,, κ) Δ₂
extendₖNF σ A Z = A
extendₖNF σ A (S x) = σ x

-- Single variable substitution is a special case of simultaneous substitution.
_βₖNF[_] : NormalType (Δ ,, κ₁) κ₂ → NormalType Δ κ₁ → NormalType Δ κ₂
τ₁ βₖNF[ τ₂ ] = subₖNF (extendₖNF idSubst τ₂) τ₁

--------------------------------------------------------------------------------
-- Application *is* β-substitution due to canonicity of arrow kinded types

_·'_ : NormalType Δ (κ₁ `→ κ₂) → NormalType Δ κ₁ → NormalType Δ κ₂
`λ f ·' v = f βₖNF[ v ]

map-map₂-' : (ρ : SimpleRow NormalType Δ R[ κ₁ ]) (f : NormalType Δ (κ₁ `→ κ₂)) →
                NormalOrdered ρ → NormalOrdered ((map (map₂ (f ·'_)) ρ))
map-map₂-' [] f oρ = tt
map-map₂-' (x₁ ∷ []) f oρ = tt
map-map₂-' (x₁ ∷ x₂ ∷ ρ) f oρ = oρ .fst , map-map₂-' (x₂ ∷ ρ) f (oρ .snd)

--------------------------------------------------------------------------------
-- Normality-preserving <$> 

_<$>'_ : NormalType Δ (κ₁ `→ κ₂) → NormalType Δ R[ κ₁ ] → NormalType Δ R[ κ₂ ]
f <$>' ρ = ⇓ (⇑ f <$> ⇑ ρ)

--------------------------------------------------------------------------------
-- Normal forms of the bodies of Syn & Ana

SynT' : NormalType Δ R[ κ ] → NormalType Δ (κ `→ ★) → NormalType Δ ★
SynT' {κ = κ} ρ φ = ⇓ (SynT (⇑ ρ) (⇑ φ))


AnaT' : NormalType Δ R[ κ ] → NormalType Δ (κ `→ ★) → NormalType Δ ★ → NormalType Δ ★
AnaT' {κ = κ} ρ φ τ = ⇓ (AnaT (⇑ ρ) (⇑ φ) (⇑ τ))
