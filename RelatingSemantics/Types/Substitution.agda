module Rome.RelatingSemantics.Types.Substitution where 

open import Rome.RelatingSemantics.Prelude
open import Rome.RelatingSemantics.Kinds.Syntax
open import Rome.RelatingSemantics.Kinds.GVars
open import Rome.RelatingSemantics.Types.Syntax
open import Rome.RelatingSemantics.Types.Renaming

--------------------------------------------------------------------------------
-- η-normalization of neutral types

η-expand : NeutralType Δ κ → NormalType Δ κ 
η-expand {κ = ★} n = ne n
η-expand {κ = L} n = ne n
η-expand {κ = κ₁ `→ κ₂} n = `λ (η-expand ((weakenₖNE n) · (η-expand (` Z))))
η-expand {κ = R[ κ ]} n = (`λ (η-expand (` Z))) <$> n

--------------------------------------------------------------------------------
-- Normality preserving type substitution

SubstitutionₖNF : KEnv ι₁ → KEnv ι₂ → Set
SubstitutionₖNF Δ₁ Δ₂ = ∀ {ι}{κ : Kind ι} → TVar Δ₁ κ → NormalType Δ₂ κ

-- lifting a substitution over binders.
liftsₖNF :  SubstitutionₖNF Δ₁ Δ₂ → SubstitutionₖNF (Δ₁ ,, κ) (Δ₂ ,, κ)
liftsₖNF σ Z = η-expand (` Z)
liftsₖNF σ (S x) = weakenₖNF (σ x)

extendₖNF : SubstitutionₖNF Δ₁ Δ₂ → NormalType Δ₂ κ → SubstitutionₖNF (Δ₁ ,, κ) Δ₂
extendₖNF σ τ Z = τ
extendₖNF σ τ (S x) = σ x


-- Identity substitution (s.t. substₖNF idSubst x = (idSubst x))
idSubst : SubstitutionₖNF Δ Δ
idSubst = η-expand ∘ `


subₖNF : SubstitutionₖNF Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
subₖNE : SubstitutionₖNF Δ₁ Δ₂ → NeutralType Δ₁ κ → NormalType Δ₂ κ

subₖNE σ (` α) = σ α 
subₖNE σ (n · τ) with subₖNE σ n 
... | `λ m = subₖNF (extendₖNF idSubst (subₖNF σ τ)) m
-- subₖNE σ x β subₖNF σ τ
--   where
--     _β_ : NormalType Δ₂ (κ₁ `→ κ₂) → NormalType Δ₂ κ₁ → NormalType Δ₂ κ₂ 
--     `λ φ β τ = subₖNF (extendₖNF idSubst τ) φ

subₖNF σ (ne n) = subₖNE σ n
subₖNF σ (τ <$> x) = {!!}
subₖNF σ (`λ τ) = {!!}
subₖNF σ (τ `→ τ₁) = {!!}
subₖNF σ (`∀ τ) = {!!}
subₖNF σ (π ⇒ τ) = {!!}
subₖNF σ (⦅ ρ ⦆ oρ) = {!!}
subₖNF σ (lab l) = {!!}
subₖNF σ ⌊ τ ⌋ = {!!}
subₖNF σ (Π τ) = {!!}
subₖNF σ (Σ τ) = {!!}
subₖNF σ (τ ─ τ₁) = {!!}
subₖNF σ (l ▹ₙ τ) = {!!}
