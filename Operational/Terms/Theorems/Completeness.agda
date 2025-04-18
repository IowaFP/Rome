module Rome.Operational.Terms.Theorems.Completeness where 

open import Rome.Operational.Prelude 

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Syntax

open import Rome.Operational.Containment

--------------------------------------------------------------------------------
-- Completeness of type checking

⇓Ctx : Context Δ → NormalContext Δ 
⇓Ctx ∅ = ∅
⇓Ctx (Γ , x) = ⇓Ctx Γ , ⇓ x
⇓Ctx (Γ ,, κ) = ⇓Ctx Γ ,, κ
⇓Ctx (Γ ,,, π) = ⇓Ctx Γ ,,, ⇓Pred π

--------------------------------------------------------------------------------
-- 

⇓Term : ∀ {Γ : Context Δ} {τ : Type Δ ★} → Term Γ τ → NormalTerm (⇓Ctx Γ) (⇓ τ)
⇓Term (` x) = {!!}
⇓Term (`λ M) = {!!}
⇓Term (M · M₁) = {!!}
⇓Term (Λ M) = {!!}
⇓Term (M ·[ τ₁ ]) = {!!}
⇓Term (In F M) = {!!}
⇓Term (Out F M) = {!!}
⇓Term (`ƛ M) = {!!}
⇓Term (M ·⟨ x ⟩) = {!!}
⇓Term (# ℓ) = # (⇓ ℓ)
⇓Term (M Π▹ M₁) = {!!}
⇓Term (M Π/ M₁) = {!!}
⇓Term (prj M x) = {!!}
⇓Term ((M ⊹ M₁) x) = {!!}
⇓Term (M Σ▹ M₁) = {!!}
⇓Term (M Σ/ M₁) = {!!}
⇓Term (inj M x) = {!!}
⇓Term ((M ▿ M₁) x) = {!!}
⇓Term (convert eq M) = conv (completeness eq) (⇓Term M)
