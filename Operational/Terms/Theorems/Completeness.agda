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
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming

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

⇓Var : ∀ {Γ} {τ : Type Δ ★} → Var Γ τ → NormalVar (⇓Ctx Γ) (⇓ τ)
⇓Var Z = Z
⇓Var (S x) = S (⇓Var x)
⇓Var (K {τ = τ} x) = 
  convVar 
    (trans 
      (↻-renSem-eval S τ idEnv-≋) 
      (trans (idext (↻-ren-reflect S ∘ `) τ) (sym (↻-renₖ-eval S τ idEnv-≋)))) 
    (K (⇓Var x))
⇓Var (P x) = P (⇓Var x)

⇓Term : ∀ {Γ : Context Δ} {τ : Type Δ ★} → Term Γ τ → NormalTerm (⇓Ctx Γ) (⇓ τ)
⇓Term (` x) = ` (⇓Var x)
⇓Term (`λ M) = `λ (⇓Term M)
⇓Term (M · N) = ⇓Term M · ⇓Term N
⇓Term (Λ {τ = τ} M) = Λ 
  (conv 
    (idext 
      (λ { Z → reflect-≋ refl ; (S x) → sym-≋ (↻-ren-reflect S (` x)) }) τ) 
    (⇓Term M))
⇓Term (M ·[ τ ]) = conv {!!} (⇓Term M ·[ ⇓ τ ])
⇓Term (In F M) = {!!}
⇓Term (Out F M) = {!!}
⇓Term (`ƛ M) = `ƛ (⇓Term M)
⇓Term (M ·⟨ x ⟩) = {!!}
⇓Term (# ℓ) = # (⇓ ℓ)
⇓Term (l Π▹ M) = (⇓Term l) Π▹ ⇓Term M
⇓Term (M Π/ M₁) = ⇓Term M Π/ ⇓Term M₁
⇓Term (prj M x) = {!!}
⇓Term ((M ⊹ M₁) x) = {!!}
⇓Term (M Σ▹ M₁) = ⇓Term M Σ▹ ⇓Term M₁
⇓Term (M Σ/ M₁) = ⇓Term M Σ/ ⇓Term M₁
⇓Term (inj M x) = ⇓Term M
⇓Term ((M ▿ M₁) x) = {!!}
⇓Term (convert eq M) = conv (completeness eq) (⇓Term M)
