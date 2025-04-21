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
-- Lemmas

↻-·-⇓ : ∀ (F : Type Δ (κ₁ `→ κ₂)) (τ : Type Δ κ₁) → 
          ⇓ (F · τ) ≡ ⇓ F ·' ⇓ τ 
↻-·-⇓ F τ = {!!}

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
⇓Term (_·[_] {τ₂ = τ'} M τ) = conv {! !} (⇓Term M ·[ ⇓ τ ])
⇓Term (In F M) = In (⇓ F) (conv (↻-·-⇓ F (μ F)) (⇓Term M))
⇓Term (Out F M) = conv (sym (↻-·-⇓ F (μ F))) (Out (⇓ F) (⇓Term M))
⇓Term (`ƛ M) = `ƛ (⇓Term M)
⇓Term (M ·⟨ x ⟩) = (⇓Term M) ·⟨ {!!} ⟩
⇓Term (# ℓ) = # (⇓ ℓ)
⇓Term (l Π▹ M) = (⇓Term l) Π▹ ⇓Term M
⇓Term (M Π/ l) = ⇓Term M Π/ ⇓Term l
⇓Term (prj M x) = prj (⇓Term M) {!!}
⇓Term ((M ⊹ N) x) = {!!}
⇓Term (M Σ▹ N) = ⇓Term M Σ▹ ⇓Term N
⇓Term (M Σ/ N) = ⇓Term M Σ/ ⇓Term N
⇓Term (inj M e) = inj (⇓Term M) {!!}
⇓Term ((M ▿ N) e) = {!!}
⇓Term (convert eq M) = conv (completeness eq) (⇓Term M)
