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

open import Rome.Operational.Types.Equivalence
open import Rome.Operational.Types.Properties.Equivalence

open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Terms.Normal.Syntax
open import Rome.Operational.Terms.Syntax

open import Rome.Operational.Terms.Theorems.Soundness

open import Rome.Operational.Containment

--------------------------------------------------------------------------------
-- Completeness of type checking

⇓Ctx : Context Δ → NormalContext Δ 
⇓Ctx ∅ = ∅
⇓Ctx (Γ , x) = ⇓Ctx Γ , ⇓ x
⇓Ctx (Γ ,, κ) = ⇓Ctx Γ ,, κ
⇓Ctx (Γ ,,, π) = ⇓Ctx Γ ,,, ⇓Pred π

--------------------------------------------------------------------------------
-- Normalization commutes over application

↻-·-⇓ : ∀ (F : Type Δ (κ₁ `→ κ₂)) (τ : Type Δ κ₁) → 
          ⇓ (F · τ) ≡ ⇓ F ·' ⇓ τ 
↻-·-⇓ F τ = trans 
  (completeness 
    (eq-· (soundness F) (soundness τ))) 
  (sym (stability-·' (⇓ F) (⇓ τ)))

↻-<$>-⇓ : ∀ (F : Type Δ (κ₁ `→ κ₂)) (ρ : Type Δ R[ κ₁ ]) → 
          ⇓ (F <$> ρ) ≡ ⇓ F <$>' ⇓ ρ 
↻-<$>-⇓ F ρ = trans 
  (completeness 
    (eq-<$> (soundness F) (soundness ρ))) 
  (sym (stability-<$> (⇓ F) (⇓ ρ)))

--------------------------------------------------------------------------------
-- SynT respects type equivalence

SynT-cong : ∀ {ρ₁ ρ₂ : Type Δ R[ κ ]} {φ₁ φ₂ : Type Δ (κ `→ ★)} → ρ₁ ≡t ρ₂ → φ₁ ≡t φ₂ → 
            SynT ρ₁ φ₁ ≡t SynT ρ₂ φ₂
SynT-cong eq₁ eq₂ = 
  eq-∀ (eq-∀ (eq-⇒ 
    (eq-refl eq-≲ (renₖ-≡t S (renₖ-≡t S eq₁))) 
    (eq-→ 
      eq-refl 
      (eq-· 
        (renₖ-≡t S (renₖ-≡t S eq₂)) 
        eq-refl))))

AnaT-cong : ∀ {ρ₁ ρ₂ : Type Δ R[ κ ]} {φ₁ φ₂ : Type Δ (κ `→ ★)} {τ₁ τ₂ : Type Δ ★} → 
              ρ₁ ≡t ρ₂ → φ₁ ≡t φ₂ → τ₁ ≡t τ₂ → 
              AnaT ρ₁ φ₁ τ₁ ≡t AnaT ρ₂ φ₂ τ₂
AnaT-cong eq₁ eq₂ eq₃ = 
  eq-∀ (eq-∀ (eq-⇒ 
    (eq-refl eq-≲ (renₖ-≡t S (renₖ-≡t S eq₁))) 
    (eq-→ 
      eq-refl 
      (eq-→ 
        (eq-· (renₖ-≡t S (renₖ-≡t S eq₂)) eq-refl) 
        (renₖ-≡t S (renₖ-≡t S eq₃))))))

--------------------------------------------------------------------------------
-- Variables

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

⇓PVar : ∀ {Γ} {π : Pred Type Δ R[ κ ]} → PVar Γ π → NormalPVar (⇓Ctx Γ) (⇓Pred π)
⇓PVar Z = Z
⇓PVar (S x) = S (⇓PVar x)
⇓PVar (T x) = T (⇓PVar x)
⇓PVar (K {π = π} x) = 
  convPVar 
    (trans 
      (↻-renSem-eval-pred S π idEnv-≋) 
      (trans (idext-pred (↻-ren-reflect S ∘ `) π) (sym (↻-renₖ-eval-pred S π idEnv-≋)))) 
    (K (⇓PVar x))

--------------------------------------------------------------------------------
-- Completeness of terms and entailments

⇓Term : ∀ {Γ : Context Δ} {τ : Type Δ ★} → Term Γ τ → NormalTerm (⇓Ctx Γ) (⇓ τ)
⇓Ent : ∀ {Γ : Context Δ} {π : Pred Type Δ R[ κ ]} → Ent Γ π → NormalEnt (⇓Ctx Γ) (⇓Pred π)

⇓Ent (n-var x) = n-var (⇓PVar x)
⇓Ent (n-≲ i) = n-≲ (⊆-cong ⇓ ⇓Row (⇓Row-isMap idEnv) i)
⇓Ent (n-· i₁ i₂ i₃) = n-· 
  (⊆-cong ⇓ ⇓Row (⇓Row-isMap idEnv) i₁) 
  (⊆-cong ⇓ ⇓Row (⇓Row-isMap idEnv) i₂) 
  (⊆-cong-or ⇓ ⇓Row (⇓Row-isMap idEnv) i₃)
⇓Ent n-refl = n-refl
⇓Ent (n-trans n₁ n₂) = n-trans (⇓Ent n₁) (⇓Ent n₂)
⇓Ent (n-·≲L n) = n-·≲L (⇓Ent n)
⇓Ent (n-·≲R n) = n-·≲R (⇓Ent n)
⇓Ent n-ε-R = n-ε-R
⇓Ent n-ε-L = n-ε-L
⇓Ent (n-≲lift {ρ₁ = ρ₁} {ρ₂} {F} n) = 
  n-≲lift 
    {F = ⇓ F} 
    (⇓Ent n) 
    (↻-<$>-⇓ F ρ₁) 
    (↻-<$>-⇓ F ρ₂)
⇓Ent (n-·lift {ρ₁ = ρ₁} {ρ₂} {ρ₃} {F} n) = 
  n-·lift 
    {F = ⇓ F} 
    (⇓Ent n) 
    (↻-<$>-⇓ F ρ₁) 
    (↻-<$>-⇓ F ρ₂) 
    (↻-<$>-⇓ F ρ₃)
⇓Ent {π = π₂} (convert {π₁ = π₁} eq n) = convEnt (fundC-pred idEnv-≋ eq) (⇓Ent n)

⇓Term (` x) = ` (⇓Var x)
⇓Term (`λ M) = `λ (⇓Term M)
⇓Term (M · N) = ⇓Term M · ⇓Term N
⇓Term (Λ {τ = τ} M) = Λ 
  (conv 
    (idext 
      (λ { Z → reflect-≋ refl ; (S x) → sym-≋ (↻-ren-reflect S (` x)) }) τ) 
    (⇓Term M))
⇓Term (_·[_] {τ₂ = τ'} M τ) = 
  conv 
    (sym (↻-β-⇓ τ' τ)) 
    (_·[_] {τ₂ = ⇓ τ'} 
      (conv (trans 
        (completeness 
          (eq-∀ (soundness τ'))) 
        (stability  (`∀ (⇓ τ')))) 
      (⇓Term M)) (⇓ τ))
⇓Term (In F M) = In (⇓ F) (conv (↻-·-⇓ F (μ F)) (⇓Term M))
⇓Term (Out F M) = conv (sym (↻-·-⇓ F (μ F))) (Out (⇓ F) (⇓Term M))
⇓Term (`ƛ M) = `ƛ (⇓Term M)
⇓Term (M ·⟨ n ⟩) = (⇓Term M) ·⟨ ⇓Ent n  ⟩
⇓Term (# ℓ) = # (⇓ ℓ)
⇓Term (l Π▹ M) = (⇓Term l) Π▹ ⇓Term M
⇓Term (M Π/ l) = ⇓Term M Π/ ⇓Term l
⇓Term (prj M n) = prj (⇓Term M) (⇓Ent n)
⇓Term ((M ⊹ N) n) = (⇓Term M ⊹ ⇓Term N) (⇓Ent n)
⇓Term (M Σ▹ N) = ⇓Term M Σ▹ ⇓Term N
⇓Term (M Σ/ N) = ⇓Term M Σ/ ⇓Term N
⇓Term (inj M n) = inj (⇓Term M) (⇓Ent n)
⇓Term ((M ▿ N) n) = (⇓Term M ▿ ⇓Term N) (⇓Ent n)
⇓Term (convert eq M) = conv (completeness eq) (⇓Term M)
⇓Term (fix M) = fix (⇓Term M)
⇓Term (syn ρ φ M) = 
  conv 
    (completeness {τ₁ = Π · (⇑ (⇓ φ) <$> ⇑ (⇓ ρ))} {τ₂ = Π · (φ <$> ρ)}
       (eq-· eq-refl (eq-<$> (eq-sym (soundness φ)) (eq-sym (soundness ρ))))) 
  (syn (⇓ ρ) (⇓ φ) (conv 
    (completeness     
      (SynT-cong (soundness ρ) (soundness φ))) 
  (⇓Term M)))
⇓Term (ana ρ φ τ M) = 
  conv 
    (completeness {τ₁ = (Σ · (⇑ (⇓ φ) <$> ⇑ (⇓ ρ))) `→ τ} {τ₂ = (Σ · (φ <$> ρ)) `→ τ} 
    (eq-→ (eq-· eq-refl (eq-<$> (eq-sym (soundness φ)) (eq-sym (soundness ρ)))) eq-refl)) 
  (ana (⇓ ρ) (⇓ φ) (⇓ τ) (conv 
    (completeness (AnaT-cong (soundness ρ) (soundness φ) (soundness τ))) (⇓Term M)))

--------------------------------------------------------------------------------
-- CompletenessT 

