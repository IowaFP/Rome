module Rome.Both.Terms.Theorems.Soundness where 

open import Rome.Both.Prelude 

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.SynAna
open import Rome.Both.Types.Renaming
open import Rome.Both.Types.Substitution
open import Rome.Both.Types.Equivalence.Relation

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Substitution
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Properties.Substitution
open import Rome.Both.Types.Normal.Properties.Renaming

open import Rome.Both.Types.Theorems.Consistency
open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Stability

open import Rome.Both.Types.Equivalence.Relation
open import Rome.Both.Types.Equivalence.Properties

open import Rome.Both.Types.Semantic.NBE
open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.Renaming

open import Rome.Both.Terms.Normal.Syntax
open import Rome.Both.Terms.Syntax

open import Rome.Both.Terms.Theorems.Consistency

open import Rome.Both.Containment

--------------------------------------------------------------------------------
-- Soundness of type checking

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
  (soundness 
    (eq-· (consistency F) (consistency τ))) 
  (sym (stability-·' (⇓ F) (⇓ τ)))

↻-<$>-⇓ : ∀ (F : Type Δ (κ₁ `→ κ₂)) (ρ : Type Δ R[ κ₁ ]) → 
          ⇓ (F <$> ρ) ≡ ⇓ F <$>' ⇓ ρ 
↻-<$>-⇓ F ρ = trans 
  (soundness 
    (eq-<$> (consistency F) (consistency ρ))) 
  (sym (stability-<$> (⇓ F) (⇓ ρ)))

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
-- Soundness of terms and entailments

⇓Term : ∀ {Γ : Context Δ} {τ : Type Δ ★} → Term Γ τ → NormalTerm (⇓Ctx Γ) (⇓ τ)
⇓Ent : ∀ {Γ : Context Δ} {π : Pred Type Δ R[ κ ]} → Ent Γ π → NormalEnt (⇓Ctx Γ) (⇓Pred π)

⇓Ent (n-var x) = n-var (⇓PVar x)
⇓Ent (n-incl i) = n-incl (⊆-cong ⇓ ⇓Row (⇓Row-isMap idEnv) i)
⇓Ent (n-plus i₁ i₂ i₃) = n-plus
  (⊆-cong ⇓ ⇓Row (⇓Row-isMap idEnv) i₁) 
  (⊆-cong ⇓ ⇓Row (⇓Row-isMap idEnv) i₂) 
  (⊆-cong-or ⇓ ⇓Row (⇓Row-isMap idEnv) i₃)
⇓Ent n-refl = n-refl
⇓Ent (_n-⨾_ n₁ n₂) = _n-⨾_ (⇓Ent n₁) (⇓Ent n₂)
⇓Ent (n-plusL≲ n) = n-plusL≲ (⇓Ent n)
⇓Ent (n-plusR≲ n) = n-plusR≲ (⇓Ent n)
⇓Ent n-emptyR = n-emptyR
⇓Ent n-emptyL = n-emptyL
⇓Ent (n-map≲ {ρ₁ = ρ₁} {ρ₂} {F} n) = 
  n-map≲ 
    {F = ⇓ F} 
    (⇓Ent n) 
    (↻-<$>-⇓ F ρ₁) 
    (↻-<$>-⇓ F ρ₂)
⇓Ent (n-map· {ρ₁ = ρ₁} {ρ₂} {ρ₃} {F} n) = 
  n-map· 
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
        (soundness 
          (eq-∀ (consistency τ'))) 
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
⇓Term (convert eq M) = conv (soundness eq) (⇓Term M)
⇓Term (fix M) = fix (⇓Term M)
⇓Term (syn ρ φ M) = 
  conv 
    (soundness {τ₁ = Π · (⇑ (⇓ φ) <$> ⇑ (⇓ ρ))} {τ₂ = Π · (φ <$> ρ)}
       (eq-· eq-refl (eq-<$> (eq-sym (consistency φ)) (eq-sym (consistency ρ))))) 
  (syn (⇓ ρ) (⇓ φ) (conv 
    (soundness     
      (SynT-cong-≡t (consistency ρ) (consistency φ))) 
  (⇓Term M)))
⇓Term (ana ρ φ τ M) = 
  conv 
    (soundness {τ₁ = (Σ · (⇑ (⇓ φ) <$> ⇑ (⇓ ρ))) `→ τ} {τ₂ = (Σ · (φ <$> ρ)) `→ τ} 
    (eq-→ (eq-· eq-refl (eq-<$> (eq-sym (consistency φ)) (eq-sym (consistency ρ)))) eq-refl)) 
  (ana (⇓ ρ) (⇓ φ) (⇓ τ) (conv 
    (soundness (AnaT-cong-≡t (consistency ρ) (consistency φ) (consistency τ))) (⇓Term M)))
⇓Term (comp M n) = comp (⇓Term M) (⇓Ent n)

--------------------------------------------------------------------------------
-- Repeated conversion of normalTerms to-then-from Terms can have indices stabilized

stability-Ctx : ∀ (Γ : NormalContext Δ) → Γ ≡ ⇓Ctx (⇑Ctx Γ)
stability-Ctx ∅ = refl
stability-Ctx (Γ , x) = cong₂ _,_ (stability-Ctx Γ) (sym (stability x))
stability-Ctx (Γ ,, κ) rewrite sym (stability-Ctx Γ) = refl
stability-Ctx (Γ ,,, x) rewrite sym (stability-Ctx Γ) | (stabilityPred x) = refl

stabilize : ∀ {Γ} {τ : NormalType Δ ★} (M : NormalTerm (⇓Ctx (⇑Ctx Γ)) (⇓ (⇑ τ))) → NormalTerm Γ τ 
stabilize {Γ = Γ} {τ} M rewrite sym (stability-Ctx Γ) | stability τ = M 
