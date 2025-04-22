module Rome.Operational.Terms.Theorems.Soundness where 

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
-- We must recursively embed contexts

⇑Ctx : NormalContext Δ → Context Δ
⇑Ctx ∅ = ∅
⇑Ctx (Γ , τ) = ⇑Ctx Γ , ⇑ τ
⇑Ctx (Γ ,, κ) = ⇑Ctx Γ ,, κ
⇑Ctx (Γ ,,, π) = ⇑Ctx Γ ,,, ⇑Pred π

--------------------------------------------------------------------------------
-- Soundness of typing: Given a well-typed NormalTerm, we can produce a well-typed Term.


⇑Var : ∀ {Γ} {τ : NormalType Δ ★} → NormalVar Γ τ → Var (⇑Ctx Γ) (⇑ τ)
⇑Var Z = Z
⇑Var (S v) = S (⇑Var v)
⇑Var (K {τ = τ} v) = convVar' (sym (↻-ren-⇑ S τ) ) (K (⇑Var v))
⇑Var (P v) = P (⇑Var v)

⇑PVar : ∀ {Γ} {π : NormalPred Δ R[ κ ]} → NormalPVar Γ π → PVar (⇑Ctx Γ) (⇑Pred π)
⇑PVar Z = Z
⇑PVar (S v) = S (⇑PVar v)
⇑PVar (T v) = T (⇑PVar v)
⇑PVar (K v) = convPVar' (sym (↻-ren-⇑Pred S _)) (K (⇑PVar v))

⇑Ent : ∀ {Γ} {π : NormalPred Δ R[ κ ]} → NormalEnt Γ π → Ent (⇑Ctx Γ) (⇑Pred π)
⇑Ent (n-var x) = n-var (⇑PVar x)
⇑Ent (n-≲ i) = n-≲ (⊆-cong ⇑ ⇑Row ⇑Row-isMap i)
⇑Ent (n-· i₁ i₂ i₃) = n-· 
  (⊆-cong ⇑ ⇑Row ⇑Row-isMap i₁) 
  (⊆-cong ⇑ ⇑Row ⇑Row-isMap i₂) 
  (⊆-cong-or ⇑ ⇑Row ⇑Row-isMap i₃)

⇑Ent n-refl = n-refl
⇑Ent (n-trans e e₁) = n-trans (⇑Ent e) (⇑Ent e₁)
⇑Ent (n-·≲L e) = n-·≲L (⇑Ent e)
⇑Ent (n-·≲R e) = n-·≲R (⇑Ent e)
⇑Ent n-ε-R = n-ε-R
⇑Ent n-ε-L = n-ε-L
⇑Ent (n-≲lift {ρ₁ = ρ₁} {ρ₂} {F = F} e refl refl) = 
  convEnt'
     (cong₂ _≲_ 
       (cong ⇑ (sym (stability-<$> F ρ₁))) 
       (cong ⇑ (sym (stability-<$> F ρ₂)))) 
  (convert ((soundness (⇑ F <$> ⇑ ρ₁)) eq-≲ (soundness (⇑ F <$> ⇑ ρ₂))) (n-≲lift (⇑Ent e)))
⇑Ent (n-·lift {ρ₁ = ρ₁} {ρ₂} {ρ₃} {F} e refl refl refl) = 
  convEnt' 
    (cong₃ _·_~_ 
      (cong ⇑ (sym (stability-<$> F ρ₁))) 
      (cong ⇑ (sym (stability-<$> F ρ₂))) 
      (cong ⇑ (sym (stability-<$> F ρ₃)))) 
  (convert 
    ((soundness (⇑ F <$> ⇑ ρ₁)) eq-· (soundness (⇑ F <$> ⇑ ρ₂)) ~ (soundness (⇑ F <$> ⇑ ρ₃))) 
    (n-·lift (⇑Ent e)))

⇑Term : ∀ {Γ} {τ : NormalType Δ ★} → NormalTerm Γ τ → Term (⇑Ctx Γ) (⇑ τ)
⇑Term (` x) = ` (⇑Var x)
⇑Term (`λ M) = `λ (⇑Term M)
⇑Term (M · N) = ⇑Term M · ⇑Term N
⇑Term (Λ M) = Λ (⇑Term M) 
⇑Term (_·[_] {τ₂ = τ₂} M τ) = (convert (eq-sym (↻-β-⇑ τ₂ τ)) ((⇑Term M) ·[ (⇑ τ) ]))
⇑Term (In F M) = In (⇑ F) (convert (embed-≡t (stability-·' F (μ F))) (⇑Term M))
⇑Term (Out F M) = convert (eq-sym (embed-≡t (stability-·' F (μ F)))) (Out (⇑ F) (⇑Term M))
⇑Term (`ƛ M) = `ƛ (⇑Term M)
⇑Term (M ·⟨ e ⟩) = (⇑Term M) ·⟨ ⇑Ent e  ⟩
⇑Term (# l) = # (⇑ l)
⇑Term (l Π▹ M) = convert (eq-· eq-refl eq-labTy) (⇑Term l Π▹ ⇑Term M)
⇑Term (M Π/ l) = (convert (eq-· eq-refl (eq-sym eq-labTy)) (⇑Term M)) Π/ (⇑Term l)
⇑Term (prj M n) = prj (⇑Term M) (⇑Ent n)
⇑Term ((M ⊹ N) n) = ((⇑Term M) ⊹ (⇑Term N)) (⇑Ent n)
⇑Term (l Σ▹ M) = convert (eq-· eq-refl eq-labTy) (⇑Term l Σ▹ ⇑Term M)
⇑Term (M Σ/ l) = (convert (eq-· eq-refl (eq-sym eq-labTy)) (⇑Term M)) Σ/ (⇑Term l)
⇑Term (inj M n) = inj (⇑Term M) (⇑Ent n)
⇑Term ((M ▿ N) n) = ((⇑Term M) ▿ (⇑Term N)) (⇑Ent n)
⇑Term (fix M) = fix (⇑Term M)
⇑Term (syn ρ φ M) = 
  convert 
    (eq-· 
      eq-refl 
      (eq-trans 
        (soundness  (⇑ φ <$> ⇑ ρ)) 
        eq-refl)) 
  (syn (⇑ ρ) (⇑ φ) (convert (eq-sym (soundness (SynT (⇑ ρ) (⇑ φ)))) (⇑Term M)))
⇑Term (ana ρ φ τ M) = 
  convert 
    (eq-→ 
      (eq-· 
        eq-refl 
        (eq-trans (soundness (⇑ φ <$> ⇑ ρ)) eq-refl)) 
      eq-refl) 
  (ana (⇑ ρ) (⇑ φ) (⇑ τ) 
    (convert (eq-sym (soundness (AnaT (⇑ ρ) (⇑ φ) (⇑ τ)))) (⇑Term M)))


