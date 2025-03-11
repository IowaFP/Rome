{-# OPTIONS --allow-unsolved-metas #-}

module Rome.Operational.Terms.Renaming where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Normal.Properties.Substitution

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Renaming

open import Rome.Operational.Terms.Syntax
open import Rome.Operational.Terms.GVars

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Stability

private
  variable
    ρ : Renamingₖ Δ₁ Δ₂
    τ τ₁ τ₂ : NormalType Δ κ

--------------------------------------------------------------------------------
-- Renamings are functions from term variables to term variables
-- and from evidence variables to evidence variables

Renaming : ∀ Γ₁ Γ₂ → Renamingₖ Δ₁ Δ₂ → Set
Renaming Γ₁ Γ₂ ρ = 
  (∀ {τ : NormalType _ ★} → Var Γ₁ τ → Var Γ₂ (renₖNF ρ τ))
  ×
  (∀ {κ} {π : NormalPred _ R[ κ ]} → PVar Γ₁ π → PVar Γ₂ (renPredₖNF ρ π))

renType : ∀ {Γ₁ Γ₂} {ρ : Renamingₖ Δ₁ Δ₂} → Renaming Γ₁ Γ₂ ρ → NormalType Δ₁ κ → NormalType Δ₂ κ
renType {ρ = ρ} R = renₖNF ρ

renPred : ∀ {Γ₁ Γ₂} {ρ : Renamingₖ Δ₁ Δ₂} → Renaming Γ₁ Γ₂ ρ → NormalPred Δ₁ R[ κ ] → NormalPred Δ₂ R[ κ ]
renPred {ρ = ρ} R = renPredₖNF ρ

--------------------------------------------------------------------------------
-- Lifting of renamings

lift : Renaming Γ₁ Γ₂ ρ → {τ : NormalType Δ₁ ★} → Renaming (Γ₁ , τ) (Γ₂ , renₖNF ρ τ) ρ
lift (r , p) = 
  (λ { Z → Z
     ; (S x) → S (r x) }) , 
   λ { (T x) → T (p x) }

liftPVar : Renaming Γ₁ Γ₂ ρ → {π : NormalPred Δ R[ κ ]} → Renaming (Γ₁ ,,, π) (Γ₂ ,,, renPredₖNF ρ π) ρ
liftPVar (r , p) = 
  (λ { (P x) → P (r x) }) , 
  λ { Z → Z
    ; (S x) → S (p x) }

liftKVar : Renaming Γ₁ Γ₂ ρ → Renaming (Γ₁ ,, κ) (Γ₂ ,, κ) (liftₖ ρ)
liftKVar {ρ = ρ} (r , p)  = 
  (λ { (K {τ = τ} x) → convVar (sym (↻-weakenₖNF-renₖNF ρ τ)) (K (r x)) }) , 
  (λ { (K {π = π} x) → convPVar (sym (↻-weakenPredₖNF-renPredₖNF ρ π)) (K (p x)) })

--------------------------------------------------------------------------------
-- Renaming terms

ren : ∀ {τ} (Ρ : Renaming Γ₁ Γ₂ ρ) → 
      Term Γ₁ τ →
      Term Γ₂ (renₖNF ρ τ)
renEnt : ∀ {π : NormalPred Δ R[ κ ]} (Ρ : Renaming Γ₁ Γ₂ ρ) → 
      Ent Γ₁ π →
      Ent Γ₂ (renPredₖNF ρ π)

--------------------------------------------------------------------------------
-- Useful lemma for commuting renaming over the lift entailment rules

↻-ren-⇓-<$> : ∀ (ρ : Renamingₖ Δ₁ Δ₂) → 
          (F : NormalType Δ₁ (κ₁ `→ κ₂))
          (ρ₁ : NormalType Δ₁ R[ κ₁ ]) → 
          ⇓ (⇑ (renₖNF ρ F) <$> ⇑ (renₖNF ρ ρ₁)) ≡  renₖNF ρ (⇓ (⇑ F <$> ⇑ ρ₁))
↻-ren-⇓-<$> ρ F ρ₁ = 
  subst 
    (λ x → (reify (⇈ (renₖNF ρ F) <$>V eval x idEnv)) ≡ renₖNF ρ (reify (⇈ F <$>V ⇈ ρ₁))) 
    (sym (↻-ren-⇑ ρ ρ₁))
    (subst 
      (λ x → reify ((λ {Δ} → eval x idEnv {Δ}) <$>V eval (renₖ ρ (⇑ ρ₁)) idEnv) ≡ renₖNF ρ (reify (⇈ F <$>V ⇈ ρ₁))) 
      (sym (↻-ren-⇑ ρ F)) 
      (trans 
        (reify-≋ 
          (trans-≋ (↻-renₖ-eval ρ (⇑ F <$> ⇑ ρ₁) idEnv-≋) 
          (trans-≋ 
            (idext (sym-≋ ∘ ↻-ren-reflect ρ ∘ `) (⇑ F <$> ⇑ ρ₁)) 
            (sym-≋ (↻-renSem-eval ρ (⇑ F <$> ⇑ ρ₁) idEnv-≋))))) 
        (sym (↻-ren-reify ρ 
          {V₁ = (⇈ F <$>V ⇈ ρ₁)} 
          {V₂ = (⇈ F <$>V ⇈ ρ₁)} 
          (fundC 
            {τ₁ = ⇑ F <$> ⇑ ρ₁} 
            {τ₂ = ⇑ F <$> ⇑ ρ₁} 
            idEnv-≋ 
            (eq-<$> 
              eq-refl 
              eq-refl))))))         

--------------------------------------------------------------------------------
-- Renaming definitions

ren (r , p) (` x) = ` (r x)
ren R (`λ M) = `λ (ren (lift R) M)
ren R (M · N) = (ren R M) · (ren R N)
ren R (Λ M) = Λ (ren (liftKVar R) M)
ren {ρ = ρ} R (_·[_] {τ₂ = τ₂} M τ) = conv (sym (↻-renₖNF-β ρ τ₂ τ)) ((ren R M) ·[ renₖNF ρ τ ])
ren {ρ = ρ} R (In F@(`λ τ) N) = 
  In 
    (renType R F) 
    (conv (↻-renₖNF-β  ρ τ (μ F)) 
      (ren R N))
ren R (In F@(ne x {()}) τ)
ren {ρ = ρ} R (Out F@(`λ τ) M) = 
  conv 
    (sym (↻-renₖNF-β ρ τ ((μ F)))) 
    (Out (renType R F) (ren R M))
ren R (Out F@(ne x {()}) τ)
ren R (# l) = # l
ren R (l Π▹ M) = (ren R l) Π▹ (ren R M)
ren R (M Π/ l) = ren R M Π/ ren R l
ren R (l Σ▹ M) = (ren R l) Σ▹ (ren R M)
ren R (M Σ/ l) = ren R M Σ/ ren R l
ren R (`ƛ τ) = `ƛ (ren (liftPVar R) τ)
ren R (τ ·⟨ e ⟩) = ren R τ ·⟨ renEnt R e ⟩

renEnt {ρ = ρ} {π} (r , p) (n-var x) = n-var (p x)
renEnt R n-refl = n-refl
renEnt R (n-trans e₁ e₂) = n-trans (renEnt R e₁) (renEnt R e₂)
renEnt R (n-·≲L e) = n-·≲L (renEnt R e)
renEnt R (n-·≲R e) = n-·≲R (renEnt R e)
renEnt R n-ε-R = n-ε-R
renEnt R n-ε-L = n-ε-L
renEnt {Γ₂ = Γ₂} {ρ = ρ} R (n-≲lift {ρ₁ = ρ₁} {ρ₂} {F} e) = 
  convEnt 
    (cong₂ _≲_ 
      (↻-ren-⇓-<$> ρ F ρ₁) 
      (↻-ren-⇓-<$> ρ F ρ₂))
    (n-≲lift {F = renₖNF ρ F} (renEnt R e))
renEnt {ρ = ρ} R (n-·lift {ρ₁ = ρ₁} {ρ₂} {ρ₃} {F} e) 
  rewrite 
    sym (↻-ren-⇓-<$> ρ F ρ₁)
  | sym (↻-ren-⇓-<$> ρ F ρ₂)
  | sym (↻-ren-⇓-<$> ρ F ρ₃) = n-·lift {F = renₖNF ρ F} (renEnt R e)
  

--------------------------------------------------------------------------------
-- Weakening is a special case of renaming (but not we must convert types)

weakenByType : Term Γ τ₁ → Term (Γ , τ₂) τ₁
weakenByType {τ₁ = τ₁} M = conv (renₖNF-id τ₁) (ren ((convVar (sym (renₖNF-id _))) ∘ S , convPVar (sym (renₖNF-id-pred _)) ∘ T) M)

weakenByKind : ∀ {τ : NormalType Δ ★} → Term Γ τ → Term (Γ ,, κ) (weakenₖNF τ)
weakenByKind = ren (K , K)

weakenByPred : ∀ {τ : NormalType Δ ★} {π : NormalPred Δ R[ κ ]} → Term Γ τ → Term (Γ ,,, π) τ
weakenByPred {Γ = Γ} {τ = τ} {π} M = conv (renₖNF-id τ) (ren ((convVar (sym (renₖNF-id _))) ∘ P , convPVar (sym (renₖNF-id-pred _)) ∘ S) M)


  