{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Normal.Properties.Substitution where


open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types
open import Rome.Operational.Types.Properties.Substitution
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution

open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness

open import Rome.Operational.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- Neutral types are equivalent to their η-normalizations

η-norm-≡t : ∀ (τ : NeutralType Δ κ) → ⇑ (η-norm τ) ≡t ⇑NE τ 
η-norm-≡t {κ = ★} τ = eq-refl
η-norm-≡t {κ = L} τ = eq-refl
η-norm-≡t {κ = κ `→ κ₁} τ = 
  eq-trans 
    (eq-λ (η-norm-≡t (renₖNE S τ · reify (reflect (` Z))))) 
  (eq-trans 
    (eq-λ 
      (eq-· 
        (inst (↻-ren-⇑NE S τ)) 
        (η-norm-≡t (` Z))))
    (eq-sym eq-η))
η-norm-≡t {κ = R[ κ ]} τ = eq-refl 

--------------------------------------------------------------------------------
-- Substitution is a relative monad

subₖNF-id          : ∀ (τ : NormalType Δ κ) → subₖNF idSubst τ ≡ τ
subₖNF-id τ = 
  trans 
    (reify-≋ (↻-subₖ-eval (⇑ τ) idEnv-≋ (⇑ ∘ idSubst)))
  (trans 
    (reify-≋ 
      (idext {η₁ = λ x → eval (⇑ (idSubst x)) idEnv} {η₂ = idEnv} 
        (λ { x → fundC {τ₁ = ⇑ (η-norm (` x))} {τ₂ = ` x} idEnv-≋ (η-norm-≡t (` x)) }) (⇑ τ)))
    (stability τ))

subₖNF-var   : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂)(x : KVar Δ₁ κ) {g : True (ground? κ)} → 
              subₖNF σ (ne (` x) {g}) ≡ σ x
subₖNF-var σ x {g} = stability (σ x)   


--------------------------------------------------------------------------------
--


  -- renaming commutes with beta-reduction.
↻-renₖNF-β      : (ρ : Renamingₖ Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ₁) κ₂) (τ₂ : NormalType Δ₁ κ₁) → 
                renₖNF ρ (τ₁ βₖNF[ τ₂ ]) ≡ (renₖNF (liftₖ ρ) τ₁) βₖNF[ (renₖNF ρ τ₂) ]
↻-renₖNF-β ρ τ₁ τ₂ = {!  !}

↻-renₖNE-app      : (ρ : Renamingₖ Δ₁ Δ₂) (τ₁ : NeutralType Δ₁ (κ₁ `→ κ₂)) (τ₂ : NormalType Δ₁ κ₁) → 
                  renₖNE ρ (τ₁ · τ₂) ≡ (renₖNE ρ τ₁) · (renₖNF ρ τ₂)
↻-renₖNE-app ρ τ₁ τ₂ = {!  !}

-- weakening commutes with substitution.
↻-weaken-sub : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ : NormalType Δ₁ κ) {κ'} → 
                  weakenₖNF {κ₁ = κ'} (subₖNF σ τ) ≡ subₖNF (liftsₖNF σ) (weakenₖNF τ)
↻-weaken-sub σ τ = {!  !}

↻-subₖNF-lifts      : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ : NormalType (Δ₁ ,, κ) ★) → 
                    subₖNF (liftsₖNF σ) τ 
                  ≡ 
                    eval (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ)) (lifte idEnv)
↻-subₖNF-lifts σ τ = {!  !}

↻-subₖNF-β      : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                    subₖNF σ (τ₁ βₖNF[ τ₂ ])
                  ≡ 
                    eval (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ₁)) (lifte idEnv)
                    βₖNF[ subₖNF σ τ₂ ]
↻-subₖNF-β σ τ₁ τ₂ = {!  !}


-- Weakening followed by application of τ equals τ
weakenₖNF-β-id   : ∀ (τ : NormalType Δ ★) {τ₂ : NormalType Δ κ} → τ ≡ (weakenₖNF τ) βₖNF[ τ₂ ]
weakenₖNF-β-id τ {τ₂} = {!↻-weaken-sub  !}

cong-·' :  ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) 
             (f : NormalType Δ₁ (κ₁ `→ ★))
             (v : NormalType Δ₁ κ₁) → 
             subₖNF σ (f ·' v) ≡ subₖNF σ f ·' subₖNF σ v
cong-·' σ (`λ f) v = trans (↻-subₖNF-β σ f v) refl
 