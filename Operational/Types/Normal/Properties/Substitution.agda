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
open import Rome.Operational.Types.Semantic.Renaming

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
-- Substitution and normalization commute

↻-⇓-sub : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) → 
             (τ : Type Δ₁ κ) → ⇓ (subₖ (⇑ ∘ σ) τ) ≡ subₖNF σ (⇓ τ)
↻-⇓-sub σ τ = 
  trans 
    (reify-≋ (↻-subₖ-eval τ idEnv-≋ (⇑ ∘ σ))) 
    (sym (trans 
      (reify-≋ (↻-subₖ-eval (⇑ (⇓ τ)) idEnv-≋ (⇑ ∘ σ))) 
      (reify-≋ (fundC ((idext idEnv-≋) ∘ ⇑ ∘ σ) (eq-sym (soundness τ))))))

--------------------------------------------------------------------------------
-- Substitution respects the functor identity law

subₖNF-id          : ∀ (τ : NormalType Δ κ) → subₖNF idSubst τ ≡ τ
subₖNF-id τ = 
  trans 
    (reify-≋ (↻-subₖ-eval (⇑ τ) idEnv-≋ (⇑ ∘ idSubst)))
  (trans 
    (reify-≋ 
      (idext {η₁ = λ x → eval (⇑ (idSubst x)) idEnv} {η₂ = idEnv} 
        (λ { x → fundC {τ₁ = ⇑ (η-norm (` x))} {τ₂ = ` x} idEnv-≋ (η-norm-≡t (` x)) }) (⇑ τ)))
    (stability τ))

--------------------------------------------------------------------------------
-- Substitution over a variable substitutes the variable

subₖNF-var   : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂)(x : KVar Δ₁ κ) {g : True (ground? κ)} → 
              subₖNF σ (ne (` x) {g}) ≡ σ x
subₖNF-var σ x {g} = stability (σ x)

--------------------------------------------------------------------------------
-- Substitution respects the functor composition

subₖNF-comp :  ∀ (σ₁ : SubstitutionₖNF Δ₁ Δ₂) (σ₂ : SubstitutionₖNF Δ₂ Δ₃) → 
                (τ : NormalType Δ₁ κ) → subₖNF (subₖNF σ₂ ∘ σ₁) τ ≡ subₖNF σ₂ (subₖNF σ₁ τ)
subₖNF-comp σ₁ σ₂ τ = 
  trans 
    (trans 
      (trans 
        (reify-≋ 
          (↻-subₖ-eval (⇑ τ) idEnv-≋ (⇑ ∘ ⇓ ∘ subₖ (⇑ ∘ σ₂) ∘ ⇑ ∘ σ₁)))
        (trans 
          (reify-≋ 
            (idext (λ x → fundC idEnv-≋ (eq-sym (soundness (subₖ (⇑ ∘ σ₂) (⇑ (σ₁ x)))))) (⇑ τ)))
          (sym (reify-≋ (↻-subₖ-eval (⇑ τ) idEnv-≋ (subₖ (⇑ ∘ σ₂) ∘ ⇑ ∘ σ₁)))))) 
      (cong ⇓ (subₖ-comp (⇑ τ)))) 
    (↻-⇓-sub σ₂ (subₖ (⇑ ∘ σ₁) (⇑ τ)))

--------------------------------------------------------------------------------
-- Congruence of normality preserving substitution

subₖNF-cong : {σ₁ : SubstitutionₖNF Δ₁ Δ₂}{σ₂ : SubstitutionₖNF Δ₁ Δ₂} →
              (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (τ : NormalType Δ₁ κ) → subₖNF σ₁ τ ≡ subₖNF σ₂ τ
subₖNF-cong {σ₁ = σ₁} {σ₂} peq τ = 
  cong ⇓ (subₖ-cong (cong ⇑ ∘ peq) (⇑ τ))      

--------------------------------------------------------------------------------
-- Substitution commutes with renaming

↻-renₖNF-subₖNF : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (ρ : Renamingₖ Δ₂ Δ₃)
                    (τ : NormalType Δ₁ κ) → subₖNF (renₖNF ρ ∘ σ) τ ≡ renₖNF ρ (subₖNF σ τ)           
↻-renₖNF-subₖNF σ ρ τ = 
  trans 
    (reify-≋ 
      (trans-≋ 
        (trans-≋ 
          (↻-subₖ-eval (⇑ τ) idEnv-≋ (⇑ ∘ renₖNF ρ ∘ σ)) 
          (trans-≋ 
            (idext 
              (λ x → trans-≋ 
                (subst 
                  (λ y → eval (⇑ (renₖNF ρ (σ x)))  idEnv ≋ eval y idEnv) 
                  (↻-ren-⇑ ρ (σ x)) 
                  (idext idEnv-≋ (⇑ (renₖNF ρ (σ x)))))
                (trans-≋ 
                  (↻-renₖ-eval ρ  (⇑ (σ x)) idEnv-≋) 
                  (idext (sym-≋ ∘ ↻-ren-reflect ρ ∘ `) (⇑ (σ x))))) 
              (⇑ τ))
            ((sym-≋ (↻-subₖ-eval (⇑ τ) (ren-≋ ρ ∘ idEnv-≋) (⇑ ∘ σ)))))) 
        (sym-≋ (↻-renSem-eval ρ (subₖ (⇑ ∘ σ) (⇑ τ)) idEnv-≋))))
    (sym (↻-ren-reify ρ (idext idEnv-≋ (subₖ (⇑ ∘ σ) (⇑ τ)))))                  

↻-subₖNF-renₖNF : ∀ (ρ : Renamingₖ Δ₁ Δ₂)(σ : SubstitutionₖNF Δ₂ Δ₃)
                (τ : NormalType Δ₁ κ) → subₖNF (σ ∘ ρ) τ ≡ subₖNF σ (renₖNF ρ τ)           
↻-subₖNF-renₖNF ρ σ τ rewrite (sym (stability τ)) = 
  trans 
    (sym (↻-⇓-sub (σ ∘ ρ) (⇑ τ))) 
    (cong ⇓
       (trans 
        (↻-subₖ-renₖ {ρ = ρ} {σ = ⇑ ∘ σ} (⇑ τ)) 
        (cong 
          (subₖ (⇑ ∘ σ)) 
          (subst 
            (λ x → renₖ ρ (⇑ τ) ≡ ⇑ (renₖNF ρ x)) 
            (sym (stability τ)) 
            (sym (↻-ren-⇑ ρ τ))))))

--------------------------------------------------------------------------------
-- weakening commutes with substitution.

↻-weakenₖNF-subₖNF : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ : NormalType Δ₁ κ) {κ'} → 
                  weakenₖNF {κ₁ = κ'} (subₖNF σ τ) ≡ subₖNF (liftsₖNF σ) (weakenₖNF τ)
↻-weakenₖNF-subₖNF σ τ {κ} = trans 
  (sym (↻-renₖNF-subₖNF σ S τ)) 
  ((↻-subₖNF-renₖNF S (liftsₖNF σ) τ))


--------------------------------------------------------------------------------
-- Problem...
-- This simply isn't true with η-normalization. Will need to find another way to 
-- prove main theorem ↻-subₖNF-β; using ↻-subₖNF-β won't go through because 
-- the following identity doesn't hold:
--   ` Z ≡ ⇑ (reify (reflect (` Z)))
-- It only holds that
--  ` Z ≡t ⇑ (reify (reflect (` Z))).
-- Can I make proof go through using the type equivalence?

neededIdentity : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) {κ κ'} (τ : Type (Δ₁ ,, κ') κ) →
                    subₖ (liftsₖ (⇑ ∘ σ)) τ ≡ subₖ (⇑ ∘ liftsₖNF σ) τ -- subₖ (liftsₖ (⇑ ∘ σ)) τ ≡ subₖ (⇑ ∘ liftsₖNF ∘ σ) τ 
neededIdentity σ τ = subₖ-cong (λ { Z → {!   !}
                                  ; (S x) → {!   !} }) τ

neededIdentity' : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) {κ κ'} (τ : Type (Δ₁ ,, κ') κ) →
                    subₖ (liftsₖ (⇑ ∘ σ)) τ ≡t subₖ (⇑ ∘ liftsₖNF σ) τ -- subₖ (liftsₖ (⇑ ∘ σ)) τ ≡ subₖ (⇑ ∘ liftsₖNF ∘ σ) τ 
neededIdentity' σ τ = {!   !}
--------------------------------------------------------------------------------
--               

subₖ-cong-≡t⇑ :  ∀ {σ : SubstitutionₖNF Δ₁ Δ₂} {τ₁ τ₂ : Type Δ₁ κ} → 
                  τ₁ ≡t τ₂ → subₖ (⇑ ∘ σ) τ₁ ≡t subₖ (⇑ ∘ σ) τ₂
subₖ-cong-≡t⇑ {σ = σ} eq = subₖ-cong-≡t {σ = ⇑ ∘ σ} eq                  


subₖNF-cong-≡t : ∀ {σ : SubstitutionₖNF Δ₁ Δ₂} {τ₁ τ₂ : NormalType Δ₁ κ} → 
                ⇑ τ₁ ≡t ⇑ τ₂ → subₖNF σ τ₁ ≡ subₖNF σ τ₂
subₖNF-cong-≡t {σ = σ} {τ₁} {τ₂} eq = 
  reify-≋ 
    (fundC 
      {τ₁ = subₖ (⇑ ∘ σ) (⇑ τ₁)} 
      {τ₂ = subₖ (⇑ ∘ σ) (⇑ τ₂)} 
      idEnv-≋ (subₖ-cong-≡t⇑ {σ = σ} eq))


--------------------------------------------------------------------------------
-- Substituting commutes over β reduction (first statement)

↻-subₖNF-β'      : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                    subₖNF σ (τ₁ βₖNF[ τ₂ ])
                  ≡ 
                    (subₖNF (liftsₖNF σ) τ₁)
                    βₖNF[ subₖNF σ τ₂ ]
↻-subₖNF-β' σ τ₁ τ₂ =   trans 
    (sym (subₖNF-comp (extendₖNF (η-norm ∘ `) τ₂) σ τ₁)) 
    (trans 
      (subₖNF-cong 
        {σ₁ = subₖNF σ ∘ extendₖNF (η-norm ∘ `) τ₂} 
        {subₖNF (extendₖNF (η-norm ∘ `) (subₖNF σ τ₂)) ∘ liftsₖNF σ} 
        (λ { Z → sym {! subₖNF-var (extendₖNF (η-norm ∘ `) (subₖNF σ τ₂)) Z     !}
           ; (S x) → {!   !} })
        τ₁) 
      (subₖNF-comp (liftsₖNF σ) (extendₖNF (η-norm ∘ `) (subₖNF σ τ₂)) τ₁))

--------------------------------------------------------------------------------
-- renaming commutes with beta-reduction

↻-renₖNF-β      : (ρ : Renamingₖ Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ₁) κ₂) (τ₂ : NormalType Δ₁ κ₁) → 
                renₖNF ρ (τ₁ βₖNF[ τ₂ ]) ≡ (renₖNF (liftₖ ρ) τ₁) βₖNF[ (renₖNF ρ τ₂) ]
↻-renₖNF-β ρ τ₁ τ₂ = {!   !}

--------------------------------------------------------------------------------
-- Substituting a lifted substitution is equivalent to evaluating a lifted environment

↻-lifted-subₖNF-eval      : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ : NormalType (Δ₁ ,, κ) ★) → 
                    subₖNF (liftsₖNF σ) τ 
                  ≡ 
                    eval (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ)) (lifte idEnv)
↻-lifted-subₖNF-eval  σ τ = {!  !}

--------------------------------------------------------------------------------
-- Immediate application of a weakened type has no effect

weakenₖNF-β-id   : ∀ (τ : NormalType Δ ★) {τ₂ : NormalType Δ κ} → τ ≡ (weakenₖNF τ) βₖNF[ τ₂ ]
weakenₖNF-β-id τ {τ₂} = {!↻-weaken-sub  !}

--------------------------------------------------------------------------------
-- Substitution commutes with β reduction (again, but actually useful declaration).

↻-subₖNF-β      : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                    subₖNF σ (τ₁ βₖNF[ τ₂ ])
                  ≡ 
                    eval (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ₁)) (lifte idEnv)
                    βₖNF[ subₖNF σ τ₂ ]
↻-subₖNF-β σ τ₁ τ₂ =  {!   !}

--------------------------------------------------------------------------------
-- Substitution is congruent over _·'_

subₖNF-cong-·' :  ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) 
             (f : NormalType Δ₁ (κ₁ `→ ★))
             (v : NormalType Δ₁ κ₁) → 
             subₖNF σ (f ·' v) ≡ subₖNF σ f ·' subₖNF σ v
subₖNF-cong-·' σ (`λ f) v = ↻-subₖNF-β σ f v
  