{-# OPTIONS --safe #-}
module Rome.Operational.Types.Normal.Properties.Substitution where


open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Properties.Substitution
open import Rome.Operational.Types.Properties.Renaming
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Equivalence.Relation

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution

open import Rome.Operational.Types.Normal.Properties.Renaming
open import Rome.Operational.Types.Equivalence.Properties

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness

open import Rome.Operational.Types.Theorems.Stability

--------------------------------------------------------------------------------
-- Membership is preserved by substitution

∈-subₖNF : ∀ {l : Label} {τ : NormalType Δ₁ κ} {xs : SimpleRow NormalType Δ₁ R[ κ ]} → 
             (σ : SubstitutionₖNF Δ₁ Δ₂) → 
             (l , τ) ∈ xs → (l , subₖNF σ τ) ∈ subRowₖNF σ xs
∈-subₖNF σ (here refl) = here refl
∈-subₖNF σ (there i) = there (∈-subₖNF σ i)

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

↻-⇓-subRow : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) → 
             (ρ : SimpleRow Type Δ₁ R[ κ ]) →
             {oρ : True (ordered? ρ)} → 
             ⇓Row (subRowₖ (⇑ ∘ σ) ρ) ≡ subRowₖNF σ (⇓Row ρ)
↻-⇓-subRow σ ρ {oρ} = inj-⦅⦆ (↻-⇓-sub σ (⦅ ρ ⦆ oρ))

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

subPredₖNF-id : ∀ (π : NormalPred Δ R[ κ ]) → subPredₖNF idSubst π ≡ π
subPredₖNF-id π = trans (mapPredHO (λ τ → subₖNF idSubst τ) id subₖNF-id π) (mapPred-id π)

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
-- Lifting type equivalence over substitution by (⇑ ∘ σ)               

subₖ-≡t⇑ :  ∀ {σ : SubstitutionₖNF Δ₁ Δ₂} {τ₁ τ₂ : Type Δ₁ κ} → 
                  τ₁ ≡t τ₂ → subₖ (⇑ ∘ σ) τ₁ ≡t subₖ (⇑ ∘ σ) τ₂
subₖ-≡t⇑ {σ = σ} eq = subₖ-≡t {σ = ⇑ ∘ σ} eq                  


subₖNF-cong-≡t : ∀ {σ : SubstitutionₖNF Δ₁ Δ₂} {τ₁ τ₂ : NormalType Δ₁ κ} → 
                ⇑ τ₁ ≡t ⇑ τ₂ → subₖNF σ τ₁ ≡ subₖNF σ τ₂
subₖNF-cong-≡t {σ = σ} {τ₁} {τ₂} eq = 
  reify-≋ 
    (fundC 
      {τ₁ = subₖ (⇑ ∘ σ) (⇑ τ₁)} 
      {τ₂ = subₖ (⇑ ∘ σ) (⇑ τ₂)} 
      idEnv-≋ (subₖ-≡t⇑ {σ = σ} eq))

--------------------------------------------------------------------------------
-- Substitution over a variable substitutes the variable

subₖNF-var   : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂)(x : TVar Δ₁ κ) → 
              subₖNF σ (idSubst x) ≡ σ x
subₖNF-var {κ = κ} σ x = trans
  (reify-≋ (fundC {τ₁ = subₖ (⇑ ∘ σ) (⇑ (idSubst x))} {τ₂ = ⇑ (σ x)} idEnv-≋ 
    (eq-trans 
      (subₖ-≡t⇑ {σ = σ}  (η-norm-≡t (` x)))
      eq-refl)))
  (stability (σ x))

subₖNF-var-ground   : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂)(x : TVar Δ₁ κ) {g : True (ground? κ)} → 
                      subₖNF σ (ne (` x) {g}) ≡ σ x
subₖNF-var-ground σ x {g} = stability (σ x)                      

--------------------------------------------------------------------------------
-- Congruence of normality preserving substitution

subₖNF-cong : {σ₁ : SubstitutionₖNF Δ₁ Δ₂}{σ₂ : SubstitutionₖNF Δ₁ Δ₂} →
              (∀ {κ} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
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
        (↻-subₖ-renₖ {r = ρ} {σ = ⇑ ∘ σ} (⇑ τ)) 
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

↻-weakenPredₖNF-subPredₖNF : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ : NormalPred Δ₁ R[ κ ]) {κ'} → 
                  weakenPredₖNF {κ₁ = κ'} (subPredₖNF σ τ) ≡ subPredₖNF (liftsₖNF σ) (weakenPredₖNF τ)
↻-weakenPredₖNF-subPredₖNF σ π {κ'} with mapPredHO  (weakenₖNF {κ₁ = κ'} ∘ subₖNF σ) (subₖNF (liftsₖNF σ) ∘ weakenₖNF) (λ τ → ↻-weakenₖNF-subₖNF σ τ {κ'}) π 
↻-weakenPredₖNF-subPredₖNF σ (ρ₁ · ρ₂ ~ ρ₃) {κ'} | c = c
↻-weakenPredₖNF-subPredₖNF σ (ρ₁ ≲ ρ₂) {κ'} | c = c

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
        (λ { Z     → sym (subₖNF-var (extendₖNF (η-norm ∘ `) (subₖNF σ τ₂)) Z)
           ; (S x) → trans 
              (trans 
                (subₖNF-var σ x)
                (sym (subₖNF-id (σ x))))
              (↻-subₖNF-renₖNF S (extendₖNF idSubst (subₖNF σ τ₂)) (σ x)) })
        τ₁) 
      (subₖNF-comp (liftsₖNF σ) (extendₖNF (η-norm ∘ `) (subₖNF σ τ₂)) τ₁))

--------------------------------------------------------------------------------
-- renaming commutes with beta-reduction

↻-renₖNF-β      : (ρ : Renamingₖ Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ₁) κ₂) (τ₂ : NormalType Δ₁ κ₁) → 
                renₖNF ρ (τ₁ βₖNF[ τ₂ ]) ≡ (renₖNF (liftₖ ρ) τ₁) βₖNF[ (renₖNF ρ τ₂) ]
↻-renₖNF-β ρ τ₁ τ₂ = 
  trans 
    (sym (↻-renₖNF-subₖNF (extendₖNF idSubst τ₂) ρ τ₁)) 
    (trans 
      (subₖNF-cong 
        {σ₁ = renₖNF ρ ∘ extendₖNF idSubst τ₂} 
        {σ₂ = extendₖNF idSubst (renₖNF ρ τ₂) ∘ liftₖ ρ} 
        (λ { Z → refl
           ; (S x) → trans 
                (↻-ren-reify 
                  ρ 
                  {reflect (` x)} 
                  {reflect (` x)} 
                  (reflect-≋ refl)) 
                (reify-≋ (↻-ren-reflect ρ (` x))) }) 
        τ₁) 
      (↻-subₖNF-renₖNF (liftₖ ρ) (extendₖNF idSubst (renₖNF ρ τ₂)) τ₁))

--------------------------------------------------------------------------------
-- Immediate application of a weakened type has no effect

weakenₖNF-β-id   : ∀ {κ'} (τ : NormalType Δ κ) {τ₂ : NormalType Δ κ'} → τ ≡ (weakenₖNF τ) βₖNF[ τ₂ ]
weakenₖNF-β-id τ {τ₂} = 
  trans 
    (trans 
      (sym (stability τ))
      (reify-≋ (evalCRSubst idEnv-≋ (sym (subₖ-id (⇑ τ))))))
    (trans 
      (reify-≋ (fundC 
        {τ₁ = subₖ ` (⇑ τ)} 
        {τ₂ = subₖ (⇑ ∘ η-norm ∘ `) (⇑ τ)} 
        idEnv-≋ 
        (subₖ-cong-≡t {σ₁ = `} {σ₂ = ⇑ ∘ η-norm ∘ `} (eq-sym ∘ η-norm-≡t ∘ `) (⇑ τ)))) 
      (↻-subₖNF-renₖNF S (extendₖNF idSubst τ₂) τ))

weakenPredₖNF-Β-id : ∀ {κ'} (π : NormalPred Δ R[ κ ]) {τ₂ : NormalType Δ κ'} → π ≡ subPredₖNF (extendₖNF (λ x₁ → η-norm (` x₁)) τ₂) (weakenPredₖNF π)
weakenPredₖNF-Β-id π {τ₂} with mapPredHO id  (λ τ → (weakenₖNF τ) βₖNF[ τ₂ ]) (λ τ → weakenₖNF-β-id τ {τ₂}) π 
weakenPredₖNF-Β-id (ρ₁ · ρ₂ ~ ρ₃) {τ₂} | c = c
weakenPredₖNF-Β-id (ρ₁ ≲ ρ₂) {τ₂} | c = c

--------------------------------------------------------------------------------
-- Liftsₖ and liftsₖNF fusion under ≡t

liftsₖ-liftsₖNF≡t : ∀ {σ : SubstitutionₖNF Δ₁ Δ₂} → 
                   ∀ (x : TVar (Δ₁ ,, κ₁) κ) →
                    liftsₖ (⇑ ∘ σ) x ≡t (⇑ ∘ liftsₖNF σ) x
liftsₖ-liftsₖNF≡t Z = eq-sym ((η-norm-≡t (` Z)))
liftsₖ-liftsₖNF≡t {σ = σ} (S x) = inst (sym (↻-ren-⇑ S (σ x)))

--------------------------------------------------------------------------------
-- Substitution of a lifted substitution over τ is eqivalent under _≡t_ to 
-- substitution of (⇑ ∘ liftsₖNF σ) over τ

subₖ-liftsₖ-≡t : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) {κ κ'} (τ : Type (Δ₁ ,, κ') κ) →
                    subₖ (liftsₖ (⇑ ∘ σ)) τ ≡t subₖ (⇑ ∘ liftsₖNF σ) τ
subₖ-liftsₖ-≡t σ τ = subₖ-cong-≡t liftsₖ-liftsₖNF≡t τ

weaken-⇓ : ∀ {κ'}(τ : Type (Δ₁ ,, κ') κ) → 
                  ⇓ τ ≡ reify (eval τ (extende (renSem S ∘ idEnv) (reflect (` Z))))
weaken-⇓ τ = reify-≋ (idext (λ { Z → reflect-≋ refl
                                      ; (S x) → sym-≋ (↻-ren-reflect S (` x)) }) τ)

--------------------------------------------------------------------------------
-- Substituting a lifted substitution is equivalent to evaluating a lifted environment

↻-lifted-subₖNF-eval      : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ : NormalType (Δ₁ ,, κ) ★) → 
                    subₖNF (liftsₖNF σ) τ 
                  ≡ 
                    eval (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ)) (lifte idEnv)
↻-lifted-subₖNF-eval  σ τ = 
  trans 
    (fundC idEnv-≋ (eq-sym (subₖ-liftsₖ-≡t σ (⇑ τ))))
    (weaken-⇓ (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ)))

--------------------------------------------------------------------------------
-- Substitution commutes with β reduction (again, but actually useful declaration).

↻-subₖNF-β      : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                    subₖNF σ (τ₁ βₖNF[ τ₂ ])
                  ≡ 
                    eval (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ₁)) (lifte idEnv)
                    βₖNF[ subₖNF σ τ₂ ]
↻-subₖNF-β σ τ₁ τ₂ =  
  trans 
    (↻-subₖNF-β' σ τ₁ τ₂) 
    (cong (λ x → x βₖNF[ subₖNF σ τ₂ ]) 
      (trans         
        (completeness (eq-sym (subₖ-liftsₖ-≡t σ (⇑ τ₁))))
        (weaken-⇓ (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ₁)))))

--------------------------------------------------------------------------------
-- Substitution commutes over _·'_

↻-subₖNF-·' :  
           ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) 
             (f : NormalType Δ₁ (κ₁ `→ ★))
             (v : NormalType Δ₁ κ₁) → 
             subₖNF σ (f ·' v) ≡ subₖNF σ f ·' subₖNF σ v
↻-subₖNF-·' σ (`λ f) v = ↻-subₖNF-β σ f v

--------------------------------------------------------------------------------
-- Substitution commutes with embedding

↻-sub-⇑ : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) → (τ : NormalType Δ₁ κ) → 
          ⇑ (subₖNF σ τ) ≡t subₖ (⇑ ∘ σ) (⇑ τ)
↻-sub-⇑ σ τ = embed-≡t (⇑-inj  (subₖNF σ τ) (⇓ (subₖ (⇑ ∘ σ) (⇑ τ))) refl)

--------------------------------------------------------------------------------
-- Substitution commutes with embedding (over rows)

↻-sub-⇑Row : ∀ {Δ₁ Δ₂} (σ : SubstitutionₖNF Δ₁ Δ₂) (ys : SimpleRow NormalType Δ₁ R[ κ ]) → 
        ⇑Row (subRowₖNF σ (⇓Row (⇑Row ys))) ≡r subRowₖ (⇑ ∘ σ) (⇑Row ys)
↻-sub-⇑Row σ [] = eq-[]
↻-sub-⇑Row σ ((l , τ) ∷ ys) rewrite stability τ = eq-cons refl (↻-sub-⇑ σ τ) (↻-sub-⇑Row σ ys)

--------------------------------------------------------------------------------
-- Embedding commutes with β-reduction

↻-β-⇑ : ∀ (τ₁ : NormalType (Δ ,, κ₁) κ₂) (τ₂ : NormalType Δ κ₁) → 
        ⇑ (τ₁ βₖNF[ τ₂ ]) ≡t (⇑ τ₁) βₖ[ ⇑ τ₂ ]
↻-β-⇑ τ₁ τ₂ = 
  embed-≡t {τ₁ = τ₁ βₖNF[ τ₂ ]} {⇑ τ₁ βₖ[ ⇑ τ₂ ]} 
  (reify-≋ 
  (fundC {τ₁ = subₖ (λ x → ⇑ (extendₖNF idSubst τ₂ x)) (⇑ τ₁)}
         {⇑ τ₁ βₖ[ ⇑ τ₂ ]} 
         idEnv-≋ 
         (subₖ-cong-≡t 
           (λ { Z → eq-refl ; (S x) → η-norm-≡t (` x) }) 
           (⇑ τ₁))))


--------------------------------------------------------------------------------
-- Normalization commutes with β-reduction

↻-β-⇓ : ∀ (τ₁ : Type (Δ ,, κ) ★) (τ₂ : Type Δ κ) → 
        ⇓ (τ₁ βₖ[ τ₂ ]) ≡ (⇓ τ₁) βₖNF[ ⇓ τ₂ ]
↻-β-⇓ τ₁ τ₂ = 
  reify-≋ 
  (fundC 
    {τ₁ = subₖ (extendₖ ` τ₂) τ₁}
    {τ₂ = subₖ (λ x → ⇑ (extendₖNF idSubst (⇓ τ₂) x)) (⇑ (eval τ₁ idEnv))}
    idEnv-≋ 
      (eq-trans 
        (subₖ-cong-≡t (λ { Z → soundness τ₂ ; (S x) → eq-sym (η-norm-≡t (` x)) }) τ₁) 
        (subₖ-≡t (soundness τ₁))))

--------------------------------------------------------------------------------
-- _·'_ commutes with embedding

↻-·'-⇑ : (f : NormalType Δ (κ₁ `→ κ₂)) → (N : NormalType Δ κ₁) → ⇑ (f ·' N) ≡t ⇑ f · ⇑ N
↻-·'-⇑ (`λ f) N = 
  eq-trans 
    (eq-trans 
      (↻-sub-⇑ (extendₖNF idSubst N) f) 
      (subₖ-cong-≡t (λ { Z → eq-refl
                       ; (S x) → η-norm-≡t  (` x) }) (⇑ f))) 
    (eq-sym eq-β)

--------------------------------------------------------------------------------
-- _·'_ and mapping are stable (Denormalization followed by renormalization yields themselves)

stability-·' : (f : NormalType Δ (κ₁ `→ κ₂)) → (N : NormalType Δ κ₁) → f ·' N ≡ ⇓ (⇑ f · ⇑ N)
stability-·' f N = trans 
    (sym (stability (f ·' N))) 
    (completeness {τ₁ = ⇑ (f ·' N)} {τ₂ =  ⇑ f · ⇑ N} (↻-·'-⇑ f N))

stability-map : ∀ (f : NormalType Δ (κ₁ `→ κ₂)) → (xs : SimpleRow NormalType Δ R[ κ₁ ]) → 
                map (map₂ (_·'_ f)) xs ≡ reifyRow 
                  ((evalRow (⇑Row xs) idEnv .fst) ,
                  (λ i → 
                    ((evalRow (⇑Row xs) idEnv .snd i) .fst) , 
                    (eval (⇑ f) idEnv id ((evalRow (⇑Row xs) idEnv .snd i) .snd)))) 
stability-map f [] = refl
stability-map f (x ∷ xs) = (cong₂ _∷_ (cong₂ _,_ refl (stability-·' f (x .snd))) (stability-map f xs))

--------------------------------------------------------------------------------
-- Normality preserving substitution commutes over <$>

↻-sub-⇓-<$> : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) → 
          (F : NormalType Δ₁ (κ₁ `→ κ₂))
          (ρ : NormalType Δ₁ R[ κ₁ ]) → 
          ⇓ (⇑ (subₖNF σ F) <$> ⇑ (subₖNF σ ρ)) ≡  subₖNF σ (⇓ (⇑ F <$> ⇑ ρ))
↻-sub-⇓-<$> σ F@(`λ M) ρ  = trans 
  (reify-≋
     {V₁ = (↑ (subₖNF σ F)) <$>V ((↑ (subₖNF σ ρ)))} 
     {V₂ = (eval (subₖ (⇑ ∘ σ) (⇑ F)) idEnv) <$>V (eval (subₖ (⇑ ∘ σ) (⇑ ρ)) idEnv)}  
     (cong-<$> 
      (fundC idEnv-≋ (↻-sub-⇑ σ F)) 
      ((fundC idEnv-≋ (↻-sub-⇑ σ ρ)))))
  (↻-⇓-sub σ (⇑ F <$> ⇑ ρ))

--------------------------------------------------------------------------------
-- Ordering is preserved by substitution and embedding

ordered-subRowₖ-⇑ : ∀ {Δ₁ Δ₂} (σ : SubstitutionₖNF Δ₁ Δ₂) → {ys : SimpleRow NormalType Δ₁ R[ κ ]} → 
                      NormalOrdered ys → 
                      Ordered (subRowₖ (⇑ ∘ σ) (⇑Row ys))
ordered-subRowₖ-⇑ σ {[]} oys = tt
ordered-subRowₖ-⇑ σ {(l , τ) ∷ []} oys = tt
ordered-subRowₖ-⇑ σ {(l , τ) ∷ (l' , τ') ∷ ys} (l<l' , oys) = l<l' , ordered-subRowₖ-⇑ σ oys
