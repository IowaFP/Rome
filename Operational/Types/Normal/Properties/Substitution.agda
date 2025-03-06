{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Normal.Properties.Substitution where


open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types
open import Rome.Operational.Types.Properties.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Substitution
open import Rome.Operational.Types.Normal.Eta-expansion
open import Rome.Operational.Types.Normal.Properties.Eta-expansion

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Theorems.Stability


--------------------------------------------------------------------------------
-- Functor laws for lifting

-- η-norm ∘ ` serves as an identity substitution on normal types.
liftsₖNF-id : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
              (x : KVar (Δ₁ ,, κ₁) κ₂) → liftsₖNF (η-norm ∘ `) x ≡ η-norm (` x)
liftsₖNF-id Z = refl
liftsₖNF-id (S x)  = ↻-ren-η-norm S x

--------------------------------------------------------------------------------
-- Substitution is a relative monad

subₖNF-id          : ∀ (τ : NormalType Δ κ) → subₖNF (η-norm ∘ `) τ ≡ τ
subₖNF-id τ = trans (cong ⇓ {x = subₖ (⇑ ∘ η-norm ∘ `) (⇑ τ)} {y = ⇑ τ} {!!}) (stability τ)

subₖNF-var : {!!}
subₖNF-var = {!!}

subₖNF-comp : {!!}
subₖNF-comp = {!!}

--------------------------------------------------------------------------------
--


  -- renaming commutes with beta-reduction.
↻-renₖNF-β      : (ρ : Renamingₖ Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ₁) κ₂) (τ₂ : NormalType Δ₁ κ₁) → 
                renₖNF ρ (τ₁ βₖNF[ τ₂ ]) ≡ (renₖNF (liftₖ ρ) τ₁) βₖNF[ (renₖNF ρ τ₂) ]
↻-renₖNF-β ρ τ₁ τ₂ = {!!}

↻-renₖNE-app      : (ρ : Renamingₖ Δ₁ Δ₂) (τ₁ : NeutralType Δ₁ (κ₁ `→ κ₂)) (τ₂ : NormalType Δ₁ κ₁) → 
                  renₖNE ρ (τ₁ · τ₂) ≡ (renₖNE ρ τ₁) · (renₖNF ρ τ₂)
↻-renₖNE-app ρ τ₁ τ₂ = {!!}

-- weakening commutes with substitution.
↻-weaken-sub : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ : NormalType Δ₁ κ) {κ'} → 
                  weakenₖNF {κ₁ = κ'} (subₖNF σ τ) ≡ subₖNF (liftsₖNF σ) (weakenₖNF τ)
↻-weaken-sub σ τ = {!!}

↻-subₖNF-lifts      : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ : NormalType (Δ₁ ,, κ) ★) → 
                    subₖNF (liftsₖNF σ) τ 
                  ≡ 
                    eval (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ)) (lifte idEnv)
↻-subₖNF-lifts σ τ = {!!}

↻-subₖNF-β      : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ ,, κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                    subₖNF σ (τ₁ βₖNF[ τ₂ ])
                  ≡ 
                    eval (subₖ (liftsₖ (⇑ ∘ σ)) (⇑ τ₁)) (lifte idEnv)
                    βₖNF[ subₖNF σ τ₂ ]
↻-subₖNF-β σ τ₁ τ₂ = {!!}


-- Weakening followed by application of τ equals τ
weakenₖNF-β-id   : ∀ (τ : NormalType Δ ★) {τ₂ : NormalType Δ κ} → τ ≡ (weakenₖNF τ) βₖNF[ τ₂ ]
weakenₖNF-β-id τ {τ₂} = {!↻-weaken-sub !}

-- id-when-ground : ∀ {κ} → Ground κ → (x : KVar Δ κ) → (⇑ ∘ η-norm ∘ `) x ≡ Types.` x
-- id-when-ground {κ = ★} g x = refl
-- id-when-ground {κ = L} g x = refl
-- id-when-ground {κ = R[ κ ]} g x = refl

-- sub-id-η-norm : ∀ (τ : NormalType Δ κ) → Types.sub (⇑ ∘ η-norm ∘ `) (⇑ τ) ≡ (⇑ τ)
-- sub-id-η-norm Unit = refl
-- sub-id-η-norm {κ = κ} (ne x {ground = g}) = {!!} -- trans (TypeProps.sub-cong (id-when-ground (toWitness g)) (⇑NE x)) (TypeProps.sub-id (⇑ (ne x)))
-- sub-id-η-norm (`λ τ) = cong Types.`λ (trans {!TypeProps.sub-cong TypeProps.lifts-id (⇑ τ)!} {!!})
-- sub-id-η-norm (τ `→ τ₁) = {!!}
-- sub-id-η-norm (`∀ κ τ) = {!!}
-- sub-id-η-norm (μ τ) = {!!}
-- sub-id-η-norm (π₁ ⇒ τ) = {!!}
-- sub-id-η-norm ε = {!!}
-- sub-id-η-norm (τ ▹ τ₁) = {!!}
-- sub-id-η-norm (lab l) = {!!}
-- sub-id-η-norm ⌊ τ ⌋ = {!!}
-- sub-id-η-norm (Π τ) = {!!}
-- sub-id-η-norm (ΠL τ) = {!!}
-- sub-id-η-norm (Σ τ) = {!!}
-- sub-id-η-norm (ΣL τ) = {!!}



-- -- trans 
-- --   (cong ⇓ (sub-id-η-norm τ)) 
-- --   (stability τ)


cong-·' :  ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) 
             (f : NormalType Δ₁ (κ₁ `→ ★))
             (v : NormalType Δ₁ κ₁) → 
             subₖNF σ (f ·' v) ≡ subₖNF σ f ·' subₖNF σ v
cong-·' σ (`λ f) v = trans (↻-subₖNF-β σ f v) refl
