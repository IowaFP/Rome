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
liftsₖ-id-ground : ∀ {κ} (g : True (ground? κ)) → 
                  (x : KVar (Δ₁ ,, κ₁) κ) → liftsₖ (⇑ ∘ η-norm ∘ `) x ≡ ⇑ (η-norm (` x))
liftsₖ-id-ground {κ = ★} g      Z = refl
liftsₖ-id-ground {κ = L}  g      Z = refl
liftsₖ-id-ground {κ = R[ κ₃ ]} g Z = refl
liftsₖ-id-ground g (S x) = {! ↻-ren-η-norm S x  !}

-- subₖ-liftsₖ-id (S x)  = ↻-ren-η-norm S x

--------------------------------------------------------------------------------
-- Substitution is a relative monad

subₖ-cong-ground : 
  ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
    (∀ {κ} (_ : True (ground? κ)) (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
    (τ : NormalType Δ₁ κ) → subₖ σ₁ (⇑ τ) ≡ subₖ σ₂ (⇑ τ)
subₖ-cong-ground {κ = κ} c Unit = refl
subₖ-cong-ground {κ = κ} c (ne (` α) {g}) = c {κ} g α
subₖ-cong-ground {κ = κ} c (ne (x · τ)) = {!   !}
subₖ-cong-ground {κ = κ} c (ne (φ <$> x)) = {!   !}
subₖ-cong-ground {κ = κ} c (`λ τ) = cong `λ (subₖ-cong-ground (λ {κ} g x → {! liftsₖ-cong    !}) τ)
subₖ-cong-ground {κ = κ} c (τ `→ τ₁) = {!   !}
subₖ-cong-ground {κ = κ} c (`∀ κ₁ τ) = {!   !}
subₖ-cong-ground {κ = κ} c (μ τ) = cong μ (subₖ-cong-ground c τ)
subₖ-cong-ground {κ = κ} c (π₁ ⇒ τ) = {!   !}
subₖ-cong-ground {κ = κ} c ε = refl
subₖ-cong-ground {κ = κ} c (τ ▹ τ₁) = {!   !}
subₖ-cong-ground {κ = κ} c (lab l) = refl
subₖ-cong-ground {κ = κ} c ⌊ τ ⌋ = cong ⌊_⌋ (subₖ-cong-ground c τ)
subₖ-cong-ground {κ = κ} c (Π τ) = {!   !}
subₖ-cong-ground {κ = κ} c (ΠL τ) = {!   !}
subₖ-cong-ground {κ = κ} c (Σ τ) = {!   !}
subₖ-cong-ground {κ = κ} c (ΣL τ) = {!   !}

subₖ-η-norm-id : ∀ (τ : NormalType Δ κ) → subₖ (⇑ ∘ η-norm ∘ `) (⇑ τ) ≡ ⇑ τ
subₖ-η-norm-id Unit = refl
subₖ-η-norm-id {κ = ★} (ne (` α) {ground}) = refl
subₖ-η-norm-id {κ = L} (ne (` α) {ground}) = refl
subₖ-η-norm-id {κ = R[ κ ]} (ne (` α) {ground}) = refl
subₖ-η-norm-id (ne (x · τ) {ground}) rewrite subₖ-η-norm-id τ = {!  !}
subₖ-η-norm-id (ne (φ <$> x) {ground}) = {!   !}
subₖ-η-norm-id {Δ = Δ} (`λ {κ₁ = κ₁} τ) = 
  cong `λ 
    (trans 
      (subₖ-cong-ground {σ₁ = liftsₖ (⇑ ∘ η-norm ∘ `)} {σ₂ = (⇑ ∘ η-norm ∘ `)} (liftsₖ-id-ground {Δ} {κ₁}) τ) 
      (subₖ-η-norm-id τ))
subₖ-η-norm-id (τ `→ τ₁) = {!   !}
subₖ-η-norm-id (`∀ κ τ) = {!   !}
subₖ-η-norm-id (μ τ) = cong μ (subₖ-η-norm-id τ)
subₖ-η-norm-id (π₁ ⇒ τ) = {!   !}
subₖ-η-norm-id ε = refl
subₖ-η-norm-id (τ ▹ τ₁) = {!   !}
subₖ-η-norm-id (lab l) = refl
subₖ-η-norm-id ⌊ τ ⌋ = {!   !}
subₖ-η-norm-id (Π τ) = {!   !}
subₖ-η-norm-id (ΠL τ) = {!   !}
subₖ-η-norm-id (Σ τ) = {!   !}
subₖ-η-norm-id (ΣL τ) = {!   !}

subₖNF-id          : ∀ (τ : NormalType Δ κ) → subₖNF (η-norm ∘ `) τ ≡ τ
subₖNF-id τ = trans (cong ⇓ {x = subₖ (⇑ ∘ η-norm ∘ `) (⇑ τ)} {y = ⇑ τ} (subₖ-η-norm-id τ)) (stability τ)

-- subₖNF-var : {!  !}
-- subₖNF-var = {!  !}

-- subₖNF-comp : {!  !}
-- subₖNF-comp = {!  !}

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
