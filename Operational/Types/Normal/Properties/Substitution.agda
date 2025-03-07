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
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE

open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Theorems.Stability
open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness             

--------------------------------------------------------------------------------
-- Substitution of types is related to substitution of normal types

raise-subₖ-result          : ∀ {σ : SubstitutionₖNF Δ₁ Δ₂} → 
                               (τ : NormalType Δ₁ κ) (υ : Type Δ₂ κ) → 
                               subₖ (⇑ ∘ σ) (⇑ τ) ≡ υ → 
                               subₖNF σ τ ≡ ⇓ υ

raise-subₖ-result {σ = σ} τ υ eq = cong ⇓ {x = (subₖ (λ x → ⇑ (σ x)) (⇑ τ))} {y = υ} eq

↻-⇓-sub : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂) → 
             (τ : Type Δ₁ κ) → ⇓ (subₖ (⇑ ∘ σ) τ) ≡ subₖNF σ (⇓ τ)
↻-⇓-sub σ τ = 
  trans 
    (reify-≋ (↻-subₖ-eval τ idEnv-≋ (⇑ ∘ σ))) 
    (sym (trans 
      (reify-≋ (↻-subₖ-eval (⇑ (⇓ τ)) idEnv-≋ (⇑ ∘ σ))) 
      (reify-≋ (fundComplete ((idext idEnv-≋) ∘ ⇑ ∘ σ) (eq-sym (soundness τ))))))

--------------------------------------------------------------------------------
-- Ground equivalence of substitutions σ₁ and σ₂ means σ₁ and σ₂ equate
-- *just* type variables at ground kind.

_≈g_ : ∀ {Δ₁} {Δ₂} → (σ₁ σ₂ : Substitutionₖ Δ₁ Δ₂) → Set
_≈g_ {Δ₁ = Δ₁} σ₁ σ₂ = ∀ {κ} (g : True (ground? κ)) (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x

--------------------------------------------------------------------------------
-- Functor laws for lifting

-- η-norm ∘ ` serves as an identity substitution on normal types.
liftsₖNF-id : ∀ (x : KVar (Δ ,, κ₁) κ) → 
                  liftsₖNF (η-norm ∘ `) x ≡ (η-norm ∘ `) x
liftsₖNF-id  {κ = ★}      Z = refl
liftsₖNF-id  {κ = L}       Z = refl
liftsₖNF-id  {κ = R[ κ₃ ]} Z = refl
liftsₖNF-id  {κ = κ₁ `→ κ₂} Z = refl
liftsₖNF-id  (S x) = {! ↻-ren-⇑ S  !}
  -- trans (sym (↻-ren-⇑ S (η-norm (` x)))) 
  -- (cong ⇑ {renₖNF S (η-norm (` x))} {η-norm (` (S x))} (↻-ren-η-norm S x))
foo : ∀ (x : KVar (Δ ,, κ₁) κ) → 
                  ⇑ (liftsₖNF (η-norm ∘ `) x) ≡ liftsₖ (⇑ ∘ η-norm ∘ `) x
foo Z = {!   !}
foo (S x) = {!   !}                   


liftsₖ-cong-ground : 
  ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
    σ₁ ≈g σ₂ → 
    ∀ {κ} (g : True (ground? κ)) (x : KVar (Δ₁ ,, κ₁) κ) → liftsₖ σ₁ x ≡ liftsₖ σ₂ x
liftsₖ-cong-ground c g Z = refl
liftsₖ-cong-ground c g (S x) = cong (renₖ S) (c g x)

--------------------------------------------------------------------------------
-- Substitution is a relative monad

-- subₖ-cong-ground : 
--   ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
--     σ₁ ≈g σ₂ → 
--     (τ : NormalType Δ₁ κ) → subₖ σ₁ (⇑ τ) ≡ subₖ σ₂ (⇑ τ)
-- subₖ-cong-groundNE : 
--   ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
--     σ₁ ≈g σ₂ → 
--     True (ground? κ) → (τ : NeutralType Δ₁ κ) → subₖ σ₁ (⇑NE τ) ≡ subₖ σ₂ (⇑NE τ)    

-- subₖ-cong-groundNE {κ = κ} c g (` α) = c {κ} g α
-- subₖ-cong-groundNE {κ = κ} c g (x · τ) = cong₂ _·_ {! subₖ-cong  !} {! subₖ-cong-ground c g   !}
-- subₖ-cong-groundNE {κ = κ} c g (φ <$> x) = {!   !}

-- subₖ-cong-ground {κ = κ} c Unit = refl
-- subₖ-cong-ground {κ = κ} c (ne x {g}) = subₖ-cong-groundNE c g x
-- subₖ-cong-ground {κ = κ} c (`λ τ) = cong `λ (subₖ-cong-ground (liftsₖ-cong-ground c) τ)
-- subₖ-cong-ground {κ = κ} c (τ `→ τ₁) = cong₂ _`→_ (subₖ-cong-ground c τ) (subₖ-cong-ground c τ₁)
-- subₖ-cong-ground {κ = κ} c (`∀ κ₁ τ) = {!   !}
-- subₖ-cong-ground {κ = κ} c (μ τ) = cong μ (subₖ-cong-ground c τ)
-- subₖ-cong-ground {κ = κ} c (π₁ ⇒ τ) = {!   !}
-- subₖ-cong-ground {κ = κ} c ε = refl
-- subₖ-cong-ground {κ = κ} c (τ ▹ τ₁) = {!   !}
-- subₖ-cong-ground {κ = κ} c (lab l) = refl
-- subₖ-cong-ground {κ = κ} c ⌊ τ ⌋ = cong ⌊_⌋ (subₖ-cong-ground c τ)
-- subₖ-cong-ground {κ = κ} c (Π τ) = {!   !}
-- subₖ-cong-ground {κ = κ} c (ΠL τ) = {!   !}
-- subₖ-cong-ground {κ = κ} c (Σ τ) = {!   !}
-- subₖ-cong-ground {κ = κ} c (ΣL τ) = {!   !}

-- fuckit : ∀ (τ : NormalType (Δ ,, κ₁) κ) → 
--             subₖ (liftsₖ (⇑ ∘ η-norm ∘ `)) (⇑ τ) ≡ 
--             subₖ (⇑ ∘ η-norm ∘ `) (⇑ τ)          
-- fuckit Unit = refl
-- fuckit (ne x) = {!   !}
-- fuckit (`λ τ) = cong `λ {! sub-lift-weaken  !}
-- fuckit (τ `→ τ₁) = {!   !}
-- fuckit (`∀ κ τ) = {!   !}
-- fuckit (μ τ) = {!   !}
-- fuckit (π₁ ⇒ τ) = {!   !}
-- fuckit ε = {!   !}
-- fuckit (τ ▹ τ₁) = {!   !}
-- fuckit (lab l) = {!   !}
-- fuckit ⌊ τ ⌋ = {!   !}
-- fuckit (Π τ) = {!   !}
-- fuckit (ΠL τ) = {!   !}
-- fuckit (Σ τ) = {!   !}
-- fuckit (ΣL τ) = {!   !}

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
      {! sub-lift-weaken (⇑ ∘ η-norm ∘ `) (⇑ τ)   !} -- (subₖ-cong {σ₁ = liftsₖ (⇑ ∘ η-norm ∘ `)} {σ₂ = ⇑ ∘ η-norm ∘ `} {!   !} (⇑ τ)) 
      (subₖ-η-norm-id τ))
    -- (trans 
    --   (subₖ-cong-ground {σ₁ = liftsₖ (⇑ ∘ η-norm ∘ `)} {σ₂ = (⇑ ∘ η-norm ∘ `)} (liftsₖ-id-ground {Δ} {κ₁}) τ) 
    --   (subₖ-η-norm-id τ))
subₖ-η-norm-id (τ₁ `→ τ₂) = {!   !}
subₖ-η-norm-id (`∀ κ τ) = {!   !}
subₖ-η-norm-id (μ τ) = cong μ (subₖ-η-norm-id τ)
subₖ-η-norm-id (π ⇒ τ) = {!   !}
subₖ-η-norm-id ε = refl
subₖ-η-norm-id (τ ▹ τ₁) = {!   !}
subₖ-η-norm-id (lab l) = refl
subₖ-η-norm-id ⌊ τ ⌋ = {!   !}
subₖ-η-norm-id (Π τ) = {!   !}
subₖ-η-norm-id (ΠL τ) = {!   !}
subₖ-η-norm-id (Σ τ) = {!   !}
subₖ-η-norm-id (ΣL τ) = {!   !}


subₖNF-id          : ∀ (τ : NormalType Δ κ) → subₖNF (η-norm ∘ `) τ ≡ τ
subₖNF-id τ = 
  trans 
    (reify-≋ (↻-subₖ-eval (⇑ τ) idEnv-≋ (⇑ ∘ η-norm ∘ `)))
    {! ⇓  !} -- trans (raise-subₖ-result {σ = η-norm ∘ `} τ (⇑ τ) (subₖ-η-norm-id τ)) (stability τ)

subₖNF-var   : ∀ (σ : SubstitutionₖNF Δ₁ Δ₂)(x : KVar Δ₁ κ) {g : True (ground? κ)} → 
                  subₖNF σ (ne (` x) {g}) ≡ σ x
subₖNF-var σ x {g} = stability (σ x)                  

-- subₖNF-cong : ∀ {σ₁ σ₂ : SubstitutionₖNF Δ₁ Δ₂} → 
--                 (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
--                 (τ : NormalType Δ₁ κ) → subₖNF σ₁ τ ≡ subₖNF σ₂ τ
-- subₖNF-cong {σ₁ = σ₁} {σ₂} r τ = raise-subₖ-result {σ = σ₁} τ (subₖ (⇑ ∘ σ₂) (⇑ τ)) (subₖ-cong-ground (λ {κ} g x → cong ⇑  (r x)) τ) 


subₖNF-comp : ∀ {σ₁ : SubstitutionₖNF Δ₁ Δ₂} {σ₂ : SubstitutionₖNF Δ₂ Δ₃} → 
                (τ : NormalType Δ₁ κ) → subₖNF (subₖNF σ₂ ∘ σ₁) τ ≡ subₖNF σ₂ (subₖNF σ₁ τ)
subₖNF-comp {σ₁ = σ₁} {σ₂} τ = 
  trans 
    (raise-subₖ-result {σ = subₖNF σ₂ ∘ σ₁} τ (⇑ (subₖNF σ₂ (subₖNF σ₁ τ))) {!   !}) 
    (stability _)

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
   