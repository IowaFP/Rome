{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Properties.Substitution where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence

open import Rome.Operational.Types.Properties.Renaming


-------------------------------------------------------------------------------
-- Functor laws for lifting

liftsₖ-cong : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
              (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (x : KVar (Δ₁ ,, κ₁) κ₂) → liftsₖ σ₁ x ≡ liftsₖ σ₂ x
liftsₖ-cong e Z = refl
liftsₖ-cong e (S x) = cong (renₖ S) (e x)              

liftsₖ-id    : ∀ (x : KVar (Δ ,, κ₁) κ₂) → liftsₖ ` x ≡ ` x 
liftsₖ-id Z = refl
liftsₖ-id (S x) = refl

-- Fusion for liftsₖ and lift
liftsₖ-liftₖ      : ∀ {ρ : Renamingₖ Δ₁ Δ₂}{σ : Substitutionₖ Δ₂ Δ₃} 
                    (x : KVar (Δ₁ ,, κ₁) κ₂) → 
                    liftsₖ (σ ∘ ρ) x ≡ liftsₖ σ (liftₖ ρ x)
liftsₖ-liftₖ Z = refl
liftsₖ-liftₖ (S x) = refl

renₖ-liftₖ-liftsₖ : ∀ {σ : Substitutionₖ Δ₁ Δ₂}{ρ : Renamingₖ Δ₂ Δ₃}(x : KVar (Δ₁ ,, κ₁) κ₂) → 
                    liftsₖ (renₖ ρ ∘ σ) x ≡ renₖ (liftₖ ρ) (liftsₖ σ x)
renₖ-liftₖ-liftsₖ Z = refl
renₖ-liftₖ-liftsₖ {σ = σ} {ρ} (S x) = trans (sym (renₖ-comp ρ S (σ x))) (renₖ-comp S (liftₖ ρ) (σ x))                    

-------------------------------------------------------------------------------
-- Functor laws for substitution

subₖ-cong : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
              (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (τ : Type Δ₁ κ) → subₖ σ₁ τ ≡ subₖ σ₂ τ
subₖ-cong e Unit = refl
subₖ-cong e ε = refl
subₖ-cong e (` α) = e α
subₖ-cong e (`λ τ) = cong `λ (subₖ-cong (liftsₖ-cong e) τ)
subₖ-cong e (τ₁ · τ₂) = cong₂ _·_ (subₖ-cong e τ₁) (subₖ-cong e τ₂)
subₖ-cong e (τ₁ `→ τ₂) = cong₂ _`→_ (subₖ-cong e τ₁) (subₖ-cong e τ₂)
subₖ-cong e (`∀ κ τ) = cong (`∀ κ) (subₖ-cong (liftsₖ-cong e) τ)
subₖ-cong e (μ τ) = cong μ (subₖ-cong e τ)
subₖ-cong e ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
  subₖ-cong e ρ₁ | subₖ-cong e ρ₂ | subₖ-cong e ρ₃ | subₖ-cong e τ = refl
subₖ-cong e ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite
  subₖ-cong e ρ₁ | subₖ-cong e ρ₂ | subₖ-cong e τ = refl
subₖ-cong e (lab l) = refl
subₖ-cong e (τ₁ ▹ τ₂) = cong₂ _▹_ (subₖ-cong e τ₁) (subₖ-cong e τ₂)
subₖ-cong e ⌊ τ ⌋ = cong ⌊_⌋ (subₖ-cong e τ)
subₖ-cong e Π = refl
subₖ-cong e Σ = refl
subₖ-cong e (τ <$> τ₁) = cong₂ _<$>_ (subₖ-cong e τ) (subₖ-cong e τ₁)

subₖ-id : ∀ (τ : Type Δ κ) → subₖ ` τ ≡ τ
subₖ-id Unit = refl
subₖ-id ε = refl
subₖ-id (` α) = refl
subₖ-id (`λ τ) = cong `λ (trans (subₖ-cong  {σ₁ = liftsₖ `} {σ₂ = `} liftsₖ-id τ) (subₖ-id τ))
subₖ-id (τ₁ · τ₂) = cong₂ _·_ (subₖ-id τ₁) (subₖ-id τ₂)
subₖ-id (τ₁ `→ τ₂) = cong₂ _`→_ (subₖ-id τ₁) (subₖ-id τ₂)
subₖ-id (`∀ κ τ) = cong (`∀ κ) (trans (subₖ-cong liftsₖ-id τ) (subₖ-id τ))
subₖ-id (μ τ) = cong μ (subₖ-id τ)
subₖ-id ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
  subₖ-id ρ₁ | subₖ-id ρ₂ | subₖ-id ρ₃ | subₖ-id τ = refl
subₖ-id ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite
  subₖ-id ρ₁ | subₖ-id ρ₂ | subₖ-id τ = refl
subₖ-id (lab l) = refl
subₖ-id (τ₁ ▹ τ₂) = cong₂ _▹_ (subₖ-id τ₁) (subₖ-id τ₂)
subₖ-id ⌊ τ ⌋ = cong ⌊_⌋ (subₖ-id τ)
subₖ-id Π = refl
subₖ-id Σ = refl
subₖ-id (τ₁ <$> τ₂) = cong₂ _<$>_ (subₖ-id τ₁) (subₖ-id τ₂)


-------------------------------------------------------------------------------
-- lifting a substitution fixes points

-- sub-lift-fp : ∀ {σ : Substitutionₖ Δ₁ Δ₂} (τ : Type Δ₁ κ₂) → 
--                 subₖ (liftsₖ σ) (weakenₖ τ) ≡ subₖ σ τ
-- sub-lift-fp τ = ?

-------------------------------------------------------------------------------
-- subₖstitution and renₖaming commute

↻-subₖ-renₖ : ∀ {ρ : Renamingₖ Δ₁ Δ₂}{σ : Substitutionₖ Δ₂ Δ₃}  
                (τ : Type Δ₁ κ) → subₖ (σ ∘ ρ) τ ≡ subₖ σ (renₖ ρ τ)
↻-subₖ-renₖ {ρ = ρ} {σ} Unit = refl
↻-subₖ-renₖ {ρ = ρ} {σ} ε = refl
↻-subₖ-renₖ {ρ = ρ} {σ} (` α) = refl
↻-subₖ-renₖ {ρ = ρ} {σ} (`λ τ) = cong `λ (trans (subₖ-cong liftsₖ-liftₖ τ) (↻-subₖ-renₖ τ))
↻-subₖ-renₖ {ρ = ρ} {σ} (τ₁ · τ₂) = cong₂ _·_ (↻-subₖ-renₖ τ₁) (↻-subₖ-renₖ τ₂)
↻-subₖ-renₖ {ρ = ρ} {σ} (τ₁ `→ τ₂) = cong₂ _`→_ (↻-subₖ-renₖ τ₁) (↻-subₖ-renₖ τ₂) 
↻-subₖ-renₖ {ρ = ρ} {σ} (`∀ κ τ) = cong (`∀ κ) (trans (subₖ-cong liftsₖ-liftₖ τ) (↻-subₖ-renₖ τ))
↻-subₖ-renₖ {ρ = ρ} {σ} (μ τ) = cong μ (↻-subₖ-renₖ τ)
↻-subₖ-renₖ {ρ = ρ} {σ} ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
    ↻-subₖ-renₖ {ρ = ρ} {σ} ρ₁ 
  | ↻-subₖ-renₖ {ρ = ρ} {σ} ρ₂ 
  | ↻-subₖ-renₖ {ρ = ρ} {σ} ρ₃ 
  | ↻-subₖ-renₖ {ρ = ρ} {σ} τ = refl
↻-subₖ-renₖ {ρ = ρ} {σ} ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite 
    ↻-subₖ-renₖ {ρ = ρ} {σ} ρ₁ 
  | ↻-subₖ-renₖ {ρ = ρ} {σ} ρ₂ 
  | ↻-subₖ-renₖ {ρ = ρ} {σ} τ = refl
↻-subₖ-renₖ {ρ = ρ} {σ} (lab l) = refl
↻-subₖ-renₖ {ρ = ρ} {σ} (τ₁ ▹ τ₂) = cong₂ _▹_ (↻-subₖ-renₖ τ₁) (↻-subₖ-renₖ τ₂) 
↻-subₖ-renₖ {ρ = ρ} {σ} ⌊ τ ⌋ = cong ⌊_⌋ (↻-subₖ-renₖ τ)
↻-subₖ-renₖ {ρ = ρ} {σ} Π = refl
↻-subₖ-renₖ {ρ = ρ} {σ} Σ = refl
↻-subₖ-renₖ {ρ = ρ} {σ} (τ₁ <$> τ₂) = cong₂ _<$>_ (↻-subₖ-renₖ τ₁) (↻-subₖ-renₖ τ₂) 

↻-renₖ-subₖ         : ∀ {σ : Substitutionₖ Δ₁ Δ₂}{ρ : Renamingₖ Δ₂ Δ₃}(τ : Type Δ₁ κ) →
                    subₖ (renₖ ρ ∘ σ) τ ≡ renₖ ρ (subₖ σ τ)
↻-renₖ-subₖ {σ = σ} {ρ} Unit = refl
↻-renₖ-subₖ {σ = σ} {ρ} ε = refl
↻-renₖ-subₖ {σ = σ} {ρ} (` α) = refl
↻-renₖ-subₖ {σ = σ} {ρ} (`λ τ) = cong `λ (trans (subₖ-cong renₖ-liftₖ-liftsₖ τ) (↻-renₖ-subₖ τ))
↻-renₖ-subₖ {σ = σ} {ρ} (τ₁ · τ₂) = cong₂ _·_ (↻-renₖ-subₖ τ₁) (↻-renₖ-subₖ τ₂)
↻-renₖ-subₖ {σ = σ} {ρ} (τ₁ `→ τ₂) = cong₂ _`→_ (↻-renₖ-subₖ τ₁) (↻-renₖ-subₖ τ₂)
↻-renₖ-subₖ {σ = σ} {ρ} (`∀ κ τ) = cong (`∀ κ) (trans (subₖ-cong renₖ-liftₖ-liftsₖ τ) (↻-renₖ-subₖ τ))
↻-renₖ-subₖ {σ = σ} {ρ} (μ τ) = cong μ (↻-renₖ-subₖ τ)
↻-renₖ-subₖ {σ = σ} {ρ} ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
    ↻-renₖ-subₖ {σ = σ} {ρ} ρ₁ 
  | ↻-renₖ-subₖ {σ = σ} {ρ} ρ₂ 
  | ↻-renₖ-subₖ {σ = σ} {ρ} ρ₃ 
  | ↻-renₖ-subₖ {σ = σ} {ρ} τ = refl
↻-renₖ-subₖ {σ = σ} {ρ} ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite 
    ↻-renₖ-subₖ {σ = σ} {ρ} ρ₁ 
  | ↻-renₖ-subₖ {σ = σ} {ρ} ρ₂ 
  | ↻-renₖ-subₖ {σ = σ} {ρ} τ = refl
↻-renₖ-subₖ {σ = σ} {ρ} (lab l) = refl
↻-renₖ-subₖ {σ = σ} {ρ} (τ₁ ▹ τ₂) = cong₂ _▹_ (↻-renₖ-subₖ τ₁) (↻-renₖ-subₖ τ₂)
↻-renₖ-subₖ {σ = σ} {ρ} ⌊ τ ⌋ = cong ⌊_⌋ (↻-renₖ-subₖ τ)
↻-renₖ-subₖ {σ = σ} {ρ} Π = refl
↻-renₖ-subₖ {σ = σ} {ρ} Σ = refl
↻-renₖ-subₖ {σ = σ} {ρ} (τ₁ <$> τ₂) = cong₂ _<$>_ (↻-renₖ-subₖ τ₁) (↻-renₖ-subₖ τ₂)

subₖ-weaken : ∀ (τ : Type Δ κ₁) (v : Type Δ κ₂) → 
             subₖ (extendₖ ` v) (renₖ S τ) ≡ τ 
subₖ-weaken τ v = trans (sym (↻-subₖ-renₖ {ρ = S} {σ = extendₖ ` v} τ)) (subₖ-id τ)

-------------------------------------------------------------------------------
-- Arrow functor law for liftsₖ & subₖ (needs commutativity of subₖ and renₖ)

liftsₖ-comp : ∀ (σ₁ : Substitutionₖ Δ₁ Δ₂)(σ₂ : Substitutionₖ Δ₂ Δ₃)
                (x : KVar (Δ₁ ,, κ₁) κ₂) → liftsₖ (subₖ σ₂ ∘ σ₁) x ≡ subₖ (liftsₖ σ₂) (liftsₖ σ₁ x)
liftsₖ-comp σ₁ σ₂ Z = refl
liftsₖ-comp σ₁ σ₂ (S x) = trans (sym (↻-renₖ-subₖ (σ₁ x))) (↻-subₖ-renₖ (σ₁ x)) 

subₖ-comp : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₂ Δ₃}
                (τ : Type Δ₁ κ) → subₖ (subₖ σ₂ ∘ σ₁) τ ≡ subₖ σ₂ (subₖ σ₁ τ)
subₖ-comp Unit = refl
subₖ-comp ε = refl
subₖ-comp (` α) = refl
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} (`λ τ) = 
  cong `λ ((trans 
    (subₖ-cong (liftsₖ-comp σ₁ σ₂) τ) 
    (subₖ-comp {σ₁ = liftsₖ σ₁} {σ₂ = liftsₖ σ₂} τ)))
subₖ-comp (τ₁ · τ₂) = cong₂ _·_ (subₖ-comp τ₁) (subₖ-comp τ₂)
subₖ-comp (τ₁ `→ τ₂) = cong₂ _`→_ (subₖ-comp τ₁) (subₖ-comp τ₂)
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} (`∀ κ τ) =   
  cong (`∀ κ) ((trans 
    (subₖ-cong (liftsₖ-comp σ₁ σ₂) τ) 
    (subₖ-comp {σ₁ = liftsₖ σ₁} {σ₂ = liftsₖ σ₂} τ)))
subₖ-comp (μ τ) = cong μ (subₖ-comp τ)
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
    subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₁ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₂ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₃ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} τ = refl
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite 
    subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₁ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} ρ₂ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} τ = refl
subₖ-comp (lab l) = refl
subₖ-comp (τ₁ ▹ τ₂) = cong₂ _▹_ (subₖ-comp τ₁) (subₖ-comp τ₂)
subₖ-comp ⌊ τ ⌋ = cong ⌊_⌋ (subₖ-comp τ)
subₖ-comp Π = refl
subₖ-comp Σ = refl
subₖ-comp (τ₁ <$> τ₂) = cong₂ _<$>_ (subₖ-comp τ₁) (subₖ-comp τ₂)

-------------------------------------------------------------------------------
-- 

renₖ-subₖ-id : ∀ (σ : Substitutionₖ Δ₁ Δ₂) (ρ : Renamingₖ Δ₂ Δ₃) 
                (τ :  Type Δ₂ κ) → renₖ ρ τ ≡ subₖ (` ∘ ρ) τ
renₖ-subₖ-id σ ρ τ = trans (cong (renₖ ρ) (sym (subₖ-id τ))) (trans (sym (↻-renₖ-subₖ τ)) refl )

-------------------------------------------------------------------------------
-- Renamingₖ commutes with β-reduction

↻-renₖ-β      : (ρ : Renamingₖ Δ₁ Δ₂) (τ₁ : Type (Δ₁ ,, κ₁) κ₂) (τ₂ : Type Δ₁ κ₁) → 
                renₖ ρ (τ₁ βₖ[ τ₂ ]) ≡ (renₖ (liftₖ ρ) τ₁) βₖ[ (renₖ ρ τ₂) ]  
↻-renₖ-β ρ τ₁ τ₂ = 
  trans 
    (sym (↻-renₖ-subₖ τ₁)) 
    (trans 
      (subₖ-cong (λ { Z → refl ; (S x) → refl }) τ₁) 
      (↻-subₖ-renₖ {ρ = liftₖ ρ} {extendₖ ` (renₖ ρ τ₂)} τ₁))                  

-------------------------------------------------------------------------------
-- Substitution commutes with β-reduction 

↻-subₖ-β      : (σ : Substitutionₖ Δ₁ Δ₂) (τ₁ : Type (Δ₁ ,, κ₁) κ₂) (τ₂ : Type Δ₁ κ₁) → 
                (subₖ (liftsₖ σ) τ₁ βₖ[ subₖ σ τ₂ ]) ≡ subₖ σ (τ₁ βₖ[ τ₂ ])
↻-subₖ-β σ τ₁ τ₂ = 
  trans 
    (sym (subₖ-comp {σ₁ = liftsₖ σ} {extendₖ ` (subₖ σ τ₂)} τ₁)) 
    (trans 
      (subₖ-cong (λ { Z → refl
                    ; (S x) → trans 
                        (sym (↻-subₖ-renₖ {ρ = S} {extendₖ ` (subₖ σ τ₂)} (σ x))) 
                        (subₖ-id (σ x)) }) τ₁) 
      (subₖ-comp {σ₁ = extendₖ ` τ₂} {σ} τ₁))