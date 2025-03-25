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
-- Substitution respects congruence

subₖ-cong : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
              (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (τ : Type Δ₁ κ) → subₖ σ₁ τ ≡ subₖ σ₂ τ
subRowₖ-cong : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
              (∀ {κ} (x : KVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (ρ : SimpleRow Type Δ₁ R[ κ ]) → subRowₖ σ₁ ρ ≡ subRowₖ σ₂ ρ
subₖ-cong e ε = refl
subₖ-cong e (` α) = e α
subₖ-cong e (`λ τ) = cong `λ (subₖ-cong (liftsₖ-cong e) τ)
subₖ-cong e (τ₁ · τ₂) = cong₂ _·_ (subₖ-cong e τ₁) (subₖ-cong e τ₂)
subₖ-cong e (τ₁ `→ τ₂) = cong₂ _`→_ (subₖ-cong e τ₁) (subₖ-cong e τ₂)
subₖ-cong e (`∀ τ) = cong (`∀) (subₖ-cong (liftsₖ-cong e) τ)
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
subₖ-cong {σ₁ = σ₁} e ⦅ ρ ⦆ = {!!}

subRowₖ-cong eq [] = refl
subRowₖ-cong {σ₁ = σ₁} {σ₂} eq (τ ∷ ρ) rewrite 
  subₖ-cong eq τ | subRowₖ-cong eq ρ = refl

-------------------------------------------------------------------------------
-- Substitution respects identities

subₖ-id : ∀ (τ : Type Δ κ) → subₖ ` τ ≡ τ
subRowₖ-id : ∀ (ρ : SimpleRow Type Δ R[ κ ]) → subRowₖ ` ρ ≡ ρ

subₖ-id ε = refl
subₖ-id (` α) = refl
subₖ-id (`λ τ) = cong `λ (trans (subₖ-cong  {σ₁ = liftsₖ `} {σ₂ = `} liftsₖ-id τ) (subₖ-id τ))
subₖ-id (τ₁ · τ₂) = cong₂ _·_ (subₖ-id τ₁) (subₖ-id τ₂)
subₖ-id (τ₁ `→ τ₂) = cong₂ _`→_ (subₖ-id τ₁) (subₖ-id τ₂)
subₖ-id (`∀ τ) = cong (`∀) (trans (subₖ-cong liftsₖ-id τ) (subₖ-id τ))
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
subₖ-id ⦅ ρ ⦆ = {!!}

subRowₖ-id [] = refl
subRowₖ-id (τ ∷ ρ) rewrite 
  subₖ-id τ | subRowₖ-id ρ = refl

-------------------------------------------------------------------------------
-- subₖstitution and renₖaming commute

↻-subₖ-renₖ : ∀ {r : Renamingₖ Δ₁ Δ₂}{σ : Substitutionₖ Δ₂ Δ₃}  
                (τ : Type Δ₁ κ) → subₖ (σ ∘ r) τ ≡ subₖ σ (renₖ r τ)
↻-subRowₖ-renRowₖ : ∀ {r : Renamingₖ Δ₁ Δ₂}{σ : Substitutionₖ Δ₂ Δ₃}  
                (τ : SimpleRow Type Δ₁ R[ κ ]) → subRowₖ (σ ∘ r) τ ≡ subRowₖ σ (renRowₖ r τ)
↻-subₖ-renₖ {r = r} {σ} ε = refl
↻-subₖ-renₖ {r = r} {σ} (` α) = refl
↻-subₖ-renₖ {r = r} {σ} (`λ τ) = cong `λ (trans (subₖ-cong liftsₖ-liftₖ τ) (↻-subₖ-renₖ τ))
↻-subₖ-renₖ {r = r} {σ} (τ₁ · τ₂) = cong₂ _·_ (↻-subₖ-renₖ τ₁) (↻-subₖ-renₖ τ₂)
↻-subₖ-renₖ {r = r} {σ} (τ₁ `→ τ₂) = cong₂ _`→_ (↻-subₖ-renₖ τ₁) (↻-subₖ-renₖ τ₂) 
↻-subₖ-renₖ {r = r} {σ} (`∀ τ) = cong (`∀) (trans (subₖ-cong liftsₖ-liftₖ τ) (↻-subₖ-renₖ τ))
↻-subₖ-renₖ {r = r} {σ} (μ τ) = cong μ (↻-subₖ-renₖ τ)
↻-subₖ-renₖ {r = r} {σ} ((r₁ · r₂ ~ r₃) ⇒ τ) rewrite 
    ↻-subₖ-renₖ {r = r} {σ} r₁ 
  | ↻-subₖ-renₖ {r = r} {σ} r₂ 
  | ↻-subₖ-renₖ {r = r} {σ} r₃ 
  | ↻-subₖ-renₖ {r = r} {σ} τ = refl
↻-subₖ-renₖ {r = r} {σ} ((r₁ ≲ r₂) ⇒ τ) rewrite 
    ↻-subₖ-renₖ {r = r} {σ} r₁ 
  | ↻-subₖ-renₖ {r = r} {σ} r₂ 
  | ↻-subₖ-renₖ {r = r} {σ} τ = refl
↻-subₖ-renₖ {r = r} {σ} (lab l) = refl
↻-subₖ-renₖ {r = r} {σ} (τ₁ ▹ τ₂) = cong₂ _▹_ (↻-subₖ-renₖ τ₁) (↻-subₖ-renₖ τ₂) 
↻-subₖ-renₖ {r = r} {σ} ⌊ τ ⌋ = cong ⌊_⌋ (↻-subₖ-renₖ τ)
↻-subₖ-renₖ {r = r} {σ} Π = refl
↻-subₖ-renₖ {r = r} {σ} Σ = refl
↻-subₖ-renₖ {r = r} {σ} (τ₁ <$> τ₂) = cong₂ _<$>_ (↻-subₖ-renₖ τ₁) (↻-subₖ-renₖ τ₂) 
↻-subₖ-renₖ {r = r} {σ} ⦅ ρ ⦆ rewrite ↻-subRowₖ-renRowₖ {r = r} {σ = σ} ρ = refl

↻-subRowₖ-renRowₖ [] = refl
↻-subRowₖ-renRowₖ {r = r} {σ} (τ ∷ ρ) rewrite ↻-subₖ-renₖ {r = r} {σ} τ | ↻-subRowₖ-renRowₖ {r = r} {σ} ρ = refl 

↻-renₖ-subₖ         : ∀ {σ : Substitutionₖ Δ₁ Δ₂}{r : Renamingₖ Δ₂ Δ₃}(τ : Type Δ₁ κ) →
                    subₖ (renₖ r ∘ σ) τ ≡ renₖ r (subₖ σ τ)
↻-renRowₖ-subRowₖ   : ∀ {σ : Substitutionₖ Δ₁ Δ₂}{r : Renamingₖ Δ₂ Δ₃}(τ : SimpleRow Type Δ₁ R[ κ ]) →
                        subRowₖ (renₖ r ∘ σ) τ ≡ renRowₖ r (subRowₖ σ τ)
↻-renₖ-subₖ {σ = σ} {r} ε = refl
↻-renₖ-subₖ {σ = σ} {r} (` α) = refl
↻-renₖ-subₖ {σ = σ} {r} (`λ τ) = cong `λ (trans (subₖ-cong renₖ-liftₖ-liftsₖ τ) (↻-renₖ-subₖ τ))
↻-renₖ-subₖ {σ = σ} {r} (τ₁ · τ₂) = cong₂ _·_ (↻-renₖ-subₖ τ₁) (↻-renₖ-subₖ τ₂)
↻-renₖ-subₖ {σ = σ} {r} (τ₁ `→ τ₂) = cong₂ _`→_ (↻-renₖ-subₖ τ₁) (↻-renₖ-subₖ τ₂)
↻-renₖ-subₖ {σ = σ} {r} (`∀ τ) = cong (`∀) (trans (subₖ-cong renₖ-liftₖ-liftsₖ τ) (↻-renₖ-subₖ τ))
↻-renₖ-subₖ {σ = σ} {r} (μ τ) = cong μ (↻-renₖ-subₖ τ)
↻-renₖ-subₖ {σ = σ} {r} ((r₁ · r₂ ~ r₃) ⇒ τ) rewrite 
    ↻-renₖ-subₖ {σ = σ} {r} r₁ 
  | ↻-renₖ-subₖ {σ = σ} {r} r₂ 
  | ↻-renₖ-subₖ {σ = σ} {r} r₃ 
  | ↻-renₖ-subₖ {σ = σ} {r} τ = refl
↻-renₖ-subₖ {σ = σ} {r} ((r₁ ≲ r₂) ⇒ τ) rewrite 
    ↻-renₖ-subₖ {σ = σ} {r} r₁ 
  | ↻-renₖ-subₖ {σ = σ} {r} r₂ 
  | ↻-renₖ-subₖ {σ = σ} {r} τ = refl
↻-renₖ-subₖ {σ = σ} {r} (lab l) = refl
↻-renₖ-subₖ {σ = σ} {r} (τ₁ ▹ τ₂) = cong₂ _▹_ (↻-renₖ-subₖ τ₁) (↻-renₖ-subₖ τ₂)
↻-renₖ-subₖ {σ = σ} {r} ⌊ τ ⌋ = cong ⌊_⌋ (↻-renₖ-subₖ τ)
↻-renₖ-subₖ {σ = σ} {r} Π = refl
↻-renₖ-subₖ {σ = σ} {r} Σ = refl
↻-renₖ-subₖ {σ = σ} {r} (τ₁ <$> τ₂) = cong₂ _<$>_ (↻-renₖ-subₖ τ₁) (↻-renₖ-subₖ τ₂)
↻-renₖ-subₖ {σ = σ} {r} ⦅ ρ ⦆ rewrite ↻-renRowₖ-subRowₖ {σ = σ} {r} ρ = refl

↻-renRowₖ-subRowₖ {σ = σ} {r} [] = refl
↻-renRowₖ-subRowₖ {σ = σ} {r} (τ ∷ ρ) rewrite ↻-renₖ-subₖ {σ = σ} {r} τ | ↻-renRowₖ-subRowₖ {σ = σ} {r} ρ = refl

subₖ-weaken : ∀ (τ : Type Δ κ₁) (v : Type Δ κ₂) → 
             subₖ (extendₖ ` v) (renₖ S τ) ≡ τ 
subₖ-weaken τ v = trans (sym (↻-subₖ-renₖ {r = S} {σ = extendₖ ` v} τ)) (subₖ-id τ)

-------------------------------------------------------------------------------
-- Arrow functor law for liftsₖ & subₖ (needs commutativity of subₖ and renₖ)

liftsₖ-comp : ∀ (σ₁ : Substitutionₖ Δ₁ Δ₂)(σ₂ : Substitutionₖ Δ₂ Δ₃)
                (x : KVar (Δ₁ ,, κ₁) κ₂) → liftsₖ (subₖ σ₂ ∘ σ₁) x ≡ subₖ (liftsₖ σ₂) (liftsₖ σ₁ x)
liftsₖ-comp σ₁ σ₂ Z = refl
liftsₖ-comp σ₁ σ₂ (S x) = trans (sym (↻-renₖ-subₖ (σ₁ x))) (↻-subₖ-renₖ (σ₁ x)) 

subₖ-comp : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₂ Δ₃}
                (τ : Type Δ₁ κ) → subₖ (subₖ σ₂ ∘ σ₁) τ ≡ subₖ σ₂ (subₖ σ₁ τ)
subRowₖ-comp : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₂ Δ₃}
                (τ : SimpleRow Type Δ₁ R[ κ ]) → subRowₖ (subₖ σ₂ ∘ σ₁) τ ≡ subRowₖ σ₂ (subRowₖ σ₁ τ)
subₖ-comp ε = refl
subₖ-comp (` α) = refl
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} (`λ τ) = 
  cong `λ ((trans 
    (subₖ-cong (liftsₖ-comp σ₁ σ₂) τ) 
    (subₖ-comp {σ₁ = liftsₖ σ₁} {σ₂ = liftsₖ σ₂} τ)))
subₖ-comp (τ₁ · τ₂) = cong₂ _·_ (subₖ-comp τ₁) (subₖ-comp τ₂)
subₖ-comp (τ₁ `→ τ₂) = cong₂ _`→_ (subₖ-comp τ₁) (subₖ-comp τ₂)
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} (`∀ τ) =   
  cong (`∀) ((trans 
    (subₖ-cong (liftsₖ-comp σ₁ σ₂) τ) 
    (subₖ-comp {σ₁ = liftsₖ σ₁} {σ₂ = liftsₖ σ₂} τ)))
subₖ-comp (μ τ) = cong μ (subₖ-comp τ)
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} ((r₁ · r₂ ~ r₃) ⇒ τ) rewrite 
    subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₁ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₂ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₃ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} τ = refl
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} ((r₁ ≲ r₂) ⇒ τ) rewrite 
    subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₁ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₂ 
  | subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} τ = refl
subₖ-comp (lab l) = refl
subₖ-comp (τ₁ ▹ τ₂) = cong₂ _▹_ (subₖ-comp τ₁) (subₖ-comp τ₂)
subₖ-comp ⌊ τ ⌋ = cong ⌊_⌋ (subₖ-comp τ)
subₖ-comp Π = refl
subₖ-comp Σ = refl
subₖ-comp (τ₁ <$> τ₂) = cong₂ _<$>_ (subₖ-comp τ₁) (subₖ-comp τ₂)
subₖ-comp ⦅ ρ ⦆ = cong ⦅_⦆ (subRowₖ-comp ρ)

subRowₖ-comp [] = refl
subRowₖ-comp (τ ∷ ρ) = cong₂ _∷_ (subₖ-comp τ) (subRowₖ-comp ρ)


-------------------------------------------------------------------------------
-- 

renₖ-subₖ-id : ∀ (σ : Substitutionₖ Δ₁ Δ₂) (r : Renamingₖ Δ₂ Δ₃) 
                (τ :  Type Δ₂ κ) → renₖ r τ ≡ subₖ (` ∘ r) τ
renₖ-subₖ-id σ r τ = trans (cong (renₖ r) (sym (subₖ-id τ))) (trans (sym (↻-renₖ-subₖ τ)) refl )

-------------------------------------------------------------------------------
-- Renamingₖ commutes with β-reduction

↻-renₖ-β      : (r : Renamingₖ Δ₁ Δ₂) (τ₁ : Type (Δ₁ ,, κ₁) κ₂) (τ₂ : Type Δ₁ κ₁) → 
                renₖ r (τ₁ βₖ[ τ₂ ]) ≡ (renₖ (liftₖ r) τ₁) βₖ[ (renₖ r τ₂) ]  
↻-renₖ-β r τ₁ τ₂ = 
  trans 
    (sym (↻-renₖ-subₖ τ₁)) 
    (trans 
      (subₖ-cong (λ { Z → refl ; (S x) → refl }) τ₁) 
      (↻-subₖ-renₖ {r = liftₖ r} {extendₖ ` (renₖ r τ₂)} τ₁))                  

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
                        (sym (↻-subₖ-renₖ {r = S} {extendₖ ` (subₖ σ τ₂)} (σ x))) 
                        (subₖ-id (σ x)) }) τ₁) 
      (subₖ-comp {σ₁ = extendₖ ` τ₂} {σ} τ₁))
