{-# OPTIONS --safe #-}
module Rome.Operational.Types.Properties.Substitution where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence.Relation

open import Rome.Operational.Types.Properties.Renaming


--------------------------------------------------------------------------------
-- Renaming commutes over Substitution

∈L-subRowₖ : ∀ (r : Substitutionₖ Δ₁ Δ₂) → {ρ : SimpleRow Type Δ₁ R[ κ ]} → 
                 (l : Label) → l ∈L ρ → l ∈L subRowₖ r ρ
∈L-subRowₖ r {ρ} l Here = Here
∈L-subRowₖ r {ρ} l (There ev) = There (∈L-subRowₖ r l ev)

subRowₖ-∈L : ∀ (r : Substitutionₖ Δ₁ Δ₂) → {ρ : SimpleRow Type Δ₁ R[ κ ]} → 
                 (l : Label) → l ∈L subRowₖ r ρ → l ∈L ρ
subRowₖ-∈L r {(l' , τ) ∷ ρ} l Here = Here
subRowₖ-∈L r {(l' , τ) ∷ ρ} l (There ev) = There (subRowₖ-∈L r l ev)

↻-subRowₖ-─s : ∀ (r : Substitutionₖ Δ₁ Δ₂) → {ρ₂ ρ₁ : SimpleRow Type Δ₁ R[ κ ]} → 
       subRowₖ r (ρ₂ ─s ρ₁) ≡ subRowₖ r ρ₂ ─s subRowₖ r ρ₁
↻-subRowₖ-─s r {[]} {ρ₁} = refl
↻-subRowₖ-─s r {(l , τ) ∷ ρ₂} {ρ₁} with l ∈L? ρ₁ | l ∈L? subRowₖ r ρ₁
... | yes p | yes q = ↻-subRowₖ-─s r {ρ₂} {ρ₁}
... | yes  p | no q = ⊥-elim (q (∈L-subRowₖ r l p))
... | no  p | yes q = ⊥-elim (p (subRowₖ-∈L r l q))
... | no  p | no q = cong ((l , subₖ r τ) ∷_) (↻-subRowₖ-─s r {ρ₂} {ρ₁})

-------------------------------------------------------------------------------
-- Functor laws for lifting

liftsₖ-cong : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
              (∀ {κ} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (x : TVar (Δ₁ ,, κ₁) κ₂) → liftsₖ σ₁ x ≡ liftsₖ σ₂ x
liftsₖ-cong e Z = refl
liftsₖ-cong e (S x) = cong (renₖ S) (e x)              

liftsₖ-id    : ∀ (x : TVar (Δ ,, κ₁) κ₂) → liftsₖ ` x ≡ ` x 
liftsₖ-id Z = refl
liftsₖ-id (S x) = refl

-- Fusion for liftsₖ and lift
liftsₖ-liftₖ      : ∀ {ρ : Renamingₖ Δ₁ Δ₂}{σ : Substitutionₖ Δ₂ Δ₃} 
                    (x : TVar (Δ₁ ,, κ₁) κ₂) → 
                    liftsₖ (σ ∘ ρ) x ≡ liftsₖ σ (liftₖ ρ x)
liftsₖ-liftₖ Z = refl
liftsₖ-liftₖ (S x) = refl

renₖ-liftₖ-liftsₖ : ∀ {σ : Substitutionₖ Δ₁ Δ₂}{ρ : Renamingₖ Δ₂ Δ₃}(x : TVar (Δ₁ ,, κ₁) κ₂) → 
                    liftsₖ (renₖ ρ ∘ σ) x ≡ renₖ (liftₖ ρ) (liftsₖ σ x)
renₖ-liftₖ-liftsₖ Z = refl
renₖ-liftₖ-liftsₖ {σ = σ} {ρ} (S x) = trans (sym (renₖ-comp ρ S (σ x))) (renₖ-comp S (liftₖ ρ) (σ x))                    

-------------------------------------------------------------------------------
-- Substitution respects congruence

subₖ-cong : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
              (∀ {κ} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (τ : Type Δ₁ κ) → subₖ σ₁ τ ≡ subₖ σ₂ τ
subRowₖ-cong : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₁ Δ₂} →
              (∀ {κ} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (ρ : SimpleRow Type Δ₁ R[ κ ]) → subRowₖ σ₁ ρ ≡ subRowₖ σ₂ ρ

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
subₖ-cong e ⌊ τ ⌋ = cong ⌊_⌋ (subₖ-cong e τ)
subₖ-cong e Π = refl
subₖ-cong e Σ = refl
subₖ-cong e (τ <$> τ₁) = cong₂ _<$>_ (subₖ-cong e τ) (subₖ-cong e τ₁)
subₖ-cong e (ρ₂ ─ ρ₁) = cong₂ _─_ (subₖ-cong e ρ₂) (subₖ-cong e ρ₁)
subₖ-cong {σ₁ = σ₁} e (⦅ ρ ⦆ oρ) = cong-SimpleRow (subRowₖ-cong e ρ)
subₖ-cong {σ₁ = σ₁} e (l ▹ τ) = cong₂ _▹_ (subₖ-cong e l) (subₖ-cong e τ)

subRowₖ-cong eq [] = refl
subRowₖ-cong {σ₁ = σ₁} {σ₂} eq ((l , τ) ∷ ρ) = cong₂ _∷_ (cong₂ _,_ refl (subₖ-cong eq τ)) (subRowₖ-cong eq ρ)

-------------------------------------------------------------------------------
-- Substitution respects identities

subₖ-id : ∀ (τ : Type Δ κ) → subₖ ` τ ≡ τ
subRowₖ-id : ∀ (ρ : SimpleRow Type Δ R[ κ ]) → subRowₖ ` ρ ≡ ρ

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
subₖ-id ⌊ τ ⌋ = cong ⌊_⌋ (subₖ-id τ)
subₖ-id Π = refl
subₖ-id Σ = refl
subₖ-id (τ₁ <$> τ₂) = cong₂ _<$>_ (subₖ-id τ₁) (subₖ-id τ₂)
subₖ-id (⦅ ρ ⦆ oρ) = cong-SimpleRow (subRowₖ-id ρ)
subₖ-id (ρ₂ ─ ρ₁) = cong₂ _─_ (subₖ-id ρ₂) (subₖ-id ρ₁)
subₖ-id (l ▹ τ) = cong₂ _▹_ (subₖ-id l) (subₖ-id τ)

subRowₖ-id [] = refl
subRowₖ-id ((l , τ) ∷ ρ) = cong₂ _∷_ (cong₂ _,_ refl (subₖ-id τ)) (subRowₖ-id ρ)

-------------------------------------------------------------------------------
-- subₖstitution and renₖaming commute

↻-subₖ-renₖ : ∀ {r : Renamingₖ Δ₁ Δ₂}{σ : Substitutionₖ Δ₂ Δ₃}  
                (τ : Type Δ₁ κ) → subₖ (σ ∘ r) τ ≡ subₖ σ (renₖ r τ)
↻-subRowₖ-renRowₖ : ∀ {r : Renamingₖ Δ₁ Δ₂}{σ : Substitutionₖ Δ₂ Δ₃}  
                (τ : SimpleRow Type Δ₁ R[ κ ]) → subRowₖ (σ ∘ r) τ ≡ subRowₖ σ (renRowₖ r τ)

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
↻-subₖ-renₖ {r = r} {σ} ⌊ τ ⌋ = cong ⌊_⌋ (↻-subₖ-renₖ τ)
↻-subₖ-renₖ {r = r} {σ} Π = refl
↻-subₖ-renₖ {r = r} {σ} Σ = refl
↻-subₖ-renₖ {r = r} {σ} (τ₁ <$> τ₂) = cong₂ _<$>_ (↻-subₖ-renₖ τ₁) (↻-subₖ-renₖ τ₂) 
↻-subₖ-renₖ {r = r} {σ} (ρ₂ ─ ρ₁) = cong₂ _─_ (↻-subₖ-renₖ ρ₂) (↻-subₖ-renₖ ρ₁)
↻-subₖ-renₖ {r = r} {σ} (⦅ ρ ⦆ oρ) = cong-SimpleRow (↻-subRowₖ-renRowₖ ρ)
↻-subₖ-renₖ {r = r} {σ} (l ▹ τ) = cong₂ _▹_ (↻-subₖ-renₖ l) (↻-subₖ-renₖ τ)

↻-subRowₖ-renRowₖ [] = refl
↻-subRowₖ-renRowₖ {r = r} {σ} ((l , τ) ∷ ρ) = cong₂ _∷_ (cong₂ _,_ refl (↻-subₖ-renₖ τ)) (↻-subRowₖ-renRowₖ ρ)

↻-renₖ-subₖ         : ∀ {σ : Substitutionₖ Δ₁ Δ₂}{r : Renamingₖ Δ₂ Δ₃}(τ : Type Δ₁ κ) →
                    subₖ (renₖ r ∘ σ) τ ≡ renₖ r (subₖ σ τ)
↻-renRowₖ-subRowₖ   : ∀ {σ : Substitutionₖ Δ₁ Δ₂}{r : Renamingₖ Δ₂ Δ₃}(τ : SimpleRow Type Δ₁ R[ κ ]) →
                        subRowₖ (renₖ r ∘ σ) τ ≡ renRowₖ r (subRowₖ σ τ)

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
↻-renₖ-subₖ {σ = σ} {r} (ρ₂ ─ ρ₁) = cong₂ _─_ (↻-renₖ-subₖ ρ₂) (↻-renₖ-subₖ ρ₁)
↻-renₖ-subₖ {σ = σ} {r} (⦅ ρ ⦆ oρ) = cong-SimpleRow (↻-renRowₖ-subRowₖ {σ = σ} {r} ρ)

↻-renRowₖ-subRowₖ {σ = σ} {r} [] = refl
↻-renRowₖ-subRowₖ {σ = σ} {r} ((l , τ) ∷ ρ) = cong₂ _∷_ (cong₂ _,_ refl (↻-renₖ-subₖ τ)) (↻-renRowₖ-subRowₖ ρ)

subₖ-weaken : ∀ (τ : Type Δ κ₁) (v : Type Δ κ₂) → 
             subₖ (extendₖ ` v) (renₖ S τ) ≡ τ 
subₖ-weaken τ v = trans (sym (↻-subₖ-renₖ {r = S} {σ = extendₖ ` v} τ)) (subₖ-id τ)

-------------------------------------------------------------------------------
-- Arrow functor law for liftsₖ & subₖ (needs commutativity of subₖ and renₖ)

liftsₖ-comp : ∀ (σ₁ : Substitutionₖ Δ₁ Δ₂)(σ₂ : Substitutionₖ Δ₂ Δ₃)
                (x : TVar (Δ₁ ,, κ₁) κ₂) → liftsₖ (subₖ σ₂ ∘ σ₁) x ≡ subₖ (liftsₖ σ₂) (liftsₖ σ₁ x)
liftsₖ-comp σ₁ σ₂ Z = refl
liftsₖ-comp σ₁ σ₂ (S x) = trans (sym (↻-renₖ-subₖ (σ₁ x))) (↻-subₖ-renₖ (σ₁ x)) 

subₖ-comp : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₂ Δ₃}
                (τ : Type Δ₁ κ) → subₖ (subₖ σ₂ ∘ σ₁) τ ≡ subₖ σ₂ (subₖ σ₁ τ)
subRowₖ-comp : ∀ {σ₁ : Substitutionₖ Δ₁ Δ₂}{σ₂ : Substitutionₖ Δ₂ Δ₃}
                (τ : SimpleRow Type Δ₁ R[ κ ]) → subRowₖ (subₖ σ₂ ∘ σ₁) τ ≡ subRowₖ σ₂ (subRowₖ σ₁ τ)

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
subₖ-comp ⌊ τ ⌋ = cong ⌊_⌋ (subₖ-comp τ)
subₖ-comp Π = refl
subₖ-comp Σ = refl
subₖ-comp (τ₁ <$> τ₂) = cong₂ _<$>_ (subₖ-comp τ₁) (subₖ-comp τ₂)
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} (⦅ ρ ⦆ oρ) = cong-SimpleRow (subRowₖ-comp {σ₁ = σ₁} {σ₂} ρ)
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} (ρ₂ ─ ρ₁) = cong₂ _─_ (subₖ-comp ρ₂) (subₖ-comp ρ₁)
subₖ-comp {σ₁ = σ₁} {σ₂ = σ₂} (l ▹ τ) = cong₂ _▹_ (subₖ-comp l) (subₖ-comp τ)

subRowₖ-comp [] = refl
subRowₖ-comp ((l , τ) ∷ ρ) = cong₂ _∷_ (cong₂ _,_ refl (subₖ-comp τ)) (subRowₖ-comp ρ)

-------------------------------------------------------------------------------
-- lifting commutes with weakening

↻-liftsₖ-weaken : ∀ {κ'} (σ : Substitutionₖ Δ₁ Δ₂) (τ : Type Δ₁ κ) → 
                subₖ (liftsₖ {κ = κ'} σ) (renₖ S τ) ≡ renₖ S (subₖ σ τ)
↻-liftsₖ-weaken {κ' = κ'} σ τ = 
  trans 
    (sym (↻-subₖ-renₖ {r = S} {σ = liftsₖ σ} τ)) 
    (↻-renₖ-subₖ {σ = σ} {r = S} τ)


-------------------------------------------------------------------------------
-- Renaming by r is equivalent to substitution by the identity sub composed with r 

renₖ-subₖ-id : ∀ (r : Renamingₖ Δ₂ Δ₃) 
                (τ :  Type Δ₂ κ) → renₖ r τ ≡ subₖ (` ∘ r) τ
renₖ-subₖ-id r τ = trans (cong (renₖ r) (sym (subₖ-id τ))) (trans (sym (↻-renₖ-subₖ τ)) refl )

-------------------------------------------------------------------------------
-- Extension of a weakening over a lifting is just the renaming

subₖ-weaken-over-lift : ∀ (r : Renamingₖ Δ₁ Δ₂) (τ : Type Δ₁ κ₁) (v : Type Δ₂ κ₂) → 
                        renₖ r τ ≡ subₖ (extendₖ ` v) (renₖ (liftₖ r) (weakenₖ τ))
subₖ-weaken-over-lift r τ v = 
  (trans 
    (trans 
      (renₖ-subₖ-id r τ)
      (↻-subₖ-renₖ τ))
    (↻-subₖ-renₖ (weakenₖ τ)))

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

--------------------------------------------------------------------------------
-- Substitution commutes with mapping over rows

↻-sub-map : ∀ (σ : Substitutionₖ Δ₁ Δ₂) (F : Type Δ₁ (κ₁ `→ κ₂)) (ρ : SimpleRow Type Δ₁ R[ κ₁ ]) → 
              map (map₂ (subₖ σ F ·_)) (subRowₖ σ ρ) ≡ subRowₖ σ (map (map₂ (F ·_)) ρ)
↻-sub-map σ F [] = refl 
↻-sub-map σ F (x ∷ ρ) = cong (_ ∷_) (↻-sub-map σ F ρ)

--------------------------------------------------------------------------------
-- An empty substitution behaves as the identity

emptySub : ∀ (τ : Type ∅ κ) → (σ : Substitutionₖ ∅ ∅) → 
                subₖ σ τ ≡ τ
emptySub τ σ = trans (subₖ-cong {σ₁ = σ} {σ₂ = `} (λ { () }) τ) (subₖ-id τ)

realEmptySub : ∀ (τ : Type ∅ κ) → 
               subₖ (λ ()) τ ≡ τ 
realEmptySub τ = trans (subₖ-cong {σ₁ = λ ()} {σ₂ = `} (λ { () }) τ) (subₖ-id τ)
