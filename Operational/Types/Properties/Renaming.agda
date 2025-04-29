module Rome.Operational.Types.Properties.Renaming where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars
open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Equivalence

--------------------------------------------------------------------------------
-- ↑ing respects congruence, identities, and composition.
--

liftₖ-id : ∀ (x : KVar (Δ ,, κ₂) κ₁) → liftₖ id x ≡ x
liftₖ-id Z = refl
liftₖ-id (S x) = refl

liftₖ-comp : ∀ (r₁ : Renamingₖ Δ₁ Δ₂) (r₂ : Renamingₖ Δ₂ Δ₃) → 
            ∀ (x : KVar (Δ₁ ,, κ₂) κ₁) → liftₖ (r₂ ∘ r₁) x ≡ liftₖ r₂ (liftₖ r₁ x)
liftₖ-comp r₁ r₂ Z = refl
liftₖ-comp r₁ r₂ (S x) = refl

liftₖ-cong : ∀ {r₁ r₂ : Renamingₖ Δ₁ Δ₂} → (r₁ ≈ r₂) → 
              (x : KVar (Δ₁ ,, κ₂) κ) → liftₖ r₁ x ≡ liftₖ r₂ x
liftₖ-cong eq Z = refl
liftₖ-cong eq (S x) = cong S (eq x)


--------------------------------------------------------------------------------
-- Renamingₖ respects congruence

renₖ-cong :  ∀ {r₁ r₂ : Renamingₖ Δ₁ Δ₂} →  r₁ ≈ r₂ → 
              (τ : Type Δ₁ κ) → renₖ r₁ τ ≡ renₖ r₂ τ
renRowₖ-cong : ∀ {r₁ r₂ : Renamingₖ Δ₁ Δ₂} →  r₁ ≈ r₂ → 
                  (xs : SimpleRow Type Δ₁ R[ κ ]) → renRowₖ r₁ xs ≡ renRowₖ r₂ xs
renPredₖ-cong : ∀ {r₁ r₂ : Renamingₖ Δ₁ Δ₂} →  r₁ ≈ r₂ → 
                  (π : Pred Type Δ₁ R[ κ ]) → renPredₖ r₁ π ≡ renPredₖ r₂ π
                  
renₖ-cong eq (` x) rewrite eq x = refl
renₖ-cong eq (`λ τ) rewrite renₖ-cong (liftₖ-cong eq) τ = refl 
renₖ-cong eq (τ₁ · τ₂) rewrite renₖ-cong eq τ₁ | renₖ-cong eq τ₂ = refl
renₖ-cong eq (τ₁ `→ τ₂) rewrite renₖ-cong eq τ₁ | renₖ-cong eq τ₂ = refl
renₖ-cong eq (π ⇒ τ) rewrite renPredₖ-cong eq π | renₖ-cong eq τ = refl
renₖ-cong eq (`∀ τ) rewrite renₖ-cong (liftₖ-cong eq) τ = refl 
renₖ-cong eq (μ F) rewrite renₖ-cong eq F = refl 
renₖ-cong eq Π = refl 
renₖ-cong eq Σ = refl 
renₖ-cong eq (lab _) = refl
-- renₖ-cong eq (l ▹ τ) rewrite renₖ-cong eq l | renₖ-cong eq τ = refl
renₖ-cong eq ⌊ τ ⌋ rewrite renₖ-cong eq τ = refl
renₖ-cong eq (f <$> a) rewrite renₖ-cong eq f | renₖ-cong eq a = refl
renₖ-cong {r₁ = r₁} {r₂} eq (⦅ ρ ⦆ oρ) = cong-SimpleRow (renRowₖ-cong eq ρ) 
renPredₖ-cong eq (r₁ · r₂ ~ r₃) 
  rewrite renₖ-cong eq r₁ | renₖ-cong eq r₂ | renₖ-cong eq r₃ = refl
renPredₖ-cong eq (r₁ ≲ r₂) 
  rewrite renₖ-cong eq r₁ | renₖ-cong eq r₂ = refl

renRowₖ-cong eq [] = refl
renRowₖ-cong eq ((l , τ) ∷ xs) = cong₂ _∷_ (cong₂ _,_ (renₖ-cong eq l)  (renₖ-cong eq τ)) (renRowₖ-cong eq xs)

-- --------------------------------------------------------------------------------
-- -- Renamingₖ respects identities.

renₖ-id : ∀ (τ : Type Δ κ) → renₖ id τ ≡ τ
renPredₖ-id : ∀ (π : Pred Type Δ R[ κ ]) → renPredₖ id π ≡ π
renRowₖ-id : ∀ (ρ : SimpleRow Type Δ R[ κ ]) → renRowₖ id ρ ≡ ρ

renₖ-id (` x) = refl
renₖ-id (`λ τ) rewrite renₖ-cong liftₖ-id τ | renₖ-id τ = refl 
renₖ-id (τ₁ · τ₂) rewrite renₖ-id τ₁ | renₖ-id τ₂ = refl
renₖ-id (τ₁ `→ τ₂) rewrite renₖ-id τ₁ | renₖ-id τ₂ = refl
renₖ-id (π ⇒ r) rewrite renPredₖ-id π | renₖ-id r  = refl
renₖ-id (`∀ τ) rewrite renₖ-cong liftₖ-id τ | renₖ-id τ = refl
renₖ-id (μ F) rewrite renₖ-id F = refl
renₖ-id Π = refl
renₖ-id Σ = refl
renₖ-id (lab _) = refl
-- renₖ-id (l ▹ τ) rewrite renₖ-id l | renₖ-id τ = refl
renₖ-id ⌊ τ ⌋ rewrite renₖ-id τ = refl
renₖ-id (f <$> a) rewrite renₖ-id f | renₖ-id a = refl
renₖ-id (⦅ ρ ⦆ oρ)  =  cong-SimpleRow (renRowₖ-id ρ)
renPredₖ-id (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₖ-id ρ₁ | renₖ-id ρ₂ | renₖ-id ρ₃ = refl
renPredₖ-id (ρ₁ ≲ ρ₂)
  rewrite renₖ-id ρ₁ | renₖ-id ρ₂ = refl 

renRowₖ-id [] = refl
renRowₖ-id ((l , τ) ∷ xs) = cong₂ _∷_ (cong₂ _,_ (renₖ-id l) (renₖ-id τ)) (renRowₖ-id xs)

-- --------------------------------------------------------------------------------
-- -- Renamingₖ respects composition.

renₖ-comp : ∀ (r₁ : Renamingₖ Δ₁ Δ₂) (r₂ : Renamingₖ Δ₂ Δ₃) → 
           ∀ (τ : Type Δ₁ κ) → renₖ (r₂ ∘ r₁) τ ≡ renₖ r₂ (renₖ r₁ τ)
renPredₖ-comp : ∀ (r₁ : Renamingₖ Δ₁ Δ₂) (r₂ : Renamingₖ Δ₂ Δ₃) → 
                ∀ (π : Pred Type Δ₁ R[ κ ]) → renPredₖ (r₂ ∘ r₁) π ≡ renPredₖ r₂ (renPredₖ r₁ π)
renRowₖ-comp : ∀ (r₁ : Renamingₖ Δ₁ Δ₂) (r₂ : Renamingₖ Δ₂ Δ₃) → 
                ∀ (ρ : SimpleRow Type Δ₁ R[ κ ]) → renRowₖ (r₂ ∘ r₁) ρ ≡ renRowₖ r₂ (renRowₖ r₁ ρ)

renₖ-comp r₁ r₂ (` x) = refl
renₖ-comp r₁ r₂ Π = refl
renₖ-comp r₁ r₂ Σ = refl
renₖ-comp r₁ r₂ (`λ τ)  rewrite
  trans (renₖ-cong (liftₖ-comp r₁ r₂) τ) (renₖ-comp (liftₖ r₁) (liftₖ r₂) τ) = refl
renₖ-comp r₁ r₂ (τ₁ · τ₂) rewrite
    renₖ-comp r₁ r₂ τ₁ 
  | renₖ-comp r₁ r₂ τ₂ = refl
renₖ-comp r₁ r₂ (τ₁ `→ τ₂) rewrite
    renₖ-comp r₁ r₂ τ₁ 
  | renₖ-comp r₁ r₂ τ₂ = refl
renₖ-comp r₁ r₂ (`∀ τ) rewrite
  (trans (renₖ-cong (liftₖ-comp r₁ r₂) τ) (renₖ-comp (liftₖ r₁) (liftₖ r₂) τ)) = refl
renₖ-comp r₁ r₂ (μ F) rewrite
  renₖ-comp r₁ r₂ F = refl
renₖ-comp r₁ r₂ (lab _) = refl
-- renₖ-comp r₁ r₂ (l ▹ τ) rewrite renₖ-comp r₁ r₂ l | renₖ-comp r₁ r₂ τ = refl
renₖ-comp r₁ r₂ ⌊ τ ⌋ rewrite
    renₖ-comp r₁ r₂ τ = refl
renₖ-comp r₁ r₂ (f <$> a) rewrite renₖ-comp r₁ r₂ f | renₖ-comp r₁ r₂ a = refl
renₖ-comp r₁ r₂ (π ⇒ τ) rewrite renPredₖ-comp r₁ r₂ π | renₖ-comp r₁ r₂ τ = refl
renₖ-comp r₁ r₂ (⦅ ρ ⦆ oρ) = cong-SimpleRow (renRowₖ-comp r₁ r₂ ρ) 

renPredₖ-comp r r' (r₁ · r₂ ~ r₃) 
  rewrite renₖ-comp r r' r₁ | renₖ-comp r r' r₂ | renₖ-comp r r' r₃ = refl
renPredₖ-comp r r' (r₁ ≲ r₂)
  rewrite renₖ-comp r r' r₁ | renₖ-comp r r' r₂ = refl 

renRowₖ-comp r₁ r₂ [] = refl
renRowₖ-comp r₁ r₂ ((l , τ) ∷ r) = cong₂ _∷_ (cong₂ _,_ (renₖ-comp r₁ r₂ l) (renₖ-comp r₁ r₂ τ)) (renRowₖ-comp r₁ r₂ r)

↻-liftₖ-weaken : ∀ {κ'} (r : Renamingₖ Δ₁ Δ₂) (τ : Type Δ₁ κ) → 
                renₖ (liftₖ {κ = κ'} r) (renₖ S τ) ≡ renₖ S (renₖ r τ)
↻-liftₖ-weaken {κ' = κ'} r τ rewrite sym (renₖ-comp (S {κ₂ = κ'}) (liftₖ r) τ) | renₖ-comp r (S {κ₂ = κ'}) τ = refl
    

--------------------------------------------------------------------------------
-- Renaming commutes with mapping over rows

↻-ren-map : ∀ (r : Renamingₖ Δ₁ Δ₂) (F : Type Δ₁ (κ₁ `→ κ₂)) (ρ : SimpleRow Type Δ₁ R[ κ₁ ]) → 
              map (overᵣ (renₖ r F ·_)) (renRowₖ r ρ) ≡ renRowₖ r (map (overᵣ (F ·_)) ρ)
↻-ren-map φ F [] = refl 
↻-ren-map φ F (x ∷ ρ) = cong (_ ∷_) (↻-ren-map φ F ρ)
