{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.Syntax where

open import Data.Product using (_×_ ; _,_)
open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (liftₖ ; Renamingₖ)

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming


--------------------------------------------------------------------------------
-- Semantic types (signatures)
  
SemType : KEnv → Kind → Set
KripkeFunction : KEnv → Kind → Kind → Set
KripkeFunction Δ₁ κ₁ κ₂ =  (∀ {Δ₂} → Renamingₖ Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)

--------------------------------------------------------------------------------
-- Semantic Rows

Row : KEnv → Kind → Set 
Row Δ ★ = ⊥ 
Row Δ L = ⊥ 
Row Δ (_ `→ _) = ⊥ 
Row Δ R[ κ ] = ∃[ n ](Fin n → Label × SemType Δ κ)

--------------------------------------------------------------------------------
-- Ordered predicate on semantic rows

OrderedRow' : (n : ℕ) → (Fin n → Label × SemType Δ κ) → Set
OrderedRow' zero P = ⊤
OrderedRow' (suc zero) P = ⊤
OrderedRow' (suc (suc n)) P = (P fzero .fst < P (fsuc fzero) .fst)  × OrderedRow' (suc n) (P ∘ fsuc)

OrderedRow : Row Δ R[ κ ] → Set
OrderedRow (n , P) = OrderedRow' n P

--------------------------------------------------------------------------------
-- Truncating a row preserves ordering

ordered-cut : ∀ {n : ℕ} → {P : Fin (suc n) → Label × SemType Δ κ} → 
              OrderedRow (suc n , P) → OrderedRow (n , P ∘ fsuc)
ordered-cut {n = zero} oρ = tt
ordered-cut {n = suc n} oρ = oρ .snd


--------------------------------------------------------------------------------
-- Ordering is preserved by mapping

orderedOverᵣ : ∀ {n} {P : Fin n → Label × SemType Δ κ₁} → 
               (f : SemType Δ κ₁ → SemType Δ κ₂) → 
               OrderedRow (n , P) → OrderedRow (n , overᵣ f ∘ P)
orderedOverᵣ {n = zero} {P} f oρ = tt
orderedOverᵣ {n = suc zero} {P} f oρ = tt
orderedOverᵣ {n = suc (suc n)} {P} f oρ = (oρ .fst) , (orderedOverᵣ f (oρ .snd))

--------------------------------------------------------------------------------
-- 

_⨾⨾_ :  Label × SemType Δ κ → Row Δ R[ κ ] → Row Δ R[ κ ]

τ ⨾⨾ (n , P) =  suc n , λ { fzero    → τ 
                          ; (fsuc x) → P x }

-- the empty row                                  
εV : Row Δ R[ κ ] 
εV = 0 , λ ()

-- Singleton rows
⁅_⁆ : Label × SemType Δ κ → Row Δ R[ κ ] 
⁅ τ ⁆ = 1 , λ { fzero → τ }

subst-Fin : ∀ {n m : ℕ} → (n ≡ m) → Fin n → Fin m
subst-Fin refl i = i

subst-Row : ∀ {A : Set} {n m : ℕ} → (n ≡ m) → (f : Fin n → A) → Fin m → A 
subst-Row refl f = f

subst-Row-reduction : ∀ {n m} {A : Set} → 
                      ∀ (p : suc n ≡  suc m) (f : Fin (suc n) → A) → 
                      subst-Row p f fzero ≡ f fzero
subst-Row-reduction refl f = refl

subst-Row-reduction×₁ : ∀ {n m} {A B : Set} → 
                      ∀ (p : suc n ≡ suc m) (f : Fin (suc n) → A × B) → 
                      subst-Row p f fzero .fst ≡ f fzero .fst
subst-Row-reduction×₁ refl f = refl

subst-Row-reduction×₂ : ∀ {n m} {A B : Set} → 
                      ∀ (p : suc n ≡ suc m) (f : Fin (suc n) → A × B) → 
                      subst-Row p f fzero .snd ≡ f fzero .snd
subst-Row-reduction×₂ refl f = refl

--------------------------------------------------------------------------------
-- Semantic types (definition)

SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = KripkeFunction Δ₁ κ₁ κ₂ 
SemType Δ R[ κ ] = NeutralType Δ R[ κ ] 
                   or (Σ[ ρ ∈ Row Δ R[ κ ] ] (OrderedRow {κ = κ} ρ))
                   or (SemType Δ L × SemType Δ κ)
