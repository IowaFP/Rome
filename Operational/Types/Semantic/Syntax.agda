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
-- Semantic types (definition)

Row : Set → Set 
Row A = ∃[ n ](Fin n → Label × A)

-- --------------------------------------------------------------------------------
-- -- Ordered predicate on semantic rows

OrderedRow' : ∀ {A : Set} → (n : ℕ) → (Fin n → Label × A) → Set
OrderedRow' zero P = ⊤
OrderedRow' (suc zero) P = ⊤
OrderedRow' (suc (suc n)) P = (P fzero .fst < P (fsuc fzero) .fst)  × OrderedRow' (suc n) (P ∘ fsuc)

OrderedRow : ∀ {A} → Row A → Set
OrderedRow (n , P) = OrderedRow' n P

data RowType (Δ : KEnv) (𝒯 : KEnv → Set) : Kind → Set where
  -- ne : NeutralType Δ R[ κ ] → RowType Δ 𝒯 R[ κ ]

  _▹_ : NeutralType Δ L → 𝒯 Δ → RowType Δ 𝒯 R[ κ ]

  row : (ρ : Row (𝒯 Δ)) → OrderedRow ρ → RowType Δ 𝒯 R[ κ ]

  _<$>_─_ : ∀ {κ₁} → 
  
            (F : ∀ {Δ'} → Renamingₖ Δ Δ' → NeutralType Δ' κ₁ → 𝒯 Δ') → 
            (ρ₂ : NeutralType Δ R[ κ₁ ]) (ρ₁ : RowType Δ 𝒯 R[ κ₂ ])→
            ----------------------------------------------
            RowType Δ 𝒯 R[ κ₂ ]

  -- _─₁_ : NeutralType Δ R[ κ ] → RowType Δ 𝒯 R[ κ ] → RowType Δ 𝒯 R[ κ ]
  -- _─₂_ : RowType Δ 𝒯 R[ κ ] → NeutralType Δ R[ κ ] → RowType Δ 𝒯 R[ κ ]

SemType : KEnv → Kind → Set
SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = (∀ {Δ₂} → (r : Renamingₖ Δ₁ Δ₂) (v : SemType Δ₂ κ₁) → SemType Δ₂ κ₂)
SemType Δ R[ κ ] =  RowType Δ (λ Δ' → SemType Δ' κ) R[ κ ]  

-- or NeutralType Δ R[ κ ] or NormalType Δ R[ κ ] -- (NeutralApp Δ R[ κ ] or NeutralApp Δ L × SemType Δ κ)
                   -- or (Σ[ ρ ∈ Row Δ R[ κ ] ] (OrderedRow {κ = κ} ρ))
                   -- or (SemType Δ R[ κ ] × SemType Δ R[ κ ])

--------------------------------------------------------------------------------
-- renames

KripkeFunction : KEnv → Kind → Kind → Set
KripkeFunction Δ₁ κ₁ κ₂ =  (∀ {Δ₂} → Renamingₖ Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)


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

_⨾⨾_ :  Label × SemType Δ κ → Row (SemType Δ κ) → Row (SemType Δ κ)

τ ⨾⨾ (n , P) =  suc n , λ { fzero    → τ 
                          ; (fsuc x) → P x }

-- the empty row                                  
εV : Row (SemType Δ κ)
εV = 0 , λ ()

-- Singleton rows
⁅_⁆ : Label × SemType Δ κ → Row (SemType Δ κ)
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
