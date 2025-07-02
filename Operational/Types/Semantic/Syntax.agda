{-# OPTIONS --safe #-}
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

data RowType (Δ : KEnv) (𝒯 : KEnv → Set) : Kind → Set 
NotRow : ∀ {Δ : KEnv} {𝒯 : KEnv → Set} → RowType Δ 𝒯 R[ κ ] → Set 
notRows? : ∀ {Δ : KEnv} {𝒯 : KEnv → Set} → (ρ₂ ρ₁ : RowType Δ 𝒯 R[ κ ]) → Dec (NotRow ρ₂ or NotRow ρ₁)

data RowType Δ 𝒯 where

  _<$>_ : NormalType Δ (κ₁ `→ κ₂) → NeutralType Δ κ₁ → RowType Δ 𝒯 R[ κ₂ ]
  ne : NeutralType Δ R[ κ ] → RowType Δ 𝒯 R[ κ ]

  _▹_ : NeutralType Δ L → 𝒯 Δ → RowType Δ 𝒯 R[ κ ]

  row : (ρ : Row (𝒯 Δ)) → OrderedRow ρ → RowType Δ 𝒯 R[ κ ]

  _─_ : (ρ₂ ρ₁ : RowType Δ 𝒯 R[ κ ]) → {nr : NotRow ρ₂ or NotRow ρ₁} →
        RowType Δ 𝒯 R[ κ ]

NotRow (ne x) = ⊤
NotRow (x ▹ x₁) = ⊤
NotRow (row ρ x) = ⊥
NotRow (ρ ─ ρ₁) = ⊤
NotRow (φ <$> ρ) = ⊤

notRows? (ne x) ρ₁ = yes (left tt)
notRows? (x ▹ x₁) ρ₁ = yes (left tt)
notRows? (ρ₂ ─ ρ₃) ρ₁ = yes (left tt)
notRows? (φ <$> ρ) ρ₁ = yes (left tt)
notRows? (row ρ x) (ne x₁) = yes (right tt)
notRows? (row ρ x) (x₁ ▹ x₂) = yes (right tt)
notRows? (row ρ x) (row ρ₁ x₁) = no (λ { (left ()) ; (right ()) })
notRows? (row ρ x) (ρ₁ ─ ρ₂) = yes (right tt)
notRows? (row ρ x) (φ <$> τ) = yes (right tt)

SemType : KEnv → Kind → Set
SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = (∀ {Δ₂} → (r : Renamingₖ Δ₁ Δ₂) (v : SemType Δ₂ κ₁) → SemType Δ₂ κ₂)
SemType Δ R[ κ ] =  RowType Δ (λ Δ' → SemType Δ' κ) R[ κ ]  

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
-- Row operators

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

cong-subst-Row : ∀ {A : Set} 
                 {n m : ℕ} {ρ₁ ρ₂ : Fin n → A} {p₁ p₂ : n ≡ m} → ρ₁ ≡ ρ₂ → subst-Row p₁ ρ₁ ≡ subst-Row p₂ ρ₂ 
cong-subst-Row {p₁ = p₁} {p₂} refl rewrite UIP p₁ p₂ = refl

-- reduce-subst-Row : ∀ {A : Set} 
--                      {n m : ℕ} {ρ₁ ρ₂ : Fin n → A} {p₁ p₂ : n ≡ m} → ρ₁ ≡ ρ₂ → subst-Row p₁ ρ₁ ≡ ρ₁
-- reduce-subst-Row eq = ?



-- subst-Row-reduction : ∀ {n m} {A : Set} → 
--                       ∀ (p : suc n ≡  suc m) (f : Fin (suc n) → A) → 
--                       subst-Row p f fzero ≡ f fzero
-- subst-Row-reduction refl f = refl

-- subst-Row-reduction×₁ : ∀ {n m} {A B : Set} → 
--                       ∀ (p : suc n ≡ suc m) (f : Fin (suc n) → A × B) → 
--                       subst-Row p f fzero .fst ≡ f fzero .fst
-- subst-Row-reduction×₁ refl f = refl

-- subst-Row-reduction×₂ : ∀ {n m} {A B : Set} → 
--                       ∀ (p : suc n ≡ suc m) (f : Fin (suc n) → A × B) → 
--                       subst-Row p f fzero .snd ≡ f fzero .snd
-- subst-Row-reduction×₂ refl f = refl
