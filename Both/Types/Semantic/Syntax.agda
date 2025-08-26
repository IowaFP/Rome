module Rome.Both.Types.Semantic.Syntax where

open import Data.Product using (_×_ ; _,_)
open import Rome.Both.Prelude
open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Renaming using (liftₖ ; Renamingₖ)

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming



--------------------------------------------------------------------------------
-- Semantic types (definition)

Row : Set → Set 
Row A = ∃[ n ](Fin n → Label × A)

--------------------------------------------------------------------------------
-- Ordered predicate on semantic rows

OrderedRow' : ∀ {A : Set} → (n : ℕ) → (Fin n → Label × A) → Set
OrderedRow' zero P = ⊤
OrderedRow' (suc zero) P = ⊤
OrderedRow' (suc (suc n)) P = (P fzero .fst < P (fsuc fzero) .fst)  × OrderedRow' (suc n) (P ∘ fsuc)

OrderedRow : ∀ {A} → Row A → Set
OrderedRow (n , P) = OrderedRow' n P

--------------------------------------------------------------------------------
-- Defining SemType Δ R[ κ ]

data RowType (Δ : KEnv ι₁) (𝒯 : ∀ {ι} → KEnv ι → Set) : Kind ι₂ → Set 
NotRow : ∀ {Δ : KEnv ι₁} {𝒯 : ∀ {ι} → KEnv ι → Set} → RowType Δ 𝒯 R[ κ ] → Set 
notRows? : ∀ {Δ : KEnv ι₁} {𝒯 : ∀ {ι} → KEnv ι → Set} → (ρ₂ ρ₁ : RowType Δ 𝒯 R[ κ ]) → Dec (NotRow ρ₂ or NotRow ρ₁)

data RowType Δ 𝒯 where
  _<$>_ : (φ : ∀ {ι} {Δ' : KEnv ι} → Renamingₖ Δ Δ' → NeutralType Δ' κ₁ → 𝒯 Δ') → 
          NeutralType Δ R[ κ₁ ] → 
          RowType Δ 𝒯 R[ κ₂ ]

  _▹_ : ∀ {ι'} {κ : Kind ι} → NeutralType Δ (L {ι'}) → 𝒯 Δ → RowType Δ 𝒯 R[ κ ]

  row : (ρ : Row (𝒯 Δ)) → OrderedRow ρ → RowType Δ 𝒯 R[ κ ]

  _∖_ : (ρ₂ ρ₁ : RowType Δ 𝒯 R[ κ ]) → {nr : NotRow ρ₂ or NotRow ρ₁} →
        RowType Δ 𝒯 R[ κ ]

NotRow (x ▹ x₁) = ⊤
NotRow (row ρ x) = ⊥
NotRow (ρ ∖ ρ₁) = ⊤
NotRow (φ <$> ρ) = ⊤

notRows? (x ▹ x₁) ρ₁ = yes (left tt)
notRows? (ρ₂ ∖ ρ₃) ρ₁ = yes (left tt)
notRows? (φ <$> ρ) ρ₁ = yes (left tt)
notRows? (row ρ x) (x₁ ▹ x₂) = yes (right tt)
notRows? (row ρ x) (row ρ₁ x₁) = no (λ { (left ()) ; (right ()) })
notRows? (row ρ x) (ρ₁ ∖ ρ₂) = yes (right tt)
notRows? (row ρ x) (φ <$> τ) = yes (right tt)

--------------------------------------------------------------------------------
-- Defining Semantic types

SemType : KEnv ι₁ → Kind ι₂ → Set
SemType Δ κ@(★ {ι}) = NormalType Δ κ
SemType Δ κ@(L)     = NormalType Δ κ
SemType Δ₁ (κ₁ `→ κ₂) = (∀ {ι}{Δ₂ : KEnv ι} → (r : Renamingₖ Δ₁ Δ₂) (v : SemType Δ₂ κ₁) → SemType Δ₂ κ₂)
SemType Δ R[ κ ] =  RowType Δ (λ Δ' → SemType Δ' κ) R[ κ ]  

--------------------------------------------------------------------------------
-- aliases

KripkeFunction : KEnv ι₁ → Kind ι₂ → Kind ι₃ → Set
KripkeFunctionNE : KEnv ι₁ → Kind ι₂ → Kind ι₃ → Set
KripkeFunction Δ₁ κ₁ κ₂ =  (∀ {ι}{Δ₂ : KEnv ι} → Renamingₖ Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)
KripkeFunctionNE Δ₁ κ₁ κ₂ =  (∀ {ι}{Δ₂ : KEnv ι} → Renamingₖ Δ₁ Δ₂ → NeutralType Δ₂ κ₁ → SemType Δ₂ κ₂)

--------------------------------------------------------------------------------
-- Truncating a row preserves ordering

ordered-cut : ∀ {n : ℕ} → {P : Fin (suc n) → Label × SemType Δ κ} → 
              OrderedRow (suc n , P) → OrderedRow (n , P ∘ fsuc)
ordered-cut {n = zero} oρ = tt
ordered-cut {n = suc n} oρ = oρ .snd


--------------------------------------------------------------------------------
-- Ordering is preserved by mapping

orderedMap₂ : ∀ {n} {P : Fin n → Label × SemType Δ κ₁} → 
               (f : SemType Δ κ₁ → SemType Δ κ₂) → 
               OrderedRow (n , P) → OrderedRow (n , map₂ f ∘ P)
orderedMap₂ {n = zero} {P} f oρ = tt
orderedMap₂ {n = suc zero} {P} f oρ = tt
orderedMap₂ {n = suc (suc n)} {P} f oρ = (oρ .fst) , (orderedMap₂ f (oρ .snd))

--------------------------------------------------------------------------------
-- Semantic row operators

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

