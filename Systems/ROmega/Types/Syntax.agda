{-# OPTIONS --safe #-}
module ROmega.Types.Syntax where

open import Agda.Primitive
open import Level

open import Data.String

open import ROmega.Kinds.Syntax

--------------------------------------------------------------------------------
-- infix OOP.

infixr 9 _`→_
infixr 9 _⇒_
infixr 10 _▹_
infixr 10 _R▹_
infixr 10 _≲_
infix 10 _·_~_
infixl 11 _·[_]

--------------------------------------------------------------------------------
-- Labels are Strings.

Label : Set
Label = String

--------------------------------------------------------------------------------
-- Private vars.

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ι ℓΔ ℓΦ ℓκ ℓκ₁ ℓκ₂ ℓκ₃ : Level
    κ : Kind ℓκ
    κ₁ : Kind ℓκ₁
    κ₂ : Kind ℓκ₂
    κ₃ : Kind ℓκ₃
    Δ : KEnv ℓΔ


--------------------------------------------------------------------------------
-- Kinding Environments, types, and predicates.
--
-- Kinding Environments, types, and predicates are tied up together, like so:
--   - Pred references Ty, KEnv
--   - Type   references KEnv
--   - KEnv references Pred

data Type : KEnv ℓ → Kind ι →  Set
data Pred (Δ : KEnv ℓ) (κ : Kind ι) : Set

data Pred Δ κ where
  _≲_ : (ρ₁ : Type Δ R[ κ ]) →
        (ρ₂ : Type Δ R[ κ ]) →
        Pred Δ κ

  _·_~_ : (ρ₁ : Type Δ R[ κ ]) →
          (ρ₂ : Type Δ R[ κ ]) →
          (ρ₃ : Type Δ R[ κ ]) →
          Pred Δ κ


--------------------------------------------------------------------------------
-- Type vars.
data TVar : KEnv ℓ → Kind ι → Set where
  Z : TVar (Δ , κ) κ
  S : TVar Δ κ₁ → TVar (Δ , κ₂) κ₁

--------------------------------------------------------------------------------
-- 
-- private
--   variable
--     Φ : PEnv Δ ℓΦ
--     π : Pred Δ κ

--------------------------------------------------------------------------------
-- Types.

data Type where
  ------------------------------------------------------------
  -- Base types (for mechanization).

  -- Unit (Mechanization.)
  U : 

         --------------
         Type Δ (★ ℓ)

  ------------------------------------------------------------
  -- System Fω.

  tvar : 

         TVar Δ κ →
         -----------
         Type Δ κ

  _`→_ :
          Type Δ (★ ℓ₁) → Type Δ (★ ℓ₂) →
          -----------------------------------
          Type Δ (★ (ℓ₁ ⊔ ℓ₂))

  `∀ :  
          (κ : Kind ℓκ) → Type (Δ , κ) (★ ℓ) →
          -------------------------------------
          Type Δ (★ (ℓ ⊔ (lsuc ℓκ)))

  `λ :  
          (κ₁ : Kind ℓκ₁) → Type (Δ , κ₁) κ₂ →
          -----------------------------------------
          Type Δ (κ₁ `→ κ₂)

  _·[_] : 
          Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
          -----------------------------
          Type Δ κ₂

  ------------------------------------------------------------
  -- Qualified types.

  _⇒_ : ∀ {κ : Kind ℓκ} →
         (π : Pred Δ κ) → Type Δ (★ ℓ) →
         --------------------------------
         Type Δ (★ (lsuc ℓκ ⊔ ℓ))

  ------------------------------------------------------------
  -- System Rω.

  -- Labels.
  lab : 
        Label →
        ----------
        Type Δ (L ℓ)

  -- singleton formation.
  _▹_ :
        Type Δ (L ℓ) → Type Δ κ →
        -------------------
        Type Δ κ

  -- Row singleton formation.
  _R▹_ : 
         Type Δ (L ℓ) → Type Δ κ →
         -------------------
         Type Δ R[ κ ]

  -- label constant formation.
  ⌊_⌋ : 
        Type Δ (L ℓ) →
        ----------
        Type Δ (★ ι)

  -- The empty record (mechanization only.)
  ∅ : 
  
      --------------
      Type Δ (★ ℓ)

  -- Record formation.
  Π : 
      Type Δ R[ ★ ℓ ] →
      -------------
      Type Δ (★ ℓ)

  -- Variant formation.
  Σ : 
      Type Δ R[ ★ ℓ ] →
      -------------
      Type Δ (★ ℓ)

  -- lift₁ (lifting a function argument to row kind).
  _·⌈_⌉ : ∀ {κ κ' : Kind ℓκ} → 
          Type Δ R[ κ `→ κ' ] → Type Δ κ →
          --------------------------------
          Type Δ R[ κ' ]

  -- lift₂ (lifting a function to row kind.)
  ⌈_⌉·_ : ∀ {κ κ' : Kind ℓκ} →
          Type Δ (κ `→ κ') → Type Δ R[ κ ] →
          --------------------------------
          Type Δ R[ κ' ]

