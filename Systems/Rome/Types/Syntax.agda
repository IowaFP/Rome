{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Types.Syntax where

open import Preludes.Level
open import Preludes.Data

open import Rome.GVars.Kinds
open import Rome.Kinds.Syntax


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
-- Kinding Environments, types, and predicates.
--
-- Kinding Environments, types, and predicates are tied up together, like so:
--   - Pred references Ty, KEnv
--   - Type   references KEnv
--   - KEnv references Pred


data Type : KEnv ℓ → Kind ι →  Set
data Pred (Δ : KEnv ℓ) : (κ : Kind ι) → Set

data Pred Δ where
  _≲_ : ∀ {κ : Kind ι} → 
          (ρ₁ : Type Δ R[ κ ]) →
          (ρ₂ : Type Δ R[ κ ]) →
          Pred Δ κ

  _·_~_ : ∀ {κ : Kind ι} → 
            (ρ₁ : Type Δ R[ κ ]) →
            (ρ₂ : Type Δ R[ κ ]) →
            (ρ₃ : Type Δ R[ κ ]) →
            Pred Δ κ

--------------------------------------------------------------------------------
-- Type vars.
data TVar : KEnv ℓ → Kind ι → Set where
  Z : TVar (Δ ، κ) κ
  S : TVar Δ κ₁ → TVar (Δ ، κ₂) κ₁

S² : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂) κ
S³ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃) κ
S⁴ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄) κ
S⁵ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄ ، κ₅) κ

S² x = S (S x) 
S³ x = S (S² x)
S⁴ x = S (S³ x)
S⁵ x = S (S⁴ x)

--------------------------------------------------------------------------------
-- Types.

data Type where

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

  _`↪_ :
          Type Δ (★ ℓ₁) → Type Δ (★ ℓ₂) →
          -----------------------------------
          Type Δ (★ (lsuc ℓ₁ ⊔ ℓ₂))

  `∀ :  
          (κ : Kind ℓκ) → Type (Δ ، κ) (★ ℓ) →
          -------------------------------------
          Type Δ (★ (ℓ ⊔ (lsuc ℓκ)))

  `λ :  
          (κ₁ : Kind ℓκ₁) → Type (Δ ، κ₁) κ₂ →
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

  ε : Type Δ R[ κ ]

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
        Type Δ (★ ℓ)

  -- Record formation.
  Π : 
      Type Δ R[ κ ] →
      -------------
      Type Δ  κ 

  -- Variant formation.
  Σ : 
      Type Δ R[ κ ] →
      -------------
      Type Δ κ

  -- lift₁ (lifting a function argument to row kind).
  _·⌈_⌉ : ∀ {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} → 
          Type Δ R[ κ₁ `→ κ₂ ] → Type Δ κ₁ →
          --------------------------------
          Type Δ R[ κ₂ ]

  -- lift₂ (lifting a function to row kind.)
  ⌈_⌉·_ : ∀ {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} →
          Type Δ (κ₁ `→ κ₂) → Type Δ R[ κ₁ ] →
          --------------------------------
          Type Δ R[ κ₂ ]

  ------------------------------------------------------------
  -- System Rωμ.

  -- μ formation.
  μ : ∀ {ℓ} →
      (τ : Type Δ ((★ ℓ) `→ (★ ℓ))) →
      -----------------------------------------------
      Type Δ (★ ℓ)

--------------------------------------------------------------------------------
--



