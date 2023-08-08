{-# OPTIONS --safe #-}
module R2Mu.Types.Syntax where

open import Agda.Primitive
open import Level

open import Data.String
open import R2Mu.Kinds.Syntax

--------------------------------------------------------------------------------
-- infix OOP.

-- infixr 9 _`→_
-- infixr 9 _⇒_
-- infixr 10 _▹_
-- infixr 10 _R▹_
-- infixr 10 _≲_
-- infix 10 _·_~_
-- infixl 11 _·[_]

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

data Type : KEnv → Kind →  Set
data Pred (Δ : KEnv) (κ : Kind) : Set

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
data TVar : KEnv → Kind → Set where
  Z : ∀ {Δ : KEnv} {κ : Kind}
      → TVar (Δ , κ) κ
  S : ∀ {Δ : KEnv} {κ : Kind} {κ' : Kind}
      → TVar Δ κ → TVar (Δ , κ') κ

--------------------------------------------------------------------------------
-- Types.

data Type where
  ------------------------------------------------------------
  -- Base types (for mechanization).

  -- Unit (Mechanization.)
  U : ∀ {Δ : KEnv} →

         --------------
         Type Δ (★)

  ------------------------------------------------------------
  -- System Fω.

  tvar : ∀ {Δ : KEnv} {κ : Kind} →

         TVar Δ κ →
         -----------
         Type Δ κ

  _`→_ : ∀ {Δ : KEnv} →
          Type Δ (★) → Type Δ (★) →
          -----------------------------------
          Type Δ (★)

  `∀ :  ∀ {Δ : KEnv} →
          (κ : Kind) → Type (Δ , κ) (★) →
          -------------------------------------
          Type Δ (★)

  `λ :  ∀ {Δ : KEnv} {k : Kind} (κ¹ : Kind¹ k) {κ₂ : Kind} →
          Type (Δ , k) κ₂ →
          -----------------------------------------
          Type Δ (κ¹ `→ κ₂)

  _·[_] : ∀ {Δ : KEnv}{κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
          Type Δ (κ¹ `→ κ₂) → Type Δ κ →
          -----------------------------
          Type Δ κ₂

  ------------------------------------------------------------
  -- Recursion.

  -- LFP
  μ : {Δ : KEnv}{κ : Kind} {κ¹ : Kind¹ κ} →
          Type Δ (κ¹ `→ κ) → 
          Type Δ κ

  -- GFP
  ν : {Δ : KEnv}{κ : Kind} {κ¹ : Kind¹ κ} →
          Type Δ (κ¹ `→ κ) → 
          Type Δ κ

  ------------------------------------------------------------
  -- Qualified types.

  _⇒_ : ∀ {κ : Kind} {Δ : KEnv}
          → (π : Pred Δ κ) → Type Δ ★ →
         --------------------------------
         Type Δ ★

  ------------------------------------------------------------
  -- System Rω.

  -- Labels.
  lab : ∀ {Δ : KEnv} →
        Label →
        ----------
        Type Δ (L)

  -- singleton formation.
  _▹_ : ∀ {Δ : KEnv} {κ : Kind} →
        Type Δ (L) → Type Δ κ →
        -------------------
        Type Δ κ

  -- Row singleton formation.
  _R▹_ : ∀ {Δ : KEnv} {κ : Kind} →
         Type Δ L → Type Δ κ →
         -------------------
         Type Δ R[ κ ]

  -- label constant formation.
  ⌊_⌋ : ∀ {Δ : KEnv} →
        Type Δ (L) →
        ----------
        Type Δ (★)

  -- The empty record (mechanization only.)
  ∅ : ∀ {Δ : KEnv} →
  
      --------------
      Type Δ (★)

  -- Record formation.
  Π : ∀ {Δ : KEnv} →
      Type Δ R[ (★) ] →
      -------------
      Type Δ (★)

  -- Variant formation.
  Σ : ∀ {Δ : KEnv} →
      Type Δ R[ (★) ] →
      -------------
      Type Δ (★)

  -- lift₁ (lifting a function argument to row kind).
  _·⌈_⌉ : ∀ {Δ : KEnv}
            {κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
          Type Δ R[ κ¹ `→ κ₂ ] → Type Δ κ →
          --------------------------------
          Type Δ R[ κ₂ ]

  -- lift₂ (lifting a function to row kind.)
  ⌈_⌉·_ : ∀ {Δ : KEnv}
            {κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
          Type Δ (κ¹ `→ κ₂) → Type Δ R[ κ ] →
          --------------------------------
          Type Δ R[ κ₂ ]

