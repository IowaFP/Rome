{-# OPTIONS --safe #-}
module R2Mu.Types.Syntax where

open import Agda.Primitive
open import Level

open import Data.String

open import R2Mu.Kinds.Syntax
import R2Mu.Types.Pre as Pre

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

data Type : KEnv → Pre.Type → Kind →  Set
data Pred (Δ : KEnv) (_ : Pre.Pred) (κ : Kind) : Set

private
  variable
    π₁ π₂ : Pre.Type
    τ₁ τ₂ τ₃ : Pre.Type

data Pred Δ π κ where
  _≲_ : (ρ₁ : Type Δ τ₁ R[ κ ]) →
        (ρ₂ : Type Δ τ₂ R[ κ ]) →
        Pred Δ π κ

  _·_~_ : (ρ₁ : Type Δ τ₁ R[ κ ]) →
          (ρ₂ : Type Δ τ₂ R[ κ ]) →
          (ρ₃ : Type Δ τ₂ R[ κ ]) →
          Pred Δ π κ

--------------------------------------------------------------------------------
-- Type vars.
data TVar : KEnv → Kind → Set where
  Z : ∀ {Δ : KEnv} {κ : Kind}
      → TVar (Δ , κ) κ
  S : ∀ {Δ : KEnv} {κ : Kind} {κ' : Kind}
      → TVar Δ κ → TVar (Δ , κ') κ

--------------------------------------------------------------------------------
-- Types.

open Pre.Type

data Type where
  ------------------------------------------------------------
  -- Base types (for mechanization).

  -- Unit (Mechanization.)
  U : ∀ {Δ : KEnv} →

         --------------
         Type Δ U (★)

  ------------------------------------------------------------
  -- System Fω.

  tvar : ∀ {Δ : KEnv} {κ : Kind} →

         TVar Δ κ →
         -----------
         Type Δ (tvar {!!}) κ

  _`→_ : ∀ {Δ : KEnv} →
          Type Δ τ₁ ★ → Type Δ τ₂ ★ →
          -----------------------------------
          Type Δ (τ₁ `→ τ₂) ★

  `∀ :  ∀ {Δ : KEnv} →
          (κ : Kind) → Type (Δ , κ) τ₁ ★ →
          -------------------------------------
          Type Δ (`∀ κ τ₁) ★

  `λ :  ∀ {Δ : KEnv} {κ : Kind} (κ¹ : Kind¹ κ) {κ₂ : Kind} →
          Type (Δ , κ) τ₁ κ₂ →
          -----------------------------------------
          Type Δ (`λ κ τ₁) (κ¹ `→ κ₂)

  _·[_] : ∀ {Δ : KEnv}{κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
          Type Δ τ₁ (κ¹ `→ κ₂) → Type Δ τ₂ κ →
          -----------------------------
          Type Δ τ₃ κ₂

  -- ------------------------------------------------------------
  -- -- Recursion.

  -- -- LFP. A thought---what happens if we take lfp of R[★] → R[★]?
  -- μ : {Δ : KEnv} →
  --         Type Δ (★¹ `→ ★) → 
  --         Type Δ ★

  -- -- GFP
  -- ν : {Δ : KEnv} →
  --         Type Δ (★¹ `→ ★) → 
  --         Type Δ ★

  -- ------------------------------------------------------------
  -- -- Qualified types.

  -- _⇒_ : ∀ {κ : Kind} {Δ : KEnv} →
  --          (π : Pred Δ κ) → Type Δ ★ →
  --          --------------------------------
  --          Type Δ ★

  -- ------------------------------------------------------------
  -- -- System Rω.

  -- -- Labels.
  -- lab : ∀ {Δ : KEnv} →
  --       Label →
  --       ----------
  --       Type Δ (L)

  -- -- singleton formation.
  -- _▹_ : ∀ {Δ : KEnv} {κ : Kind} →
  --       Type Δ (L) → Type Δ κ →
  --       -------------------
  --       Type Δ κ

  -- -- Row singleton formation.
  -- _R▹_ : ∀ {Δ : KEnv} {κ : Kind} →
  --        Type Δ L → Type Δ κ →
  --        -------------------
  --        Type Δ R[ κ ]

  -- -- label constant formation.
  -- ⌊_⌋ : ∀ {Δ : KEnv} →
  --       Type Δ (L) →
  --       ----------
  --       Type Δ (★)

  -- -- The empty record (mechanization only.)
  -- ∅ : ∀ {Δ : KEnv} →
  
  --     --------------
  --     Type Δ (★)

  -- -- Record formation.
  -- Π : ∀ {Δ : KEnv} →
  --     Type Δ R[ (★) ] →
  --     -------------
  --     Type Δ (★)

  -- -- Variant formation.
  -- Σ : ∀ {Δ : KEnv} →
  --     Type Δ R[ (★) ] →
  --     -------------
  --     Type Δ (★)

  -- -- lift₁ (lifting a function argument to row kind).
  -- _·⌈_⌉ : ∀ {Δ : KEnv}
  --           {κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
  --         Type Δ R[ κ¹ `→ κ₂ ] → Type Δ κ →
  --         --------------------------------
  --         Type Δ R[ κ₂ ]

  -- -- lift₂ (lifting a function to row kind.)
  -- ⌈_⌉·_ : ∀ {Δ : KEnv}
  --           {κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
  --         Type Δ (κ¹ `→ κ₂) → Type Δ R[ κ ] →
  --         --------------------------------
  --         Type Δ R[ κ₂ ]

