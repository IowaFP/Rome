{-# OPTIONS --safe #-}
module Rome.Types.Syntax where

open import Agda.Primitive
open import Level

open import Data.String
open import Data.Nat using (ℕ ; suc ; zero)

open import Rome.Kinds.Syntax
import Rome.Types.Pre as Pre

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
data Value : ∀ (Δ : KEnv) (τ : Pre.Type) (κ : Kind) → Type Δ τ κ → Set

data Pred (Δ : KEnv) (_ : Pre.Pred) (κ : Kind) : Set

private
  variable
    π π₁ π₂ : Pre.Pred
    τ τ₁ τ₂ τ₃ : Pre.Type

data Pred Δ π κ where
  _≲_ : (ρ₁ : Type Δ τ₁ R[ κ ]) →
        (ρ₂ : Type Δ τ₂ R[ κ ]) →
        Pred Δ π κ

  _·_~_ : (ρ₁ : Type Δ τ₁ R[ κ ]) →
          (ρ₂ : Type Δ τ₂ R[ κ ]) →
          (ρ₃ : Type Δ τ₃ R[ κ ]) →
          Pred Δ π κ

--------------------------------------------------------------------------------
-- Type vars.
data TVar : KEnv → Kind → ℕ → Set where
  Z : ∀ {Δ : KEnv} {κ : Kind}
      → TVar (Δ , κ) κ ℕ.zero

  S : ∀ {Δ : KEnv} {κ : Kind} {κ' : Kind} 
      (n : ℕ) → TVar Δ κ n → TVar (Δ , κ') κ (ℕ.suc n)

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

         (n : ℕ) → TVar Δ κ n →
         -----------
         Type Δ (tvar n) κ

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
          Type Δ ((τ₁ ·[ τ₂ ]) (κ¹ `→ κ₂)) κ₂

  ------------------------------------------------------------
  -- Recursion.

  -- LFP. A thought---what happens if we take lfp of R[★] → R[★]?
  μ : {Δ : KEnv} →
          Type Δ τ (★¹ `→ ★) → 
          Type Δ (μ τ) ★

  -- GFP
  ν : {Δ : KEnv} →
          Type Δ τ (★¹ `→ ★) → 
          Type Δ (ν τ) ★

  ------------------------------------------------------------
  -- Qualified types.

  _⇒_ : ∀ {κ : Kind} {Δ : KEnv} →
           (π' : Pred Δ π κ) → Type Δ τ ★ →
           --------------------------------
           Type Δ (π ⦂ κ ⇒ τ)  ★

  ------------------------------------------------------------
  -- System Rω.

  -- Labels.
  lab : ∀ {Δ : KEnv} →
        (l : Label) →
        ----------
        Type Δ (lab l) L

  -- singleton formation.
  _▹_ : ∀ {Δ : KEnv} {κ : Kind} →
        Type Δ τ₁ L → Type Δ τ₂ κ →
        -------------------
        Type Δ (τ₁ ▹ τ₂) κ

  -- Row singleton formation.
  _R▹_ : ∀ {Δ : KEnv} {κ : Kind} →
         Type Δ τ₁ L → Type Δ τ₂ κ →
         -------------------
         Type Δ (τ₁ R▹ τ₂) R[ κ ]

  -- label constant formation.
  ⌊_⌋ : ∀ {Δ : KEnv} →
        Type Δ τ L →
        ----------
        Type Δ ⌊ τ ⌋ (★)

  -- The empty record (mechanization only.)
  -- Todo---remove and replace with empty record ε.
  -- (then ∅ ≃ Π ε.)
  ∅ : ∀ {Δ : KEnv} →
  
      --------------
      Type Δ ∅ (★)

  -- Record formation.
  Π : ∀ {τ} {Δ : KEnv} →
      Type Δ τ R[ (★) ] →
      -------------
      Type Δ (Π τ) ★

  -- Variant formation.
  Σ : ∀ {τ} {Δ : KEnv} →
      Type Δ τ R[ ★ ] →
      -------------
      Type Δ (Σ τ) ★

  -- lift₁ (lifting a function argument to row kind).
  _·⌈_⌉ : ∀ {Δ : KEnv}
            {κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
          Type Δ τ₁ R[ κ¹ `→ κ₂ ] → Type Δ τ₂ κ →
          --------------------------------
          Type Δ ((τ₁ ·⌈ τ₂ ⌉)  (κ¹ `→ κ₂ )) R[ κ₂ ]

  -- lift₂ (lifting a function to row kind.)
  ⌈_⌉·_ : ∀ {Δ : KEnv}
            {κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
          Type Δ τ₁ (κ¹ `→ κ₂) → Type Δ τ₂ R[ κ ] →
          --------------------------------
          Type Δ ((⌈ τ₁ ⌉· τ₂) (κ¹ `→ κ₂)) R[ κ₂ ]

-- N.B. that this Value type is actually a relation
-- on Pre.Type and Type.
-- 
data Value where
  U : ∀ {Δ} → Value Δ U ★ U
  -- Need to relate ℕ and TVar somehow...
--   tvar : ∀ {Δ}{n} → Value Δ (tvar n) ★ (tvar n)
