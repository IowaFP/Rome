{-# OPTIONS --safe #-}
module R2Mu.Types.Syntax where

open import Agda.Primitive
open import Level

open import Data.String
open import Data.Nat using (ℕ ; suc ; zero)

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
    π π₁ π₂ : Pre.Pred
    τ τ₁ τ₂ τ₃ : Pre.Type

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
          Type Δ τ₃ κ₂

  ------------------------------------------------------------
  -- Recursion.

  -- LFP. A thought---what happens if we take lfp of R[★] → R[★]?
  μ : {Δ : KEnv} →
          Type Δ τ (★¹ `→ ★) → 
          Type Δ (μ τ) ★

  -- GFP
  ν : {Δ : KEnv} →
          Type Δ τ (★¹ `→ ★) → 
          Type Δ (μ τ) ★

  ------------------------------------------------------------
  -- Qualified types.

  _⇒_ : ∀ {κ : Kind} {Δ : KEnv} →
           (π' : Pred Δ π κ) → Type Δ τ ★ →
           --------------------------------
           Type Δ (π ⇒ τ)  ★

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
  ∅ : ∀ {Δ : KEnv} →
  
      --------------
      Type Δ ∅ (★)

  -- Record formation.
  Π : ∀ {Δ : KEnv} →
      Type Δ τ R[ (★) ] →
      -------------
      Type Δ (Π τ) ★

  -- Variant formation.
  Σ : ∀ {Δ : KEnv} →
      Type Δ τ R[ ★ ] →
      -------------
      Type Δ (Π τ) ★

  -- lift₁ (lifting a function argument to row kind).
  _·⌈_⌉ : ∀ {Δ : KEnv}
            {κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
          Type Δ τ₁ R[ κ¹ `→ κ₂ ] → Type Δ τ₂ κ →
          --------------------------------
          Type Δ (τ₁ ·⌈ τ₂ ⌉) R[ κ₂ ]

  -- lift₂ (lifting a function to row kind.)
  ⌈_⌉·_ : ∀ {Δ : KEnv}
            {κ : Kind} {κ¹ : Kind¹ κ} {κ₂ : Kind} →
          Type Δ τ₁ (κ¹ `→ κ₂) → Type Δ τ₂ R[ κ ] →
          --------------------------------
          Type Δ (⌈ τ₁ ⌉· τ₂) R[ κ₂ ]


--------------------------------------------------------------------------------
-- Decidability (move to Decidabilty.agda later)


open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_)

-- Todo---need type-level "Value" predicate.
⊢ₖ? : ∀ {Δ : KEnv} → (τ : Pre.Type) → (κ : Kind) → Dec (Type Δ τ κ)
⊢ₖ? τ ★                 = {!!}

⊢ₖ? (lab l) L           = yes (lab l)
⊢ₖ? {Δ} U L                 = no P
  where
    P : ¬ Type Δ U L
    P (tvar n x ·[ τ ])      = {!!}
    P p@(`λ {τ₁} _ M ·[ τ ]) = {!P !}
    P (F ·[ F₁ ] ·[ τ ])     = P {!!}
    P ((F ▹ F₁) ·[ τ ])      = {!!}
⊢ₖ? (tvar x) L          = {!!}
⊢ₖ? (τ `→ τ₁) L         = {!!}
⊢ₖ? (`∀ x τ) L          = {!!}
⊢ₖ? (`λ x τ) L          = {!!}
⊢ₖ? (τ ·[ τ₁ ]) L       = {!!}
⊢ₖ? (μ τ) L             = {!!}
⊢ₖ? (ν τ) L             = {!!}
⊢ₖ? (x ⇒ τ) L           = {!!}
⊢ₖ? {Δ} (τ₁ ▹ τ₂) L with ⊢ₖ? {Δ} τ₁ L | ⊢ₖ? {Δ} τ₂ L
...   | yes l₁ | yes l₂ =  yes (l₁ ▹ l₂)
...   | yes l₁ | no p   =  no (λ { (F ·[ τ ]) → {!!} ; (_ ▹ l) → p l })
...   | no  p | _       =  no λ { (F ·[ τ ]) → {!!} ; (l ▹ _) → p l }
⊢ₖ? (τ R▹ τ₁) L         = {!!}
⊢ₖ? ⌊ τ ⌋ L             = {!!}
⊢ₖ? ∅ L                 = {!!}
⊢ₖ? (Π τ) L             = {!!}
⊢ₖ? (Σ τ) L             = {!!}
⊢ₖ? (τ ·⌈ τ₁ ⌉) L       = {!!}
⊢ₖ? (⌈ τ ⌉· τ₁) L       = {!!}

⊢ₖ? τ R[ κ ]            = {!!}
⊢ₖ? τ (x `→ κ)          = {!!}

