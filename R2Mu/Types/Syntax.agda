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

⊢ₖ? : ∀ {Δ : KEnv} → (τ : Pre.Type) → (v : Pre.Value τ) → (κ : Kind) → Dec (Type Δ τ κ)
⊢ₖ? .U Pre.U ★ = yes U
⊢ₖ? .(tvar n) (Pre.tvar n) ★ = yes (tvar n {!!})
⊢ₖ? .(_ `→ _) (v Pre.`→ v₁) ★ = {!!}
⊢ₖ? .(`∀ κ _) (Pre.`∀ κ v) ★ = {!!}
⊢ₖ? .(`λ κ _) (Pre.`λ κ v) ★ = {!!}
⊢ₖ? .(μ _) (Pre.μ v) ★ = {!!}
⊢ₖ? .(ν _) (Pre.ν v) ★ = {!!}
⊢ₖ? .(_ ⇒ _) (x Pre.⇒ v) ★ = {!!}
⊢ₖ? .(lab l) (Pre.lab l) ★ = {!!}
⊢ₖ? .(_ ▹ _) (v Pre.▹ v₁) ★ = {!!}
⊢ₖ? .(_ R▹ _) (v Pre.R▹ v₁) ★ = {!!}
⊢ₖ? .(⌊ _ ⌋) Pre.⌊ v ⌋ ★ = {!!}
⊢ₖ? .∅ Pre.∅ ★ = {!!}
⊢ₖ? .(Π τ) (Pre.Π v) ★ = yes (Π τ)
⊢ₖ? .(Σ _) (Pre.Σ v) ★ = {!!}

⊢ₖ? .U v@Pre.U L = {!!}
⊢ₖ? .(tvar n) (Pre.tvar n) L = {!!}
⊢ₖ? .(_ `→ _) (v Pre.`→ v₁) L = {!!}
⊢ₖ? .(`∀ κ _) (Pre.`∀ κ v) L = {!!}
⊢ₖ? .(`λ κ _) (Pre.`λ κ v) L = {!!}
⊢ₖ? .(μ _) (Pre.μ v) L = {!!}
⊢ₖ? .(ν _) (Pre.ν v) L = {!!}
⊢ₖ? .(_ ⇒ _) (x Pre.⇒ v) L = {!!}
⊢ₖ? .(lab l) (Pre.lab l) L = {!!}
⊢ₖ? .(_ ▹ _) (v Pre.▹ v₁) L = {!!}
⊢ₖ? .(_ R▹ _) (v Pre.R▹ v₁) L = {!!}
⊢ₖ? .(⌊ _ ⌋) Pre.⌊ v ⌋ L = {!!}
⊢ₖ? .∅ Pre.∅ L = {!!}
⊢ₖ? .(Π _) (Pre.Π v) L = {!!}
⊢ₖ? .(Σ _) (Pre.Σ v) L = {!!}
⊢ₖ? .U Pre.U R[ κ ] = {!!}
⊢ₖ? .(tvar n) (Pre.tvar n) R[ κ ] = {!!}
⊢ₖ? .(_ `→ _) (v Pre.`→ v₁) R[ κ ] = {!!}
⊢ₖ? .(`∀ κ _) (Pre.`∀ κ v) R[ κ₁ ] = {!!}
⊢ₖ? .(`λ κ _) (Pre.`λ κ v) R[ κ₁ ] = {!!}
⊢ₖ? .(μ _) (Pre.μ v) R[ κ ] = {!!}
⊢ₖ? .(ν _) (Pre.ν v) R[ κ ] = {!!}
⊢ₖ? .(_ ⇒ _) (x Pre.⇒ v) R[ κ ] = {!!}
⊢ₖ? .(lab l) (Pre.lab l) R[ κ ] = {!!}
⊢ₖ? .(_ ▹ _) (v Pre.▹ v₁) R[ κ ] = {!!}
⊢ₖ? .(_ R▹ _) (v Pre.R▹ v₁) R[ κ ] = {!!}
⊢ₖ? .(⌊ _ ⌋) Pre.⌊ v ⌋ R[ κ ] = {!!}
⊢ₖ? .∅ Pre.∅ R[ κ ] = {!!}
⊢ₖ? .(Π _) (Pre.Π v) R[ κ ] = {!!}
⊢ₖ? .(Σ _) (Pre.Σ v) R[ κ ] = {!!}
⊢ₖ? .U Pre.U (x `→ κ) = {!!}
⊢ₖ? .(tvar n) (Pre.tvar n) (x `→ κ) = {!!}
⊢ₖ? .(_ `→ _) (v Pre.`→ v₁) (x `→ κ) = {!!}
⊢ₖ? .(`∀ κ _) (Pre.`∀ κ v) (x `→ κ₁) = {!!}
⊢ₖ? .(`λ κ _) (Pre.`λ κ v) (x `→ κ₁) = {!!}
⊢ₖ? .(μ _) (Pre.μ v) (x `→ κ) = {!!}
⊢ₖ? .(ν _) (Pre.ν v) (x `→ κ) = {!!}
⊢ₖ? .(_ ⇒ _) (x Pre.⇒ v) (x₁ `→ κ) = {!!}
⊢ₖ? .(lab l) (Pre.lab l) (x `→ κ) = {!!}
⊢ₖ? .(_ ▹ _) (v Pre.▹ v₁) (x `→ κ) = {!!}
⊢ₖ? .(_ R▹ _) (v Pre.R▹ v₁) (x `→ κ) = {!!}
⊢ₖ? .(⌊ _ ⌋) Pre.⌊ v ⌋ (x `→ κ) = {!!}
⊢ₖ? .∅ Pre.∅ (x `→ κ) = {!!}
⊢ₖ? .(Π _) (Pre.Π v) (x `→ κ) = {!!}
⊢ₖ? .(Σ _) (Pre.Σ v) (x `→ κ) = {!!}
