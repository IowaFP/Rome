{-# OPTIONS --safe #-}
module Rome.Types.Pre where

open import Data.Nat
open import Data.String

open import Rome.Kinds.Syntax

--------------------------------------------------------------------------------
--

data Type : Set
data Pred : Set


data Pred where
   _≲_ : Type → Type → Pred
   _·_~_ : Type → Type → Type → Pred
       
data Type where
  U : Type
  tvar : ℕ → Type
  _`→_  : Type → Type → Type  
  `∀     : Kind → Type → Type
  `λ     : Kind → Type → Type
  _⦂_·[_] : Type → Kind → Type → Type
  μ      : Type → Type
  ν      : Type → Type
  _⦂_⇒_   : Pred → Kind → Type → Type
  lab    : String → Type
  _▹_    : Type → Type → Type
  _R▹_    : Type → Type → Type
  ⌊_⌋ : Type → Type
  ∅ : Type
  Π : Type → Type
  Σ : Type → Type
  _⦂_·⌈_⌉ : Type → Kind → Type → Type
  ⌈_⦂_⌉·_ : Type → Kind → Type → Type

-- data PValue : Pred → Set
-- data Value : Type → Set

-- data PValue where
--    _≲_ : ∀ {τ₁ τ₂} → Value τ₁ → Value τ₂ → PValue (τ₁ ≲ τ₂)
--    _·_~_ : ∀ {τ₁ τ₂ τ₃} → Value τ₁ → Value τ₂ → Value τ₃ →  PValue (τ₁ · τ₂ ~ τ₃)

-- data Value where
--   U : Value U
--   tvar : (n : ℕ) → Value (tvar n)
--   _`→_  : ∀ {τ₁ τ₂} → (v₁ : Value τ₁) → (v₂ : Value τ₂) → Value (τ₁ `→ τ₂)
--   `∀     : ∀ {τ} → (κ : Kind) → Value τ → Value (`∀ κ τ)
--   `λ     : ∀ {τ} → (κ : Kind) → Value τ → Value (`λ κ τ)
--   μ      : ∀ {τ} → Value τ → Value (μ τ)
--   ν      : ∀ {τ} → Value τ → Value (ν τ)
--   _⇒_   : ∀ {π τ} → PValue π → Value τ → Value (π ⇒ τ)
--   lab    : (l : String) → Value (lab l)
--   _▹_    : ∀ {τ₁ τ₂} → Value τ₁ → Value τ₂ → Value (τ₁ ▹ τ₂)
--   _R▹_    : ∀ {τ₁ τ₂} → Value τ₁ → Value τ₂ → Value (τ₁ R▹ τ₂)
--   ⌊_⌋ : ∀ {τ} → Value τ → Value (⌊ τ ⌋)
--   ∅ : Value ∅ 
--   Π : ∀ {τ} → Value τ → Value (Π τ)
--   Σ : ∀ {τ} → Value τ → Value (Σ τ)
