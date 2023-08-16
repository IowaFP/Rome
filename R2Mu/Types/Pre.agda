{-# OPTIONS --safe #-}
module R2Mu.Types.Pre where

open import Data.Nat
open import Data.String

open import R2Mu.Kinds.Syntax

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
  _·[_] : Type → Type → Type
  μ      : Type → Type
  ν      : Type → Type
  _⇒_   : Pred → Type → Type
  lab    : String → Type
  _▹_    : Type → Type → Type
  _R▹_    : Type → Type → Type
  ⌊_⌋ : Type → Type
  ∅ : Type
  Π : Type → Type
  Σ : Type → Type
  _·⌈_⌉ : Type → Type → Type
  ⌈_⌉·_ : Type → Type → Type

-- N.B., do not think I can get away with this;
-- see Types.Syntax decidability
private
  variable
    π : Pred
    τ τ₁ τ₂ τ₃ : Type

data PValue : Pred → Set
data Value : Type → Set

data PValue where
   _≲_ : Value τ₁ → Value τ₂ → PValue (τ₁ ≲ τ₂)
   _·_~_ : Value τ₁ → Value τ₂ → Value τ₃ →  PValue (τ₁ · τ₂ ~ τ₃)

data Value where
  U : Value U
  tvar : (n : ℕ) → Value (tvar n)
  _`→_  : (v₁ : Value τ₁) → (v₂ : Value τ₂) → Value (τ₁ `→ τ₂)
  `∀     : (κ : Kind) → Value τ → Value (`∀ κ τ)
  `λ     : (κ : Kind) → Value τ → Value (`λ κ τ)
  μ      : Value τ → Value (μ τ)
  ν      : Value τ → Value (ν τ)
  _⇒_   : PValue π → Value τ → Value (π ⇒ τ)
  lab    : (l : String) → Value (lab l)
  _▹_    : Value τ₁ → Value τ₂ → Value (τ₁ ▹ τ₂)
  _R▹_    : Value τ₁ → Value τ₂ → Value (τ₁ R▹ τ₂)
  ⌊_⌋ : Value τ → Value (⌊ τ ⌋)
  ∅ : Value ∅ 
  Π : Value τ → Value (Π τ)
  Σ : Value τ → Value (Σ τ)
