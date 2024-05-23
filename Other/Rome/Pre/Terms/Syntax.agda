{-# OPTIONS --safe #-}
module Rome.Pre.Terms.Syntax where

open import Preludes.Data

open import Rome.Kinds.Syntax
open import Rome.Pre.Types
--------------------------------------------------------------------------------
-- Pre-terms.

data Term : Set where
  var : ℕ → Term
  `λ : Type → Term → Term
  _·_ : Term → Term → Term
  `Λ : Type → Term → Term
  _·[_] : Term → Type → Term
  `ƛ : Pred → Term → Term
  _·⟨_⟩ : Term → Pred → Term
  lab : String → Term
  _▹_ : Term → Term → Term
  _/_ : Term → Term → Term
  ∅   : Term
  _⊹_ : Term → Term → Term
  prj : Term → Term → Term
  Π   : Term → Term
  Π⁻¹ : Term → Term
  Σ   : Term → Term
  Σ⁻¹ : Term → Term
  inj : Term → Term
  _▿_ : Term → Term → Term
  syn : Term → Term → Term
  ana : Type → Type → Term → Term
  fold : Term → Term → Term → Term → Term
  In : Term → Term
  Out : Term → Term
  
