{-# OPTIONS --safe #-}
module Rome.Terms.Pre where

open import Data.Nat
open import Data.String
open import Rome.Kinds.Syntax

open import Rome.Types.Pre

data Term : Set where
  var : ℕ → Term
  `λ : Type → Term → Term
  _⦂_·_ : Term → Term → Type → Term
  `Λ : Type → Term → Term
  _⦂_·[_] : Term → Type → Type → Term
  `ƛ : Pred → Term → Term
  _⦂_·⟨_⟩ : Term → Kind → Pred → Term
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
  
