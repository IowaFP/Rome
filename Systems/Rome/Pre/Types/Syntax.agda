{-# OPTIONS --safe #-}
module Rome.Pre.Types.Syntax where

open import Preludes.Data

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
  _·[_] : Type → Type → Type
  μ      : Type → Type
  ν      : Type → Type
  _⦂_⇒_   : Pred → Kind → Type → Type
  lab    : String → Type
  _▹_    : Type → Type → Type
  _R▹_    : Type → Type → Type
  ⌊_⌋ : Type → Type
  ε : Type
  Π : Type → Type
  Σ : Type → Type
  _·⌈_⌉ : Type → Type → Type
  ⌈_⌉·_ : Type → Type → Type
