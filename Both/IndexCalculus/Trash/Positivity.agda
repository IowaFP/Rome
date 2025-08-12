{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Both.IndexCalculus.Positivity where

open import Rome.Preludes.Level
open import Rome.Preludes.Data
open import Rome.Both.IndexCalculus.Rows
open import Rome.Both.IndexCalculus.Variants

--------------------------------------------------------------------------------
-- Denoting recursive types.

data Positive : Set₁ where
  Id : Positive
  Const : (A : Set) → Positive
  _`→_ : (A : Set) → Positive → Positive

[_] : Positive → Set → Set
[ Id ] X = X
[ Const A ] X = A
[ A `→ d ] X = {!!}
