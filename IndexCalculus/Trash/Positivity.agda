{-# OPTIONS --allow-unsolved-metas #-}
module IndexCalculus.Positivity where

open import Preludes.Level
open import Preludes.Data
open import IndexCalculus.Rows
open import IndexCalculus.Variants

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
