{-# OPTIONS --guardedness #-}
module Preludes.Partiality where

open import Agda.Builtin.Coinduction public
open import Category.Monad public
open import Category.Monad.Partiality
  renaming (Kind to PKind) public
