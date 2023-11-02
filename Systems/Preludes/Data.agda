{-# OPTIONS --safe #-}
module Preludes.Data where

--------------------------------------------------------------------------------
-- Data.Nat imports.

open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_; _,_) public
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
  hiding (map) public
open import Data.Nat using (ℕ ; zero ; suc ; _+_) public
open import Data.Nat.Show using (show) public
open import Data.String using (String ; _++_) public
open import Data.Fin 
  renaming 
    (zero to fzero ; suc to fsuc ; _+_ to _f+_) 
  public

