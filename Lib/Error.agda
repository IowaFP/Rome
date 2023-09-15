module Lib.Error where

open import Data.Sum renaming (_⊎_ to _or_) public
open import Data.String using (String) public
open import Data.Nat

--------------------------------------------------------------------------------
-- The "Error" Functor / monad, i.e., sums with named error on the left.

data Fuck : Set where
  fuck : String → Fuck
  fine : Fuck
  where? : ℕ → Fuck

Error : Set → Set
Error A = Fuck or A

open import Data.Sum.Categorical.Right public
