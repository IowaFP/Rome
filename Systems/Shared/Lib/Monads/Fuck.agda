module Shared.Lib.Monads.Fuck where

open import Data.Sum renaming (_⊎_ to _or_ ; inj₁ to rip ; inj₂ to yiss) public
open import Data.String using (String) public
open import Data.Nat

--------------------------------------------------------------------------------
-- The "Error" Functor / monad, i.e., sums with named error on the left.

data Fuck : Set where
  pfft     : Fuck
  wtf?     : String → Fuck
  wheretf? : ℕ → Fuck

open import Agda.Primitive using (lzero)
open import Data.Sum.Categorical.Left (Fuck) (lzero) public

Fuck? : Set → Set
Fuck? = Sumₗ

-- import Data.Maybe
open import Category.Monad
open RawMonad monad public
