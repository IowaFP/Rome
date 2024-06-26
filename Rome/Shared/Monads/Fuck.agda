module Shared.Monads.Fuck where

open import Data.Sum renaming (_⊎_ to _or_ ; inj₁ to rip ; inj₂ to yiss) public
open import Data.String using (String) public
open import Data.Nat

--------------------------------------------------------------------------------
-- The "Error" Functor / monad, i.e., sums with named error on the left.

data Fuck : Set where
  justFucked : Fuck
  what?  : String → Fuck
  where? : ℕ → Fuck

open import Agda.Primitive using (lzero)
open import Data.Sum.Categorical.Left (Fuck) (lzero) public

Fuck? : Set → Set
Fuck? = Sumₗ

fuck : ∀ {A} → Fuck? A
fuck = rip justFucked

wheretf? : ∀ {A} →  ℕ → Fuck? A
wheretf? n = rip (where? n)

wtf? : ∀ {A} →  String → Fuck? A
wtf? s = rip (what? s)


open import Category.Monad
open RawMonad monad public
