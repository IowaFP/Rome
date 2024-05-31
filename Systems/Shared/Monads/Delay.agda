{-# OPTIONS --guardedness --copatterns #-}
module Shared.Monads.Delay where

--------------------------------------------------------------------------------
-- Declaring the Delay Monad

data Delay (A : Set) : Set 
record ∞Delay (A : Set) : Set 

data Delay A where
  now : A → Delay A
  later : ∞Delay A → Delay A

record ∞Delay A where
  coinductive
  field
    force : Delay A

open ∞Delay

open import Category.Monad
-- open RawMonad monad public
