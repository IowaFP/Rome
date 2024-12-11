module Rome.Shared.Monads.Maybe where

open import Agda.Primitive

open import Data.Maybe using (Maybe ; just ; nothing) public
open import Data.Maybe.Effectful using (monad ; join) public
open import Effect.Monad public using (RawMonad)

open RawMonad {f = lzero} monad

-- open monad public
