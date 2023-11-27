module Mix.TTiTT where

open import Preludes.Data
open import Data.List
open import Preludes.Relation


--------------------------------------------------------------------------------
-- A core type theory with one universe (in Agda) following [AbelOV18].
--
-- RE: Nvm just steal from https://github.com/mr-ohman/logrel-mltt.
-- Their schema seem to work.

module Pre where

data WHNF : Set
data Exp : Set

data Exp where
  wh : WHNF → Exp
  _·_ : Exp → Exp → Exp

data WHNF where
