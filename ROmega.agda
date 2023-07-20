module ROmega where

--------------------------------------------------------------------------------
-- Load & typecheck *all* modules.

-- Entailment.
open import ROmega.Entailment -- extensionality
open import ROmega.Entailment.Reasoning

-- Equivalence.
open import ROmega.Equivalence -- extensionality

-- Examples.
open import ROmega.Examples.Section-3 -- extensionality

-- IndexCalculus.
open import IndexCalculus.Rows as Ix
open import IndexCalculus.Properties

-- Lib (shared util).
open import Lib.Equality

-- Postulates.
open import Postulates.FunExt

-- Terms.
open import ROmega.Terms as Terms -- extensionality

-- Types.
open import ROmega.Types as Types
open import ROmega.Types.Substitution
open import ROmega.Types.Substitution.Properties -- extensionality
