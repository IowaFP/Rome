module Rome where

--------------------------------------------------------------------------------
-- Load & typecheck *all* modules.

-- Entailment.
open import Rome.Entailment -- extensionality
open import Rome.Entailment.Reasoning

-- Equivalence.
open import Rome.Equivalence -- extensionality

-- Terms.
open import Rome.Terms as Terms -- extensionality

-- Types.
open import Rome.Types as Types
open import Rome.Types.Substitution
open import Rome.Types.Substitution.Properties -- extensionality

-- Examples.
open import Rome.Examples.Section-3 -- extensionality
