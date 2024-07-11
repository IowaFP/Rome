module Rome where

--------------------------------------------------------------------------------
-- Load & typecheck *all* modules.

-- Entailment.
open import Rome.Entailment public
open import Rome.Entailment.Reasoning public

-- Equivalence.
open import Rome.Equivalence public

open import Rome.Kinds public

-- Terms.
open import Rome.Terms as Terms public
open import Rome.Terms.Admissible public

-- Types.
open import Rome.Types as Types public
open import Rome.Types.Admissible public
open import Rome.Types.Substitution public
open import Rome.Types.Substitution.Properties public
