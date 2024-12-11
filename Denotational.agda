module Rome.Denotational where

--------------------------------------------------------------------------------
-- Load & typecheck *all* modules.

-- Entailment.
open import Rome.Denotational.Entailment public
open import Rome.Denotational.Entailment.Reasoning public

-- Equivalence.
open import Rome.Denotational.Equivalence public

-- Kinds.
open import Rome.Denotational.Kinds public

-- Terms.
open import Rome.Denotational.Terms as Terms public
open import Rome.Denotational.Terms.Admissible public

-- Types.
open import Rome.Denotational.Types as Types public
open import Rome.Denotational.Types.Admissible public
open import Rome.Denotational.Types.Substitution public
open import Rome.Denotational.Types.Substitution.Properties public
