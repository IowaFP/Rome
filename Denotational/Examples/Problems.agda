module Rome.Denotational.Examples.Problems where

open import Agda.Primitive
open import Level

open import Data.Product
  renaming (proj₁ to fst; proj₂ to snd)
  hiding (Σ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)

open import Data.String
open import Data.Unit.Polymorphic
open import Data.Fin renaming (zero to fzero ; suc to fsuc)

open import Rome.Denotational.Kinds
open import Rome.Denotational.Entailment -- extensionality
open import Rome.Denotational.Entailment.Reasoning
open import Rome.Denotational.Types
open import Rome.Denotational.Types.Admissible
open import Rome.Denotational.Types.Substitution
open import Rome.Denotational.Types.Substitution.Properties -- extensionality
open import Rome.Denotational.Equivalence.Syntax
open import Rome.Denotational.Terms -- extensionality


--------------------------------------------------------------------------------
-- 
