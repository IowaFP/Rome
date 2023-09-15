module Rome.Terms.Checking where

open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Data.Product using (∃ ; ∃-syntax; Σ-syntax; _×_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Maybe
open import Data.Maybe.Categorical

open import Rome.Kinds.Syntax
open import Rome.Kinds.Equality
open import Rome.Types.Syntax
open import Rome.Terms.Syntax

import Rome.Types.Pre as PreTypes
import Rome.Terms.Pre as PreTerms
import Pre

--------------------------------------------------------------------------------
-- 

_∣_⊢τ_⦂_ : ∀ (Δ : KEnv) (Φ : PEnv) → Pre.Term → (τ : Pre.Type) → Maybe (Term Δ Φ τ)
-- _∣_⊢τ? = ∀ (Δ : KEnv) (Φ : PEnv) → (τ : Pre.Type) → (κ : Kind) → Maybe (Term Δ Φ τ) 
