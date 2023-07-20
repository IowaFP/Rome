module PreROmega.Metatheory.TypeChecking where

open import Data.String using (String; _≟_)
open import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List 
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
import Relation.Binary.PropositionalEquality as Eq  

open import Function using (_∘_)

open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

import PreROmega.Lib.Biimplication as Bi
import PreROmega.IndexCalculus

open Bi
  using (_⇔_)
  renaming (Equivalence to E)

-- open import Atom
-- open import Row Type
open import PreROmega.Lib.AssocList
open import PreROmega.Lang.Syntax
open import PreROmega.Lang.Typing

import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary using (Dec; yes; no)

--------------------------------------------------------------------------------
-- Decidability of type checking

dec : ∀ (M : Term) (t : Type) → Dec (ε ⊢ₜ M ⦂ t)
dec = {!!}
