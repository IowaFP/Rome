module PreROmega.Lib.Atom where

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Nat using (ℕ; suc)
open import Data.List 
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

--------------------------------------------------------------------------------
-- Atoms have the following properties.
-- (i) Decidable Equality
-- (ii) give a list of atoms L, we may always produce a fresh atom a s.t. a ∉ L.

module Atom
  (Atom      : Set)
  (=dec      : ∀ (x y : Atom) → Dec (x ≡ y))
  (atomFresh : ∀ (xs : List Atom) → ∃[ a ] (a ∉ xs))
  (fresh     : List Atom → Atom)
  (fresh∉    : ∀ (xs : List Atom) → (fresh xs) ∉ xs)
  (toNat     : Atom → ℕ) where

  Atoms : Set
  Atoms = List Atom

--------------------------------------------------------------------------------
-- For now, we only postulate having such atoms.
-- (can implement as ℕ later.)

module AtomPostulate where
  postulate
    Atom      : Set
    =dec      : ∀ (x y : Atom) → Dec (x ≡ y)
    atomFresh : ∀ (xs : List Atom) → ∃[ a ] (a ∉ xs)
    fresh     : List Atom → Atom
    fresh∉    : ∀ (xs : List Atom) → (fresh xs) ∉ xs
    toNat     : Atom → ℕ

  open Atom Atom =dec atomFresh fresh fresh∉ toNat public

open AtomPostulate public
