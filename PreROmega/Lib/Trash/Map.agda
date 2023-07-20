--------------------------------------------------------------------------------
-- Key/Value maps
--
-- The Agda std-lib exports Data.Tree.AVL.Map, but this data structure (being a
-- tree) presumes a StrictTotalOrder. We presume (for atoms and labels) only
-- decidable equality and fresh name generation, as per Charguéraud.

-- @ahubers: I think it is okay to extend our assumption of atoms to a strict
-- total order; for our purposes, it's not imperative we generalize these notions.
-- We're actually well within our rights to just assert that atoms are ℕ and
-- labels are Strings.
--
-- --------------------------------------------------------------------------------
-- The usage w.r.t. Rω is:
--
-- Rows have the form
--    Row = List (Label × Type)

-- and Environments the form
--    Env = List (Atom × Type)
--
-- So there is obviously an overlap to be abstracted.

-- Here are the sort of "questions" we want to ask of rows:
--   - is each label in a row distinct?
--       ℓᵢ distinct
--   - Is a label in a row?
--       (ℓ ∈ ρ)
--   - Are the domains of rows ρ₁ and ρ₂ equal?
--       dom ρ₁ = dom ρ₂
--   - For rows ρ₁ ρ₂ ρ₃, does
--       dom ρ₁ ⋃ dom ρ₂ = dom ρ₃?
--   - Are two row domains disjoint:
--       dom ρ₁ # dom ρ₂?
--   - Is one dom subset by another?
--       dom ρ₁ ⊆ dom ρ₂?
--   - Are the mappings of ρ₁ contained in ρ₂?
--        ρ₁(ℓ) ≡ ρ₂(ℓ) for all ℓ ∈ dom ρ₁

-- I think it makes sense to represents Rows as simply as possible (Key/Value
-- pair lists) in typing derivations, etc. But it makes more sense to convert
-- them to Sets to ask the other questions.


--------------------------------------------------------------------------------
module PreROmega.Lib.Map (Type : Set) where

-- TODO clean up these imports
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)




open import Data.List 
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

import Data.Tree.AVL.Map

open import Data.String using (String; _≟_)
open import Data.String.Properties
open Data.Tree.AVL.Map <-strictTotalOrder-≈

open import Data.Nat using (ℕ; zero; suc; _≟_)
-- open import Data.Nat.Properties renaming (strictTotalOrder to NatTotalOrder)
-- open Data.Tree.AVL.Map  <-strictTotalOrder

--------------------------------------------------------------------------------
-- Predicates on Rows

Row : Set
Label = String

Row = List (Label × Type)

mapDistinct : Map Type → Set
mapDistinct = {!!}

-- ℓdistinct :  Row → Set
-- ℓdistinct m with FromList m
-- ... | 


--------------------------------------------------------------------------------
-- Predicates on Environments

Atom : Set
Atom = ℕ

Env = List (Atom × Type)

--------------------------------------------------------------------------------
-- Helpers and generic combinators

-- dom : ∀ {K V : Set} → K ⊗ V → ⟨Set⟩
-- dom =  fromList ∘ (map proj₁)

-- img : ∀ {K V : Set} → K ⊗ V → List V
-- img = map proj₂

-- -- Map over values
-- mapV : ∀ {K V V' : Set} → (V → V') → K ⊗ V → K ⊗ V'
-- mapV f [] = []
-- mapV f ( ⟨ l , t ⟩ ∷ rs) = ⟨ l , f t ⟩ ∷ (mapV f rs)

-- --------------------------------------------------------------------------------
-- -- Projections into Sets.

-- --------------------------------------------------------------------------------
-- -- Equality testing

-- -- _≡dom_ : ∀ {K V} (l₁ l₂ : K ⊗ V) → Dec (dom l₁ ≡ dom l₂)
-- -- TODO:
-- --   Need a domain equality check
-- --   and row equality check, i.e.,
-- --        ρ₁(ℓ) ≡ ρ₂(ℓ)
-- --        which is short for:
-- --         ∀ ℓ ∈ dom(ρ₁), ρ₁(ℓ) ≡ ρ₂(ℓ)
-- --
-- -- It may, again, be best to use a Set or Finite set data type.
-- -- Copy from Metalib (they have these things defined).

-- -- Not technically *just* for rows
