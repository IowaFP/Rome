--------------------------------------------------------------------------------
-- WIP. Motivation:

-- The clarity of this mechanization (and the sanity of its writer) revolves
-- around the representation of rows and environments.
--   - Most of the interesting predicates we have are set operations on rows.
--   - Variable binding == pain in the ass == mostly a problem with environments.

-- So I think it's worthwhile to specify Rows and Environments as first-class
-- citizens of this project.
--
--
-- --------------------------------------------------------------------------------
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

--------------------------------------------------------------------------------
module PreROmega.Lib.Row (Type : Set) where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.String using (String; _≟_)
open import Data.String.Properties
open import Data.Tree.AVL.Sets <-strictTotalOrder-≈

-- TODO clean up these imports
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no; _because_)

open import Function using (_∘_)

open import PreROmega.Lib.AssocList


-- open import Data.Nat.Properties renaming (strictTotalOrder to NatTotalOrder)
-- open Data.Tree.AVL.Sets  <-strictTotalOrder

--------------------------------------------------------------------------------
-- definitions

Row : Set
Label = String

Row = List (Label × Type)

⟨dom⟩ : Row → ⟨Set⟩
⟨dom⟩ = fromList ∘ dom

--------------------------------------------------------------------------------
-- Predicates.
--
-- There are many ways often to assert something. Sometimes, the dumber-looking
-- ways are easier to prove or reason about. So these implementation details are
-- subject to change.


-- --------------------------------------------------------------------------------
-- Is each label in a row distinct?
-- --       ℓᵢ distinct
data Distinct : Row → Set where
  distinct[] :
             -------------
             Distinct []
  distinct:: : ∀ l t rs →
               l ∉ dom rs   →   Distinct rs →
               -------------------------------
                 Distinct ( ⟨ l , t ⟩ ∷ rs)


-- --------------------------------------------------------------------------------
-- --   - Is a label in a row?
-- --       (ℓ ∈ ρ)

infix 4 _∈ρ_ _∉ρ_

_∈ρ_ : Label → Row → Set
l ∈ρ r = l ∈ dom r

_∉ρ_ : Label → Row → Set
l ∉ρ r = l ∉ dom r


-- --------------------------------------------------------------------------------
--  Is one dom subset by another?
--       dom ρ₁ ⊆ dom ρ₂?
--
_⊆ρ_ : Row → Row → Set
r₁ ⊆ρ r₂ = forall l → (l ∈ dom r₁) → l ∈ dom r₂

--------------------------------------------------------------------------------
--  Are the domains of rows ρ₁ and ρ₂ equal?
--       dom ρ₁ = dom ρ₂
-- _=dom=_ : Row → Row → Set
-- r₁ =dom= r₂ = (r₁ ⊆ρ r₂) × (r₂ ⊆ρ r₁)

-- Or, using ⟨Set⟩

_=dom=_ : Row → Row → Set
r₁ =dom= r₂ = ⟨dom⟩ r₁ ≡ ⟨dom⟩ r₂

--------------------------------------------------------------------------------
-- For rows ρ₁ ρ₂ ρ₃, does
--   dom ρ₁ ⋃ dom ρ₂ = dom ρ₃?

_∪dom_ : Row → Row → ⟨Set⟩
r₁ ∪dom r₂ = union (⟨dom⟩ r₁) (⟨dom⟩ r₂)

--------------------------------------------------------------------------------
-- Are two row domains disjoint:
--   dom ρ₁ # dom ρ₂?

-- Using ⟨Set⟩
_#dom_ : Row → Row → Set
r₁ #dom r₂ = intersection (⟨dom⟩ r₁) (⟨dom⟩ r₂) ≡ empty



--------------------------------------------------------------------------------
-- Are the mappings of ρ₁ contained in ρ₂?
--   ρ₁(ℓ) ≡ ρ₂(ℓ) for all ℓ ∈ dom ρ₁

-- N.B. This needs to be defined with the relation τ ≡ₜ τ on types,
-- as we need to assert type equivalence w.r.t. ≡ₜ.


