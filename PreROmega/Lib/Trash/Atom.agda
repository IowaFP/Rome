module PreROmega.Lib.Atom where

--------------------------------------------------------------------------------
-- Clean this up!

open import Data.Empty using (⊥; ⊥-elim)

open import Data.Bool using (true; false)

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤-totalOrder; _≟_; ≤-reflexive; ≤-refl; suc-injective)

open import Data.String using (String)

open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
open import Relation.Binary.PropositionalEquality
  using (_≡_;_≢_; refl; sym; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no; _because_; ofʸ; ofⁿ)

open import Function using (_∘_)

open import Data.List 
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Membership.Propositional using (_∈_;_∉_)
open import Data.List.Membership.Propositional.Properties

import Data.List.Extrema
open Data.List.Extrema (≤-totalOrder)

--------------------------------------------------------------------------------
-- Implementation of "atoms", defined by Charguèrard to be:
--
--   Atoms can be implemented using any datatype that support a comparison
--   function and a fresh name generator. The comparison function is used to
--   test whether two atoms are equal (i.e., equality on atoms needs to be
--   decidable). The fresh name generator, written "fresh", is used to pick an
--   atom fresh from any given finite set of atoms.

-- We will implement atoms sans generality as ℕ.
--------------------------------------------------------------------------------



-- postulate
--   Atom      : Set
--   atomDec   : ∀ (x y : Atom) → Dec (x ≡ y)
--   atomFresh : ∀ (xs : List Atom) → ∃[ a ] ( a ∉ xs )
--   fresh     : List Atom → Atom
--   fresh∉    : ∀ (xs : List Atom) → (fresh xs) ∉ xs

Atom Atoms : Set
Atom = ℕ
Atoms = List Atom

--------------------------------------------------------------------------------
-- Decidable Equality

AtomDec : ∀ (x y : Atom) → Dec (x ≡ y)
AtomDec = _≟_

--------------------------------------------------------------------------------
-- Freshness

-- This actually states: the max is the max.
ℕListMax : ∀ (xs : Atoms) → ∃[ n ] (All (_≤ max n xs) xs)
ℕListMax xs = ⟨ m , xs≤max m xs ⟩
  where
    m = max zero xs

∈⇒≤ : ∀ (x : Atom) (xs : Atoms) → x ∈ xs → (Any (λ y → y ≤ x) xs)
∈⇒≤ x .(_ ∷ _) (here {y} {ys} px) rewrite px = here ≤-refl
∈⇒≤ x .(_ ∷ _) (there {z} {zs} x∈zs) = there (∈⇒≤ x zs x∈zs)

≰⇒∉ : ∀ (x : Atom) (xs : Atoms) → ¬ (Any (λ y → y ≤ x) xs) → x ∉ xs
≰⇒∉ = {!!}

-- Have:
--  - x ∈ xs
--  - x = suc m
--  - ∀ (x ∈ xs), x ≤ m           or         All (_≤ m) xs
--  - 


helpMe : ∀ {n m} → n ≤ m → n ≢ suc m
helpMe {suc n} {suc m} (_≤_.s≤s n≤m) n=sucm rewrite (cong suc n=sucm) =  helpMe n≤m (suc-injective n=sucm)

-- (second go)
-- HAVE:
--   for all x ∈ xs, x ≤ m
-- WANT TO SHOW:
--   for all x ∈ xs, x ≠ suc m
atomFresh : ∀ (xs : List Atom) → ∃[ a ] ( a ∉ xs )
atomFresh xs  with (ℕListMax xs)
... | ⟨ m , ∀x∈xs→x≤m ⟩ = ⟨ (suc m) , All¬⇒¬Any {!!}  ⟩ -- with ∀x∈xs→x≤m
-- ... | []     = ⟨ suc m , All¬⇒¬Any [] ⟩
-- -- Need to show:
-- --    (¬_ ∘ _≡_ (suc m)) x
-- -- which means a lemma saying that if x≤m then x≠ m + 1.
-- ... | _∷_ {x} {xs} x≤m c =
--       ⟨ suc m , All¬⇒¬Any ((λ sucm≡x → helpMe {x}{m} {!!} (sym (sucm≡x))) ∷ {!!}) ⟩
--   where
--     contradiction : ¬ Any (_≡_ (suc m)) xs
--     contradiction J with satisfied J
--    ... | ⟨ x , x=m+1 ⟩ = {!!}
    -- contradiction (here {y} {ys} px) rewrite px = {!!}
    -- contradiction (there J) = {!!}
  --..
  -- let
  --   m = proj₁ (ℕListMax xs) in
  -- ⟨ suc m , {!!} ⟩
  -- where
  --   Pm = proj₂ (ℕListMax xs)
    
  --   m∉xs : suc m ∉ xs
  --   m∉xs px = {! ⟨ Pm , foo ⟩!}
  --     where
  --       foo = ∈⇒≤ (suc m) xs px



fresh : List Atom → Atom
fresh = proj₁ ∘ atomFresh


-- ℕListMax : ∀ (xs : Atoms) → ∃[ n ] ( ∀ x → x ∈ xs → x ≤ n)
-- ℕListMax [] = ⟨ 0 , (λ x ()) ⟩
-- ℕListMax (x ∷ xs) = ⟨ max x xs , ≤max ⟩
--   where
--     ≤max : ∀ y → y ∈ (x ∷ xs) → y ≤ max x xs
--     ≤max zero y∈ = v≤max⁺ {zero} x xs (inj₂ {!!})
--     ≤max (suc y) y∈ = v≤max⁺ {suc y} x xs (inj₂ {!!})

--------------------------------------------------------------------------------
-- Freshness



--------------------------------------------------------------------------------
-- 
