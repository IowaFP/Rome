{-# OPTIONS --safe #-}
module Prelude where

open import Agda.Primitive public

open import Data.Fin 
  using (Fin ; fromℕ ; inject₁ ; cast) 
  renaming (zero to fzero ; suc to fsuc ; _<_ to _≺_) public
open import Data.Unit hiding (_≟_) public
open import Data.Empty public
import Data.Sum as Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)

open import Data.Maybe using (Maybe ; just ; nothing) public
open import Data.Bool using (Bool ; true ; false ; not) public

open Sum using (_or_ ; left ; right) public
import Data.Product as Product
  renaming (proj₁ to fst ; proj₂ to snd) 
open Product 
  using (_×_ ; fst ; snd ; _,_ ; Σ-syntax ; ∃ ; ∃-syntax) 
  public
open import Data.Product.Properties using (,-injectiveʳ ; ,-injectiveˡ) public

open import Data.Nat using (ℕ ; zero ; suc) public
open import Data.Nat.Properties using (suc-injective) public

open import Data.String hiding (_≈_ ; map ; length ; _++_) public
open import Relation.Binary.Structures using (IsStrictPartialOrder) public
open import Data.String.Properties renaming (<-isStrictPartialOrder-≈ to SPO) public

open import Data.List using (List ; [] ;  _∷_ ; [_] ; map ; length ; reverse ; _++_; lookup) public
open import Data.List.Relation.Unary.Any 
  using (Any ; here ; there) 
  renaming (map to map-any) public
open import Data.List.Relation.Unary.Any.Properties hiding (map-id ; map-cong ; map-∘) public
open import Data.List.Membership.Propositional using (_∈_ ; _∉_ ) public
import Data.Vec as Vec using (Vec; tabulate)
open Vec public

Label = String

open import Function using (_∘_) public
open import Relation.Binary.PropositionalEquality as Eq 
  renaming ([_] to [[_]]) public 
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality) public
open import Relation.Nullary using (¬_) public
open import Relation.Nullary.Negation using (contradiction; contraposition) public
open import Relation.Nullary using (Dec; yes; no ; map′ ; Irrelevant) public
open import Relation.Nullary.Decidable using (True ; toWitness ; fromWitness) public renaming (⌊_⌋ to ∥_∥)
-- open import Relation.Unary using (_⊆_) public

module Reasoning where
  open Eq.≡-Reasoning public

--------------------------------------------------------------------------------
-- common functions

id : ∀ {A : Set} → A → A
id x = x

--------------------------------------------------------------------------------
-- Pair helpers

third : ∀ {A B C : Set} → A × B × C → C
third = snd ∘ snd

overᵣ : ∀ {A B C : Set} → (A → B) → C × A → C × B
overᵣ f (l , τ) = (l , f τ)

overₗ : ∀ {A B C : Set} → (A → B) → A × C → B × C
overₗ f (l , τ) = (f l , τ)

both :  ∀ {A B : Set} → (A → B) → A × A → B × B
both f (x , y) = (f x , f y)

------------------------------------------------------------------------------
-- A lemma that certainly is somewhere in the std-lib

left-inversion : ∀ {A B : Set} {x y : A} → left {B = B} x ≡ left y → x ≡ y
left-inversion {x = x} {y = y} refl = refl 

--------------------------------------------------------------------------------
-- congruence over a 3-ary function

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v l m} → x ≡ y → u ≡ v → l ≡ m → f x u l ≡ f y v m
cong₃ f refl refl refl = refl


--------------------------------------------------------------------------------
-- Mere propositions 
--
-- A type A is a *mere proposition* if it is term irrelevant: any two inhabitants
-- are equal.

UIP : ∀ {A : Set} {x y : A} → (p₁ p₂ : x ≡ y) → p₁ ≡ p₂
UIP {A} {x} {y} refl refl = refl

Dec→Irrelevant : ∀ (P : Set) → (d : Dec P) → Irrelevant (True d)
Dec→Irrelevant P (yes d) p₁ p₂ = refl
Dec→Irrelevant P (no  d) p₁ p₂ = refl




--------------------------------------------------------------------------------
-- Absurd elimination of Any type

-- absurd∈ : ∀ {A : Set} {xs : List Label} {x : Label} {p : x ∈ xs} → there p ≡ here refl → A 
-- absurd∈ ()
