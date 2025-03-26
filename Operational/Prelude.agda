module Rome.Operational.Prelude where

open import Agda.Primitive public

open import Data.Fin 
  using (Fin ; #_ ; fromℕ ; inject₁) 
  renaming (zero to fzero ; suc to fsuc) public
open import Data.Unit hiding (_≟_) public
open import Data.Empty public
import Data.Sum as Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)

open import Data.Maybe using (Maybe ; just ; nothing) public

open Sum using (_or_ ; left ; right) public
import Data.Product as Product
  renaming (proj₁ to fst ; proj₂ to snd) 
open Product 
  using (_×_ ; fst ; snd ; _,_ ; Σ-syntax ; ∃ ; ∃-syntax) 
  public

open import Data.Nat using (ℕ ; zero ; suc) public
open import Data.String hiding (_≈_ ; map ; length) public
open import Data.List using (List ; [] ;  _∷_ ; map ; length) public
open import Data.List.Relation.Unary.Any using (Any ; here ; there) public
open import Data.List.Relation.Unary.Any.Properties hiding (map-id ; map-cong ; map-∘) public
open import Data.List.Membership.DecPropositional (_≟_) using (_∈_ ; _∈?_ ; _∉_ ; _∉?_) public

Label = String

open import Function using (_∘_) public
open import Relation.Binary.PropositionalEquality as Eq public
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality) public
open import Relation.Nullary using (¬_) public
open import Relation.Nullary.Negation using (contradiction; contraposition) public
open import Relation.Nullary using (Dec; yes; no ; map′) public
open import Relation.Nullary.Decidable using (True ; toWitness ; fromWitness) public renaming (⌊_⌋ to ∥_∥)

module Reasoning where
  open Eq.≡-Reasoning public

id : ∀ {A : Set} → A → A
id x = x

third : ∀ {A B C : Set} → A × B × C → C
third = snd ∘ snd

------------------------------------------------------------------------------
-- Some lemmas I couldn't find elsewhere

left-inversion : ∀ {A B : Set} {x y : A} → left {B = B} x ≡ left y → x ≡ y
left-inversion {x = x} {y = y} refl = refl 

--------------------------------------------------------------------------------
--

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v l m} → x ≡ y → u ≡ v → l ≡ m → f x u l ≡ f y v m
cong₃ f refl refl refl = refl


--------------------------------------------------------------------------------
-- Mere propositions 
--
-- A type A is a *mere proposition* if it is term irrelevant: any two inhabitants
-- are equal.

MereProp : ∀ (A : Set) → Set 
MereProp A = (p₁ p₂ : A) → p₁ ≡ p₂

--------------------------------------------------------------------------------
-- Absurd elimination of Any type

absurd∈ : ∀ {A : Set} {xs : List Label} {x : Label} {p : x ∈ xs} → there p ≡ here refl → A 
absurd∈ ()
