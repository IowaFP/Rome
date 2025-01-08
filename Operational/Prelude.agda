module Rome.Operational.Prelude where

open import Agda.Primitive public

open import Data.Fin 
  using (Fin) 
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
open import Data.String hiding (_≈_ ; map) public
open import Data.List using (List ; [] ;  _∷_ ; map) public
open import Data.List.Membership.DecPropositional using (_∈_ ; _∈?_) public
open import Data.List.Relation.Unary.Any using (Any ; here ; there) public
Label = String

open import Function using (_∘_) public
open import Relation.Binary.PropositionalEquality as Eq public
open import Relation.Nullary using (¬_) public
open import Relation.Nullary.Negation using (contradiction; contraposition) public
open import Relation.Nullary using (Dec; yes; no) public

module Reasoning where
  open Eq.≡-Reasoning public

id : ∀ {A : Set} → A → A
id x = x

-- _≈_ : ∀ {A B} {P : A → Set} (f₁ f₂ : P A → P B) → Set
-- _≈_ {A} {_} {P} f₁ f₂ = ∀ (x : P A) → f₁ x ≡ f₂ x
