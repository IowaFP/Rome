module SFFP.Prelude where

open import Data.Unit public
open import Data.Empty public
import Data.Sum as Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)

open Sum using (_or_ ; left ; right) public
import Data.Product as Product
  renaming (proj₁ to fst ; proj₂ to snd ; _,_ to ⟨_,_⟩) 
open Product using (fst ; snd ; ⟨_,_⟩ ; Σ ; Σ-syntax ; ∃ ; ∃-syntax) public

open import Function using (_∘_) public
open import Relation.Binary.PropositionalEquality as Eq public

module Reasoning where
  open Eq.≡-Reasoning public

id : ∀ {A : Set} → A → A
id x = x

-- _≈_ : ∀ {A B} {P : A → Set} (f₁ f₂ : P A → P B) → Set
-- _≈_ {A} {_} {P} f₁ f₂ = ∀ (x : P A) → f₁ x ≡ f₂ x
