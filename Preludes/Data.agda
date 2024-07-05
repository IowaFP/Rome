{-# OPTIONS --safe #-}
module Preludes.Data where

--------------------------------------------------------------------------------
-- Data imports.

open import Data.Product 
  using (∃ ; ∃-syntax; Σ-syntax; _×_; _,_ )
  renaming (proj₁ to fst ; proj₂ to snd) public
open import Data.Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)
  hiding (map) public
open import Data.Nat using (ℕ ; zero ; suc ; _+_) public
open import Data.Nat.Show using (show) public
open import Data.String using (String ; _++_) public
open import Data.Fin 
  renaming 
    (zero to fzero ; suc to fsuc ; _+_ to _f+_) 
  hiding (_≟_)
  public
open import Data.Unit.Polymorphic using (⊤ ; tt) public
open import Data.Maybe using (Maybe ; just ; nothing ; _>>=_) public
open import Data.String using (_≟_) public
open import Data.Empty renaming (⊥ to ⊥₀) public
open import Data.Unit
  renaming (⊤ to ⊤₀ ; tt to tt₀)
  hiding (_≟_ ) public


--------------------------------------------------------------------------------
-- Maybe helpers.

joinM : ∀ {ℓ} {A : Set ℓ} → Maybe (Maybe A) → Maybe A
joinM (just m) = m
joinM nothing = nothing

return : ∀ {ℓ} {A : Set ℓ} → A → Maybe A
return = just


--------------------------------------------------------------------------------
-- Synonyms.

Potatoes = ℕ
dud = 0
spud = ℕ.suc
