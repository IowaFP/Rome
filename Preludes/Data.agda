{-# OPTIONS --safe #-}
module Rome.Preludes.Data where

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
open import Data.String using (String) public
open import Data.Fin 
  renaming 
    (zero to fzero ; suc to fsuc ; _+_ to _f+_) 
  hiding (_≟_)
  public
open import Data.Fin.Properties using (suc-injective) public
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

join→ : ∀ {ℓ ι} {A : Set ℓ} {B : Set ι} → 
          Maybe (Maybe A → Maybe B) → Maybe A → Maybe B
join→ (just x) a = x a
join→ nothing a = nothing

join→k : ∀ {ℓ ι} {A : Set ℓ} {B : Set ι} → 
          Maybe (A → Maybe B) → A → Maybe B
join→k (just x) a = x a
join→k nothing a = nothing

--------------------------------------------------------------------------------
-- Synonyms.

Potatoes = ℕ
