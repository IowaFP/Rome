module PreROmega.Lib.AssocList where

open import Data.List

open import Data.Product
  using (_×_; proj₁; proj₂)

-- Technical debt: this function is shared by environments, too.
-- Should move to own file -- maybe called AssocList.agda 
dom : ∀ {A B : Set} → List (A × B) → List A
dom = (map proj₁)

img :  ∀ {A B : Set} → List (A × B) → List B
img = map proj₂
