{-# OPTIONS --allow-unsolved-metas #-}
module IndexCalculus.Normal where

open import Preludes.Data
open import Preludes.Level

open import Data.Product using (Σ)

--------------------------------------------------------------------------------
-- See "Datatypes in Datatypes", McBride '15.
--
-- We can think of Normal functors as generalizing rows.

private
  variable
    ℓ : Level
record Normal : Set (lsuc ℓ) where
  constructor _/_
  field
    Shape : Set ℓ
    size  : Shape → ℕ
  ⟦_⟧N : Set ℓ → Set ℓ
  ⟦ X ⟧N = Σ[ s ∈ Shape ] (Fin (size s) → X)

open Normal public
infixr 0 _/_

--------------------------------------------------------------------------------
-- LFP of Normal functors

data Mu (N : Normal {ℓ}) : Set ℓ where
  In : ⟦ N ⟧N (Mu N) → Mu N

rec : ∀ {ℓ} {A : Set ℓ} → 
      (N : Normal) → ((⟦ N ⟧N A) → A) → Mu N → A
rec (Shape / size) φ (In x) = {!!}
