{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Both.IndexCalculus.Normal where

open import Rome.Preludes.Data
open import Rome.Preludes.Level
open import Rome.Preludes.Relation

open import Data.Product using (Σ)
open import Data.List

--------------------------------------------------------------------------------
-- 

open import Data.Vec

-- Vector & Row equivalence

toFin : ∀ {ℓ} (A : Set ℓ) (n : ℕ) →  Vec A n → (Fin n → A)
toFin A .ℕ.zero [] = λ { () }
toFin A .(ℕ.suc _) (x ∷ v) fzero = x
toFin A .(ℕ.suc _) (x ∷ v) (fsuc {n = n} f) = toFin A n v f

toVec : ∀ {ℓ} (A : Set ℓ) (n : ℕ) → (Fin n → A) → Vec A n
toVec A ℕ.zero f = []
toVec A (ℕ.suc n) f = (f (fromℕ n)) ∷ toVec A n (λ x → f (inject₁ x))

iso : ∀ {ℓ} (A : Set ℓ) (n : ℕ) (v : Vec A n) → toVec A n (toFin A n v) ≡ v
iso A .ℕ.zero [] = refl
iso A .(ℕ.suc n) (_∷_ {n} x v) = {!!}


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

-- rec : ∀ {ℓ} {A : Set ℓ} → 
--       (N : Normal) → ((⟦ N ⟧N A) → A) → Mu N → A
-- rec (Shape / size) φ (In x) = {!!}
