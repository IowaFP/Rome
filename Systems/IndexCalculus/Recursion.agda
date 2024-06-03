{-# OPTIONS --allow-unsolved-metas #-}
module IndexCalculus.Recursion where

open import Preludes.Level
open import Preludes.Data
open import IndexCalculus.Rows
open import IndexCalculus.Variants

--------------------------------------------------------------------------------
-- Denoting recursive types.

Functor = λ ℓ → Set ℓ → Set ℓ

--------------------------------------------------------------------------------
--  I have:
--   f : Type Δ (★ ℓ `→ `★ ℓ)
--  I want:
--    p : PolyFunctor
-- s.t.
-- LFP ⟦ f ⟧ ≃ Mu p
-- (which cannot be proven because lfp ⟦ f ⟧ is ill-founded.)


-- infixl 6 _⊕_
-- infixr 7 _⊗_
data PolyFunctor {ℓ : Level} : Set (lsuc ℓ) where
  Id : PolyFunctor {ℓ}
  Const : Set ℓ → PolyFunctor {ℓ}
  _`→_ : Set ℓ → PolyFunctor {ℓ} → PolyFunctor {ℓ}



[_] : ∀ {ℓ} → PolyFunctor {ℓ} → Set ℓ → Set ℓ
[ Id ] B = B
[ Const C ] B = C
[ A `→ F ] C = A → [ F ] C

data  Mu {ℓ} (F : PolyFunctor {ℓ}) : Set ℓ where
  In : [ F ] (Mu F) → Mu F

-- data W : Set where
--   w : ∀ {A} → (A → W) → W

-- fmap : {A B : Set} → (F : PolyFunctor) → (A → B) → [ F ] A → [ F ] B
-- fmap Id f a = f a
-- fmap (Const C) f c = c
-- -- fmap (F ⊕ G) f (left x) = left (fmap F f x)
-- -- fmap (F ⊕ G) f (right y) = right (fmap G f y)
-- -- fmap (F ⊗ G) f (x , y) = (fmap F f x) , fmap G f y


--------------------------------------------------------------------------------
-- Eliminators.

-- MAlg : ∀ {ℓ} (F : Functor ℓ) (A : Set ℓ) → Set (lsuc ℓ)
-- MAlg {ℓ} F A = (∀ (R : Set ℓ) → (R → A) → F R → A)

-- {-# TERMINATING #-}
-- mcata : ∀ {ℓ} {F : Functor ℓ} {A : Set ℓ} → MAlg F A → Mu F → A
-- mcata {ℓ} {F} φ (In x) = φ (Mu F) (mcata φ) x 
