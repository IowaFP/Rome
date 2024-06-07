{-# OPTIONS --allow-unsolved-metas  #-}
module IndexCalculus.Recursion where

open import Preludes.Level
open import Preludes.Data
open import IndexCalculus.Rows
open import IndexCalculus.Variants
open import IndexCalculus.Records

--------------------------------------------------------------------------------
-- Functors.

Functor = λ ℓ → (Set ℓ → Set ℓ)
FmapT : ∀ {ℓ} → (F : Functor ℓ) → Set (lsuc ℓ)
FmapT {ℓ} F = ∀ {A B : Set ℓ} → (A → B) → F A → F B 

FmapT-ρ : ∀ {ℓ} → (ρ : Row (Functor ℓ)) → Set (lsuc ℓ)
FmapT-ρ ρ = Π (lift₂ FmapT ρ)

--------------------------------------------------------------------------------
-- Denoting recursive types.

{-# NO_POSITIVITY_CHECK #-}
data Mu {ℓ} (F : Functor ℓ) : Set ℓ where
  In : F (Mu F) → Mu F

out : ∀ {ℓ} {F : Functor ℓ} → Mu F → F (Mu F)
out (In x) = x
