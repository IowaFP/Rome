{-# OPTIONS --safe #-}
module F.Kinds.Semantics where

open import Agda.Primitive
open import Level

open import Data.Unit.Polymorphic
open import Data.Product using (_×_)

open import F.Kinds.Syntax

--------------------------------------------------------------------------------
-- The meaning of kinds.

⟦_⟧k : ∀ {ℓ} → Kind ℓ → Set (lsuc ℓ)
⟦ ★ ℓ ⟧k = Set ℓ

--------------------------------------------------------------------------------
-- The meaning of kinding envs.

⟦_⟧ke : ∀ {ℓ} → KEnv ℓ → Set (lsuc ℓ)
⟦ ε ⟧ke = ⊤
⟦ Δ , κ ⟧ke =  ⟦ Δ ⟧ke × ⟦ κ ⟧k
