{-# OPTIONS --safe #-}
module ROmega.Kinds.Semantics where

open import Agda.Primitive
open import Level

open import Data.Unit.Polymorphic
open import Data.Product using (_×_)

open import IndexCalculus using (Row)
open import ROmega.Kinds.Syntax

--------------------------------------------------------------------------------
-- Var dump.

private
  variable
    ℓ : Level

--------------------------------------------------------------------------------
-- The meaning of kinds.

⟦_⟧k : Kind ℓ → Set (lsuc ℓ)
⟦ ★ ℓ ⟧k = Set ℓ
⟦ κ₁ `→ κ₂ ⟧k = ⟦ κ₁ ⟧k → ⟦ κ₂ ⟧k
⟦ L ⟧k = ⊤
⟦_⟧k {ℓ} R[ k ] = Row ⟦ k ⟧k

--------------------------------------------------------------------------------
-- The meaning of kinding envs.

⟦_⟧ke : KEnv ℓ → Set (lsuc ℓ)
⟦ ε ⟧ke = ⊤
⟦ Δ , κ ⟧ke =  ⟦ Δ ⟧ke × ⟦ κ ⟧k
