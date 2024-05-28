{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Kinds.Semantics where


open import Preludes.Level
open import Preludes.Data


open import IndexCalculus using (Row)

open import Rome.GVars.Levels
open import Rome.Kinds.Syntax

--------------------------------------------------------------------------------
-- The meaning of kinds.

⟦_⟧k : Kind ℓ → Set (lsuc ℓ)
⟦ ★ ℓ ⟧k = Set ℓ
⟦ κ₁ `→ κ₂ ⟧k = ⟦ κ₁ ⟧k → ⟦ κ₂ ⟧k
⟦ L ℓ ⟧k = ⊤
⟦_⟧k {ℓ} R[ k ] = Row ⟦ k ⟧k

--------------------------------------------------------------------------------
-- The meaning of kinding envs.

⟦_⟧ke : KEnv ℓ → Set (lsuc ℓ)
⟦ ε ⟧ke = ⊤
⟦ Δ , κ ⟧ke =  ⟦ Δ ⟧ke × ⟦ κ ⟧k
