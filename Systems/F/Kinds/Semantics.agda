{-# OPTIONS --safe #-}
module F.Kinds.Semantics where

open import Agda.Primitive
open import Level

open import Data.Unit.Polymorphic
open import Data.Product using (_×_)

open import F.Kinds.Syntax

--------------------------------------------------------------------------------
-- The meaning of kinds.  
--
-- N.B. System F does not strictly need kinds, of course. But, we are in
-- *stratified system F*, which must keep track of levels. It will be easiest
-- and most uniform (w.r.t. extended systems) to do so with kinds.

⟦_⟧k : ∀ {ℓ} → Kind ℓ → Set (lsuc ℓ)
⟦ ★ ℓ ⟧k = Set ℓ

--------------------------------------------------------------------------------
-- The meaning of kinding envs.

⟦_⟧ke : ∀ {ℓ} → KEnv ℓ → Set (lsuc ℓ)
⟦ ε ⟧ke = ⊤
⟦ Δ , κ ⟧ke =  ⟦ Δ ⟧ke × ⟦ κ ⟧k
