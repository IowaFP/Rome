{-# OPTIONS --safe #-}
module F.Types.Semantics where

open import Agda.Primitive
open import Level

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Product
  renaming (proj₁ to fst; proj₂ to snd)
  hiding (Σ)
open import Data.Unit.Polymorphic
open import Data.Empty.Polymorphic

open import F.Kinds
open import F.Types.Syntax

--------------------------------------------------------------------------------
-- The meaning of kinding environments and predicates (mutually recursive).


⟦_⟧t : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} {κ : Kind ι} →
      Type Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
--------------------------------------------------------------------------------
-- The meaning of type vars.

⟦_⟧tv : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} {κ : Kind ι}
        → TVar Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦ Z ⟧tv (_ , t) = t
⟦ S v ⟧tv (H , _) = ⟦ v ⟧tv H

--------------------------------------------------------------------------------
-- The meaning of types.

⟦ U ⟧t           H = ⊤
⟦ tvar v ⟧t      H = ⟦ v ⟧tv H
⟦ (t₁ `→ t₂) ⟧t H = ⟦ t₁ ⟧t H → ⟦ t₂ ⟧t H
⟦ `∀ κ v ⟧t      H = (s : ⟦ κ ⟧k) → ⟦ v ⟧t  (H , s)
