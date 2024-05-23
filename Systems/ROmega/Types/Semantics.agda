{-# OPTIONS --safe #-}
module ROmega.Types.Semantics where

open import Preludes.Level
open import Preludes.Data

open import ROmega.GVars.Kinds

open import ROmega.Kinds
open import ROmega.Types.Syntax

open import IndexCalculus using (Row)
import IndexCalculus as Ix

--------------------------------------------------------------------------------
-- The meaning of kinding environments and predicates (mutually recursive).


⟦_⟧t : Type Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k

⟦_⟧p : {κ : Kind ℓκ} → Pred Δ κ → ⟦ Δ ⟧ke → Set (lsuc ℓκ)
⟦ ρ₁ ≲ ρ₂ ⟧p H = ⟦ ρ₁ ⟧t H Ix.≲ ⟦ ρ₂ ⟧t H
⟦ ρ₁ · ρ₂ ~ ρ₃ ⟧p H = Ix._·_~_ (⟦ ρ₁ ⟧t H) (⟦ ρ₂ ⟧t H) (⟦ ρ₃ ⟧t H)

--------------------------------------------------------------------------------
-- The meaning of type vars.

⟦_⟧tv : TVar Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦ Z ⟧tv (_ , t) = t
⟦ S v ⟧tv (H , _) = ⟦ v ⟧tv H

--------------------------------------------------------------------------------
-- The meaning of types.

-- ⟦ U ⟧t           H = ⊤
⟦ lab l ⟧t       H = tt
⟦ tvar v ⟧t      H = ⟦ v ⟧tv H
⟦ (t₁ `→ t₂) ⟧t H = ⟦ t₁ ⟧t H → ⟦ t₂ ⟧t H
⟦ `∀ κ v ⟧t      H = (s : ⟦ κ ⟧k) → ⟦ v ⟧t  (H , s)
⟦ t₁ ·[ t₂ ] ⟧t  H = (⟦ t₁ ⟧t H) (⟦ t₂ ⟧t H)
⟦ `λ κ v ⟧t     H =  λ (s : ⟦ κ ⟧k) → ⟦ v ⟧t (H , s)
⟦ _ ▹ v ⟧t       H = ⟦ v ⟧t H
⟦ _R▹_ {ℓ} {ι} {_} {κ} _ τ ⟧t H = Ix.sing (⟦ τ ⟧t H)
⟦ ⌊ τ ⌋ ⟧t H       = ⊤
⟦ Π ρ ⟧t H = Ix.Π (⟦ ρ ⟧t H)
⟦ Σ ρ ⟧t H = Ix.Σ (⟦ ρ ⟧t H)
⟦ ρ ·⌈ τ ⌉ ⟧t H =  Ix.lift₁ (⟦ ρ ⟧t H) (⟦ τ ⟧t H)
⟦ ⌈ τ ⌉· ρ ⟧t H = Ix.lift₂ (⟦ τ ⟧t H) (⟦ ρ ⟧t H)
⟦ π ⇒ τ ⟧t H = ⟦ π ⟧p H → ⟦ τ ⟧t H
⟦ ε ⟧t H = Ix.emptyRow
