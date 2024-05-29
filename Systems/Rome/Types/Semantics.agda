{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Types.Semantics where

open import Preludes.Level
open import Preludes.Data

open import Rome.GVars.Kinds

open import Rome.Kinds
open import Rome.Types.Syntax

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

buildΣ : ∀ {ι} → (κ : Kind ι) → ⟦ R[ κ ] ⟧k → ⟦ κ ⟧k
buildΣ (★ _) ⟦ρ⟧ = Ix.Σ ⟦ρ⟧
buildΣ (κ₁ `→ κ₂) (n , f) = λ X → buildΣ κ₂ (n , λ i → f i X)
buildΣ (L _) ⟦ρ⟧ = tt
buildΣ R[ κ ] ⟦ρ⟧ = 0 , λ () 

buildΠ : ∀ {ι} → (κ : Kind ι) → ⟦ R[ κ ] ⟧k → ⟦ κ ⟧k
buildΠ (★ _) ⟦ρ⟧ = Ix.Π ⟦ρ⟧
buildΠ (κ₁ `→ κ₂) (n , f) = λ X → buildΠ κ₂ (n , λ i → f i X)
buildΠ (L _) ⟦ρ⟧ = tt
buildΠ R[ κ ] ⟦ρ⟧ = 0 , (λ ())

⟦ lab l ⟧t       H = tt
⟦ tvar v ⟧t      H = ⟦ v ⟧tv H
⟦ (t₁ `→ t₂) ⟧t H = ⟦ t₁ ⟧t H → ⟦ t₂ ⟧t H
⟦ `∀ κ v ⟧t      H = (s : ⟦ κ ⟧k) → ⟦ v ⟧t  (H , s)
⟦ t₁ ·[ t₂ ] ⟧t  H = (⟦ t₁ ⟧t H) (⟦ t₂ ⟧t H)
⟦ `λ κ v ⟧t     H =  λ (s : ⟦ κ ⟧k) → ⟦ v ⟧t (H , s)
⟦ _ ▹ v ⟧t       H = ⟦ v ⟧t H
⟦ _ R▹ τ ⟧t H = Ix.sing (⟦ τ ⟧t H)
⟦ ⌊ τ ⌋ ⟧t H       = ⊤
⟦ Π {κ = κ} ρ ⟧t H = buildΠ κ (⟦ ρ ⟧t H)
⟦ Σ {κ = κ} ρ ⟧t H = buildΣ κ (⟦ ρ ⟧t H)
⟦ ρ ·⌈ τ ⌉ ⟧t H = Ix.lift₁ (⟦ ρ ⟧t H) (⟦ τ ⟧t H)
⟦ ⌈ τ ⌉· ρ ⟧t H = Ix.lift₂ (⟦ τ ⟧t H) (⟦ ρ ⟧t H)
⟦ π ⇒ τ ⟧t H = ⟦ π ⟧p H → ⟦ τ ⟧t H
⟦ ε ⟧t H = Ix.emptyRow
⟦ μ F ⟧t H =  ⟦ F ⟧t H (Ix.Mu (⟦ F ⟧t H)) -- Ix.Mu (⟦ F ⟧t H)


--------------------------------------------------------------------------------
-- Problems with Σ κ for arbitrary κ:
--
-- ⟦_⟧t {κ = ★ _} (Σ ρ) H = Ix.Σ (⟦ ρ ⟧t H)
-- ⟦_⟧t {κ = ★ _ `→ ★ _} (Σ ρ) H = Ix.Σ² (⟦ ρ ⟧t H)
-- ⟦_⟧t {κ = κ₁ `→ κ₂} (Σ ρ) H with (⟦ ρ ⟧t H)
-- -- Goal: ⟦ κ₁ ⟧k → ⟦ κ₂ ⟧k
-- -- ————————————————————————————————————————————————————————————
-- -- P    : Fin n → ⟦ κ₁ ⟧k → ⟦ κ₂ ⟧k
-- -- n    : ℕ
-- --
-- -- The problem is we would like to introduce a ∃ (i : Fin n),
-- -- which we can do when the goal is (Set ℓ), but we cannot do here.
-- -- We do not know if
-- --   (∃ (i : Fin n). P i) : ⟦ κ₁ ⟧k → ⟦ κ₂ ⟧k
-- -- One way or another we need to reduce the goal to Set ι for some ι.
-- ... | n , P = {!∃!}
-- ⟦_⟧t {κ = L _} (Σ ρ) H = tt
-- ⟦_⟧t {κ = R[ κ ]} (Σ ρ) H with ⟦ ρ ⟧t H
-- ... | n , P = n , λ i → {!P i!}
