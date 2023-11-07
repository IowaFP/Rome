{-# OPTIONS --allow-unsolved-metas #-}
module Mix.Substitution where

open import Preludes.Data
open import Data.List
open import Preludes.Relation

open import Mix.Pre.Terms
open import Mix.Terms

--------------------------------------------------------------------------------
-- Required reading, which I seem to always forget...
-- https://plfa.github.io/Properties/#prelude-to-preservation
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------


-- weaken : ∀ {Δ} {τ υ} {κ₁ κ₂} 
--          {Δ ⊢ υ ⦂ κ₁} → Δ ⊢ (τ ⦂ κ₂)   →
--          (Δ , υ) ⊢ ((rename τ) ⦂ κ₂)
-- weaken {υ = υ} ★ = ★
-- weaken {υ = υ} (⊤ x) = ⊤ x
-- weaken {υ = υ} tt = tt
-- weaken {υ = υ} varZ = varS varZ
-- weaken {υ = υ} (varS τ) = varS (weaken τ)
-- weaken {υ = υ} Nat = Nat
-- weaken {υ = υ} Zero = Zero
-- weaken {υ = υ} (Suc τ) = Suc (weaken τ)
-- weaken {υ = υ} (Ix τ) = Ix (weaken τ)
-- weaken {Δ} {υ = υ} (FZero (Ix τ)) = FZero (Ix {!weaken τ!})
-- weaken {υ = υ} (FSuc τ) = {!!}
-- weaken {υ = υ} (Π τ M) = {!!}
-- weaken {υ = υ} (`λ τ M) = {!!}
-- weaken {υ = υ} (M · N) = weaken M · weaken N
-- weaken {υ = υ} (Σ τ M) = {!!}
-- weaken {υ = υ} ⟪ M ⦂ τ₁ , τ₂ ⟫ = {!!}
-- weaken {υ = υ} (fst τ) = fst (weaken τ)
-- weaken {υ = υ} (snd τ) = snd (weaken τ)
