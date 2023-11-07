{-# OPTIONS --allow-unsolved-metas #-}
module Mix.Semantics where

open import Mix.Pre.Terms
import Mix.Pre.Semantics as Pre
open import Mix.Terms

open import Preludes.Data
open import Data.List
open import Preludes.Relation

--------------------------------------------------------------------------------
--

module Rμ where
 open import Rome.Kinds.Syntax public
 open import Rome.Types.Syntax public
 open import Rome.Terms.Syntax public
 open import Rome.Entailment.Syntax public

open Rμ.Kind
open Rμ.KEnv
open Rμ.Type
open Rμ.TVar
open Rμ.Term

postulate
  weaken : ∀ {Δ} {τ υ} {κ₁ κ₂} 
           {u : Δ ⊢ υ ⦂ κ₁} → Δ ⊢ τ ⦂ κ₂   →
           (Δ , u) ⊢ (rename τ) ⦂ κ₂
--------------------------------------------------------------------------------
-- Typed translation of kinds.

⟦_⟧κ : ∀ {Δ} → (κ : Rμ.Kind) → Δ ⊢ Pre.⟦ κ ⟧κ ⦂ 𝓤
⟦ ★ ⟧κ = ★
⟦ L ⟧κ = ⊤ 𝓤
⟦ R[ κ ] ⟧κ = Σ Nat (Π (Ix varZ) ⟦ κ ⟧κ) 
⟦ κ₁ `→ κ₂ ⟧κ = Π ⟦ κ₁ ⟧κ {!!} -- (weaken ⟦ κ₂ ⟧κ) 

-- --------------------------------------------------------------------------------
-- -- Typed translation of contexts.
⟦_⟧Δ : Rμ.KEnv → Context
⟦ ε ⟧Δ = ε
⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , ⟦ κ ⟧κ

-- --------------------------------------------------------------------------------
-- -- Typed translation of types.

⟦_⟧v : ∀ {Δ}{κ} → (v : Rμ.TVar Δ κ) → ⟦ Δ ⟧Δ ⊢ Pre.⟦ (tvar v) ⟧τ ⦂ Pre.⟦ κ ⟧κ
⟦ Z ⟧v = varZ
⟦ S v ⟧v = varS ⟦ v ⟧v

⟦_⟧τ : ∀ {Δ}{κ} → (τ : Rμ.Type Δ κ) → ⟦ Δ ⟧Δ ⊢ Pre.⟦ τ ⟧τ  ⦂ Pre.⟦ κ ⟧κ
⟦ U ⟧τ = ⊤ ★
⟦ tvar x ⟧τ = ⟦ x ⟧v
⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ {!!} -- (weaken ⟦ τ₂ ⟧τ)
⟦ `∀ κ τ ⟧τ = Π ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ `λ κ τ ⟧τ = `λ ⟦ κ ⟧κ {!⟦ τ ⟧τ!} -- ⟦ τ ⟧τ
⟦ τ₁ ·[ τ₂ ] ⟧τ = ⟦ τ₁ ⟧τ · ⟦ τ₂ ⟧τ
--
⟦ lab l ⟧τ = tt
⟦ _ ▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ _ R▹ τ ⟧τ = {!!} -- ⟪ (Suc Zero) ⦂ Nat , `λ (Ix varZ) ? --  ⟫ -- ⟪ (Suc Zero) ⦂ Nat , (Π (Ix varZ) {!⟦ τ ⟧τ!}) ⟫ 
⟦ ⌊ τ ⌋ ⟧τ = ⊤ ★
-- I need to actually do substitution.
⟦ ε ⟧τ = ⟪ Zero ⦂ Nat , `λ (Ix varZ) (⊤ ★) ⟫
-- I need renaming in symbol expressions.
⟦ Π τ ⟧τ = {!!} -- Π (Ix (fst ⟦ τ ⟧τ)) (snd (weaken (⟦ τ ⟧τ)) · {!varZ!})
⟦ Σ τ ⟧τ = Σ {!!} ({!!} · {!!})
⟦ τ ·⌈ τ₁ ⌉ ⟧τ = {!!}
⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}

⟦ μ τ ⟧τ = {!!}
⟦ ν τ ⟧τ = {!!}

⟦ π ⇒ τ ⟧τ = {!!}
