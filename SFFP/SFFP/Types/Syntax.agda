module SFFP.Types.Syntax where

open import SFFP.Prelude
open import SFFP.Kinds.Syntax
open import SFFP.Kinds.GVars

--------------------------------------------------------------------------------
-- 2.4 Types


data Type Δ : Kind → Set where
  ` : 
      KVar Δ κ →
      --------
      Type Δ κ

  `λ : 
      
      Type (Δ ,, κ₁) κ₂ → 
      ---------------
      Type Δ (κ₁ `→ κ₂)

  _·_ : 
      
      Type Δ (κ₁ `→ κ₂) → 
      Type Δ κ₁ → 
      ----------------
      Type Δ κ₂

  _`→_ : 

         Type Δ ★ →
         Type Δ ★ → 
         --------
         Type Δ ★

  `∀    :
      
         (κ : Kind) → Type (Δ ,, κ) ★ →
         -------------
         Type Δ ★

  μ     :
      
         Type (Δ ,, ★) ★ →
         -------------
         Type Δ ★
