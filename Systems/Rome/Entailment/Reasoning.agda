{-# OPTIONS --safe #-}
module Rome.Entailment.Reasoning where

open import Agda.Primitive

open import Function using (id)

open import Rome.Kinds.Syntax
open import Rome.Types.Syntax
open import Rome.Entailment.Syntax

--------------------------------------------------------------------------------
-- Entailment derivations in the style of PLFA equational reasoning.

infixr 2 _⊩⟨_⟩_

private
  variable
    Δ : KEnv 
    Φ : PEnv Δ 
    κ : Kind
    π : Pred Δ κ


_⊩⟨_⟩_ : ∀ {κ₁ κ₂ κ₃ : Kind} {π₂ : Pred Δ κ₂}  {π₃ : Pred Δ κ₃} 
         (π₁ : Pred Δ κ₁) →
         (Ent Δ Φ π₁ → Ent Δ Φ π₂) →
         (Ent Δ Φ π₂ → Ent Δ Φ π₃) →
         Ent Δ Φ π₁ → Ent Δ Φ π₃
_⊩⟨_⟩_ π₁ 1→2 2→3 e₁ = 2→3 (1→2 e₁)         

∎ : Ent Δ Φ π →
     Ent Δ Φ π
∎ = id

--------------------------------------------------------------------------------

