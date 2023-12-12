{-# OPTIONS --allow-unsolved-metas #-}
module Mix.Pre.Semantics where

open import Mix.Pre.Terms

module Rμ where
 open import Rome.Kinds.Syntax public
 open import Rome.Types.Syntax public
 open import Rome.Terms.Syntax public
 open import Rome.Entailment.Syntax public

open Rμ.Kind hiding (_`→_)
open Rμ.KEnv
open Rμ.Type hiding (_`→_)
open Rμ.TVar
open Rμ.Term

Row : Term → Term
Row s = `∃ Nat (Ix varZ `→ s)

--------------------------------------------------------------------------------
-- Translating typed Rω to untyped Mix.
--
⟦_⟧κ : (κ : Rμ.Kind) →  Term
⟦ ★ ⟧κ = ★
⟦ L ⟧κ = ⊤
⟦ R[ κ ] ⟧κ = Row ⟦ κ ⟧κ
⟦ κ₁ Rμ.`→ κ₂ ⟧κ = `∀ ⟦ κ₁ ⟧κ ⟦ κ₂ ⟧κ

⟦_⟧p : ∀ {Δ}{κ} → Rμ.Pred Δ κ → Term
⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Term

⟦ U ⟧τ = ⊤
⟦ tvar Z ⟧τ = varZ
⟦ tvar (S x) ⟧τ = varS ⟦ (tvar x) ⟧τ
⟦ τ Rμ.`→ υ ⟧τ = ⟦ τ ⟧τ `→ ⟦ υ ⟧τ 
⟦ `∀ κ τ ⟧τ = `∀ ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ `λ κ τ ⟧τ = `∀ ⟦ κ ⟧κ  ⟦ τ ⟧τ
⟦ τ ·[ υ ] ⟧τ = ⟦ τ ⟧τ · ⟦ υ ⟧τ
⟦ μ τ ⟧τ = ⊤
⟦ ν τ ⟧τ = ⊤
⟦ π ⇒ τ ⟧τ = ⟦ π ⟧p `→ ⟦ τ ⟧τ
⟦ lab l ⟧τ = ⊤
⟦ _ ▹ τ ⟧τ = ⟦ τ ⟧τ
⟦ _ R▹ τ ⟧τ = ⟪ One ⦂ Nat , `λ (Ix One) Case x₀ of[I₀↦ ⟦ τ ⟧τ Iₛ↦ ƛ⦅⦆ ] ⟫
⟦ ⌊ _ ⌋ ⟧τ = ⊤
⟦ ε ⟧τ = ⟪ Z ⦂ Nat , ƛ⦅⦆ ⟫
⟦ Π ρ ⟧τ = Case ⟦ ρ ⟧τ of⟪
                       --   | x₀  | x₁        | x₂
  (`λ Nat              -- ε 
    (`λ (Ix x₀ `→ ★) -- ε , Nat 
      ((Ix x₁) `→ (x₁ · x₀)))) ⟫ -- ε , Nat , Ix x₀ → ★, Ix x₁
⟦ Σ ρ ⟧τ = Case ⟦ ρ ⟧τ of⟪
                       --   | x₀  | x₁        | x₂
  (`λ Nat              -- ε 
    (`λ (Ix x₀ `→ ★) -- ε , Nat 
      (`∃ (Ix x₁)      -- ε , Nat , Ix x₀ → ★
        (x₁ · x₀)))) ⟫ -- ε , Nat , Ix x₀ → ★, Ix x₁

⟦ _·⌈_⌉ {κ₁ = κ₁} {κ₂} ρ υ ⟧τ = Case ⟦ ρ ⟧τ of⟪                       
  (`λ Nat              
    (`λ ((Ix x₀) `→ (⟦ κ₁ ⟧κ `→ ⟦ κ₂ ⟧κ)) 
    -- Nat , Ix x₀ → ⟦ κ₁ ⟧κ → ⟦ κ₂ ⟧κ
    ⟪ x₁ ⦂ Nat , (`λ (Ix x₁) 
    -- Nat , Ix x₀ → ⟦ κ₁ ⟧κ → ⟦ κ₂ ⟧κ, Ix x₁
    ((x₁ · x₀) · ⟦ υ ⟧τ)) ⟫ )) ⟫
⟦ ⌈_⌉·_ {κ₁ = κ₁} {κ₂} τ ρ ⟧τ = Case ⟦ ρ ⟧τ of⟪                       
  (`λ Nat              
    (`λ (Ix x₀ `→ ⟦ κ₁ ⟧κ) 
    -- Nat , Ix x₀ → ⟦ κ₁ ⟧κ
    ⟪ x₁ ⦂ Nat , (`λ (Ix x₁) 
    -- Nat , Ix x₀ → ⟦ κ₁ ⟧κ , Ix x₁
    (⟦ τ ⟧τ · (x₁ · x₀))) ⟫ )) ⟫

--------------------------------------------------------------------------------
-- Translating predicate well-formedness judgements to Ix types.

-- The next few helpers are for my sanity.

ρ-elim : ∀ {Δ} → (κ : Rμ.Kind) → Rμ.Type Δ R[ κ ] → Term → Term
ρ-elim κ ρ M = Case ⟦ ρ ⟧τ of⟪ `λ Nat (`λ (Ix x₀ `→ ⟦ κ ⟧κ) M) ⟫

-- This doesn't work. P and Q need to be weakened.
⟪_,_⟫In⟪_,_⟫ : Term → Term → Term → Term → Term 
⟪ n , P ⟫In⟪ m , Q ⟫ = `∀ (Ix n) (`∃ (Ix m) (varS (varS P) · x₁) ~ (varS (varS Q) · x₀))

-- N.b. I am actually weakening x₂ ↦ x₄ and x₀ ↦ x₂.
-- This is all sorts of a fucking mess. Should write a
⟦_⟧p {κ = κ} (ρ₁ Rμ.≲ ρ₂) = ρ-elim κ ρ₁ (ρ-elim κ ρ₂ ⟪ x₃  , varS (varS x₂) ⟫In⟪ x₁ , varS (varS x₀) ⟫)
⟦_⟧p {κ = κ} (ρ₁ Rμ.· ρ₂ ~ ρ₃) = 
  ρ-elim κ ρ₁  -- intr. ⟪ x₅ : Nat , x₄ ⟫
  (ρ-elim κ ρ₂ -- intr. ⟪ x₃ , x₂ ⟫
  (ρ-elim κ ρ₃ -- intr. ⟪ x₁ , x₀ ⟫
  injL `× injR))
  where
  injL = (⟪ n ,  P ⟫In⟪ l , R ⟫ `× ⟪ m ,  Q ⟫In⟪ l , R ⟫)
    where
      n = x₅
      P = x₄
      m = x₃
      Q = x₂
      l = x₁
      R = x₀
  injR = 
    `∀ (Ix x₁) -- forall k : Ix l
    (`∃ (Ix (varS x₅))  -- exists i : Ix n
    ((P · i) ~ (R · k)))
    Or 
    (`∃ (Ix (varS x₃)) -- exists i : Ix m
    ((Q · i) ~ (R · k)))
    where
      n = varS x₅
      P = varS x₅
      m = varS x₄
      Q = varS x₃
      l = varS x₂
      R = varS x₁
      k = x₁
      i = x₀
  

