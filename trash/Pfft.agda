module Mix.Pfft where

open import Preludes.Data
open import Data.List
open import Preludes.Relation

open import Data.Nat using (_⊔_)

--------------------------------------------------------------------------------
-- Sorts

data Sort : Set where
  𝓤 : Sort
  ★  : Sort

-- =============================================================================
-- Terms, i.e., the untyped syntax.
-- =============================================================================


data Term : Set where
  ★ : Term
  var : ℕ → Term
  Π : Term → Term → Term
  `λ : Term → Term → Term
  _·_ : Term → Term → Term
  
-- =============================================================================
-- Formation and typing rules. 
-- =============================================================================
--------------------------------------------------------------------------------
-- Declare contexts and judgements.
-- (mutually recursive.)
data Context : Set
data _⊢_⦂ₛ_ : Context → Term → Sort → Set
data _⊢_⦂_ : Context → Term → Term → Set

data Context where
  ε : Context
  _,_ : ∀ {M}{σ} → (Δ : Context) → Δ ⊢ M ⦂ₛ σ → Context

private
  variable
    Δ : Context 

--------------------------------------------------------------------------------
-- Sorting judgements.


data _⊢_⦂ₛ_ where
  ★ : Δ ⊢ ★ ⦂ₛ 𝓤
  Π : ∀ {τ υ σ σ'} →
        (t : Δ ⊢ τ ⦂ₛ σ)   →   (Δ , t) ⊢ υ ⦂ₛ σ' →
        -------------------------------------------
        Δ ⊢ (Π τ υ) ⦂ₛ σ'
  _·_ : ∀ { υ M N} → Δ ⊢ M ⦂ Π τ υ → Δ ⊢ N ⦂ₛ σ  → Δ ⊢ M · N ⦂ₛ υ

--------------------------------------------------------------------------------
-- Typing Judgments.

data _⊢_⦂_ where
  `λ : ∀ {τ υ σ M} → (t : Δ ⊢ τ ⦂ₛ σ) → (Δ , t) ⊢ M ⦂ υ  → Δ ⊢ `λ τ M ⦂ Π τ υ 
  _·_ : ∀ {τ υ M N} → Δ ⊢ M ⦂ Π τ υ → Δ ⊢ N ⦂ τ  → Δ ⊢ M · N ⦂ υ

-- =============================================================================
-- Translating Rω.  
-- =============================================================================

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

-- -- Row : Term → Term
-- -- Row s = Σ Nat (Π (Ix (var 0)) s)

-- --------------------------------------------------------------------------------
-- -- Translating typed Rω to untyped Mix.
-- --
-- -- These "flat" translations become indices to the translation of typed Rω to typed
-- -- Mix terms.

module Sym where

  -- read as "the translation of κ *has sort* ⟦ κ ⟧σ"
  ⟦_⟧σ : (κ : Rμ.Kind) → Sort
  ⟦ ★ ⟧σ = 𝓤
  ⟦ L ⟧σ = 𝓤
  ⟦ R[ κ ] ⟧σ = {!!}
  ⟦ κ `→ κ₁ ⟧σ = {!!}

--   -- read as "the translation of κ to type ⟦ κ ⟧κ"
  ⟦_⟧κ : (κ : Rμ.Kind) →  Term
  ⟦ ★ ⟧κ = ★
  ⟦ L ⟧κ = ★
  ⟦ R[ κ ] ⟧κ = {!!} -- Row ⟦ κ ⟧κ
  ⟦ κ₁ `→ κ₂ ⟧κ = Π ⟦ κ₁ ⟧κ ⟦ κ₂ ⟧κ

  ⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Term
  ⟦ U ⟧τ = {!!}
  ⟦ lab l ⟧τ = {!!}
  ⟦ ⌊ τ ⌋ ⟧τ = {!!}
  ⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ ⟦ τ₂ ⟧τ
  ⟦ `∀ κ τ ⟧τ = Π ⟦ κ ⟧κ ⟦ τ ⟧τ
  ⟦ `λ κ τ ⟧τ = `λ ⟦ κ ⟧κ ⟦ τ ⟧τ
  ⟦ τ₁ ·[ τ₂ ] ⟧τ = ⟦ τ₁ ⟧τ · ⟦ τ₂ ⟧τ

-- --------------------------------------------------------------------------------
-- -- Typed translation of kinds.

⟦_⟧κ : ∀ {Δ}{σ} → (κ : Rμ.Kind) → Δ ⊢ Sym.⟦ κ ⟧κ ⦂ₛ 𝓤
⟦ ★ ⟧κ = ★
⟦ L ⟧κ = ★
⟦ R[ κ ] ⟧κ = {!!} -- Σ Nat (Π (Ix varZ) ⟦ κ ⟧κ) 
⟦ κ₁ `→ κ₂ ⟧κ = {!!} -- Π ⟦ κ₁ ⟧κ (weaken ⟦ κ₂ ⟧κ) 

-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Typed translation of contexts.
⟦_⟧Δ : Rμ.KEnv → Context
⟦ ε ⟧Δ = ε
⟦ Δ , κ ⟧Δ = ⟦ Δ ⟧Δ , ⟦ κ ⟧κ

-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Typed translation of types.

-- -- ⟦_⟧v : ∀ {Δ}{κ} → (v : Rμ.TVar Δ κ) → ⟦ Δ ⟧Δ ⊢ Sym.⟦ (tvar v) ⟧τ ⦂ Sym.⟦ κ ⟧κ
-- -- ⟦ Z ⟧v = varZ
-- -- ⟦ S v ⟧v = {!!}

⟦_⟧τ : ∀ {Δ}{κ} → (τ : Rμ.Type Δ κ) → ⟦ Δ ⟧Δ ⊢ Sym.⟦ τ ⟧τ ⦂ₛ Sym.⟦ κ ⟧σ

⟦ tvar x ⟧τ = {!!}
⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ {!⟦ τ₂ ⟧τ!} -- Π ⟦ τ₁ ⟧τ (weaken ⟦ τ₂ ⟧τ)
⟦ `∀ κ τ ⟧τ = Π ⟦ κ ⟧κ ⟦ τ ⟧τ -- Π ⟦ κ ⟧κ ⟦ τ ⟧τ
⟦ `λ κ τ ⟧τ = {!!} -- `λ ⟦ κ ⟧κ {!!} -- ⟦ τ ⟧τ
⟦ τ₁ ·[ τ₂ ] ⟧τ = {!_·_!} -- ⟦ τ₁ ⟧τ · ⟦ τ₂ ⟧τ
-- -- --
-- -- ⟦ lab l ⟧τ = tt
-- -- ⟦ _ ▹ τ ⟧τ = ⟦ τ ⟧τ
-- -- ⟦ _ R▹ τ ⟧τ = ⟪ (Suc Zero) ⦂ Nat , `λ (Ix varZ) (weaken (weaken {!!})) ⟫ -- ⟪ (Suc Zero) ⦂ Nat , (Π (Ix varZ) {!⟦ τ ⟧τ!}) ⟫ 
-- -- ⟦ ⌊ τ ⌋ ⟧τ = ⊤ ★
-- -- -- I need to actually do substitution.
-- -- ⟦ ε ⟧τ = ⟪ Zero ⦂ Nat , `λ (Ix varZ) (⊤ ★) ⟫
-- -- -- I need renaming in symbol expressions.
-- -- ⟦ Π τ ⟧τ = Π (Ix (fst ⟦ τ ⟧τ)) (snd (weaken (⟦ τ ⟧τ)) · {!varZ!})
-- -- ⟦ Σ τ ⟧τ = Σ {!!} ({!!} · {!!})
-- -- ⟦ τ ·⌈ τ₁ ⌉ ⟧τ = {!!}
-- -- ⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}

-- -- ⟦ μ τ ⟧τ = {!!}
-- -- ⟦ ν τ ⟧τ = {!!}

-- -- ⟦ π ⇒ τ ⟧τ = {!!}
