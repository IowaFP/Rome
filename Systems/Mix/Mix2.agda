module Mix.Mix2 where

open import Preludes.Data
open import Data.List
open import Preludes.Relation
open import Data.Nat using (_⊔_)

----------------------------------------------------------------------------------
-- following Xi & Pfenning 99.


--------------------------------------------------------------------------------
-- Index sorts.

-- data ISort : Set where
--   Nat : ISort
--   ⊤ : ISort
--   _*_ : ISort → ISort → ISort

-- --------------------------------------------------------------------------------
-- -- 

-- data IContext : Set where
--   ε : IContext
--   _,_ : IContext → ISort → IContext

-- private
--   variable
--     Ξ : IContext

-- data IObject : IContext → Set where
--   ivar : ℕ → IObject Ξ 
--   ⊤    : IObject Ξ
--   ⟨_,_⟩ : IObject Ξ → IObject Ξ → IObject Ξ

-- data ISort : Set
-- data IObject : ISort

-- data ISort where
--   Nat : ISort
--   Ix  : 
data Context : Set
data Type : Context → Set 

data Context where
  ε : Context
  _,_ : (Ξ : Context) → Type Ξ → Context

private
  variable
    Δ : Context
data Type where
  -- "sorts"
  ★    : Type Δ
  Nat  : Type Δ
  Ix   : Type Δ → Type Δ
  --
  Zero : Type Δ
  Suc  : Type Δ → Type Δ
  tvar : ℕ → Type Δ
  --
  ⊤ : Type Δ
  Π : (τ : Type Δ) → Type (Δ , τ) → Type Δ
  Σ : (τ : Type Δ) → Type (Δ , τ) → Type Δ
  _·_ : Type Δ → Type Δ → Type Δ
  _~_ : Type Δ → Type Δ → Type Δ

data Typed : (Δ : Context) → Type Δ → Set where
  ★    : Typed Δ ★
  Nat  : Typed Δ ★
  Ix   : Typed Δ Nat → Typed Δ ★
  --
  Zero : Typed Δ Nat
  Suc  : Typed Δ Nat → Typed Δ Nat
  tvar : ∀ {υ} → ℕ → Typed Δ υ
  --
  ⊤ : Typed Δ ★
  Π : {τ : Type Δ} {υ : Type (Δ , τ)} → Typed Δ τ → Typed (Δ , τ) υ → Typed Δ ★
  Σ : {τ : Type Δ} {υ : Type (Δ , τ)} → Typed Δ τ → Typed (Δ , τ) υ → Typed Δ ★
  _·_ : {τ : Type Δ} {υ : Type (Δ , τ)} → Typed Δ (Π τ υ) → Typed Δ τ → Typed (Δ , τ) ★
  _~_ : ∀ {τ υ : Type Δ} → Typed Δ τ → Typed Δ υ → Typed Δ ★
  
  -- Ix     : IObject Ξ → Type Ξ
  -- ⊤     : Type Ξ
  -- _*_   : Type Ξ → Type Ξ → Type Ξ
  -- _`→_ : Type Ξ → Type Ξ → Type Ξ
  -- Π     : (i : ISort) → Type (Ξ , i) → Type Ξ
  -- `∀    : Type Ξ  → Type Ξ → Type Ξ
  -- _·_   : Type Ξ  → Type Ξ → Type Ξ
  -- Σ     : (i : ISort) → Type (Ξ , i) → Type Ξ
  -- `∃     : Type Ξ → Type Ξ → Type Ξ

-- --------------------------------------------------------------------------------
-- -- Interpretation of type level.

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
  weaken : ∀ {τ : Type Δ} → Type Δ → Type (Δ , τ)
  weakened : ∀ {τ υ : Type Δ} → Typed Δ υ → Typed (Δ , τ) (weaken υ)
  
⟦_⟧Δ : Rμ.KEnv → Context
⟦_⟧κ : Rμ.Kind → (Δ : Rμ.KEnv) → Type ⟦ Δ ⟧Δ
⟦ ★ ⟧κ _ =  ★
⟦ L ⟧κ _ = ⊤
⟦ R[ κ ] ⟧κ Δ = Σ Nat (Π (Ix (tvar 0)) (weaken (weaken (⟦ κ ⟧κ Δ))))
⟦ κ₁ `→ κ₂ ⟧κ Δ = Π (⟦ κ₁ ⟧κ Δ ) (weaken (⟦ κ₂ ⟧κ Δ))


-- data Env : IContext → Set where
--   ε : Env Ξ
--   _,_ : Env Ξ → Type Ξ → Env Ξ
--   _,'_   : Env Ξ → (i : ISort) → Env (Ξ , i)

-- private
--   variable
--     Δ : Env Ξ
--     τ τ₁ τ₂ : Type Ξ

⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → Typed ⟦ Δ ⟧Δ (⟦ κ ⟧κ Δ)
⟦_⟧Δ = {!!}

⟦ U ⟧τ = ⊤
⟦ tvar x ⟧τ = {!!}
⟦ τ₁ `→ τ₂ ⟧τ = Π ⟦ τ₁ ⟧τ (weakened ⟦ τ₂ ⟧τ )
⟦ `∀ κ τ ⟧τ = {!!}
⟦ `λ κ₁ τ ⟧τ = {!!}
⟦ τ ·[ τ₁ ] ⟧τ = {!!}
⟦ μ τ ⟧τ = {!!}
⟦ ν τ ⟧τ = {!!}
⟦ π' ⇒ τ ⟧τ = {!!}
⟦ lab l ⟧τ = {!!}
⟦ τ ▹ τ₁ ⟧τ = {!!}
⟦ τ R▹ τ₁ ⟧τ = {!!}
⟦ ⌊ τ ⌋ ⟧τ = {!!}
⟦ ε ⟧τ = {!!}
⟦ Π τ ⟧τ = {!!}
⟦ Σ τ ⟧τ = {!!}
⟦ τ ·⌈ τ₁ ⌉ ⟧τ = {!!}
⟦ ⌈ τ ⌉· τ₁ ⟧τ = {!!}

-- ⟦ ε ⟧τ = Σ Nat ((Ix (ivar 0)) `→ ⊤)
-- ⟦ Π ρ ⟧τ = ∃ Nat (`∀ (Ix (ivar 0)) (⟦ ρ ⟧τ · tvar 0))
-- ⟦ Σ ρ ⟧τ = Σ Nat (`∃ (Ix (ivar 0)) (⟦ ρ ⟧τ · tvar 0))
-- ⟦ c ·⌈ c₁ ⌉ ⟧τ = {!!}
-- ⟦ ⌈ c ⌉· c₁ ⟧τ = {!!}
-- ⟦ U ⟧τ = ⊤
-- ⟦ tvar x ⟧τ = {!!}
-- ⟦ τ₁ `→ τ₂ ⟧τ = ⟦ τ₁ ⟧τ `→ ⟦ τ₂ ⟧τ
-- ⟦ `∀ κ c ⟧τ = {!!}
-- ⟦ `λ κ₁ c ⟧τ = {!!} -- Π {!δ!} {!!}
-- ⟦ c ·[ c₁ ] ⟧τ = {!!}
-- ⟦ μ c ⟧τ = {!!}
-- ⟦ ν c ⟧τ = {!!}
-- ⟦ π' ⇒ c ⟧τ = {!!}
-- ⟦ lab l ⟧τ = {!!}
-- ⟦ c ▹ c₁ ⟧τ = {!!}
-- ⟦ c R▹ c₁ ⟧τ = {!!}
-- ⟦ ⌊ c ⌋ ⟧τ = {!!}

-- data Term : (Ξ : IContext) → (Δ : Env Ξ) → Type Ξ → Set where
--   -- later---Intrinsic De Bruijn nonsense
--   var : ℕ → Term Ξ Δ τ
--   ⟨⟩   : Term Ξ Δ ⊤
--   ⟨_,_⟩ : Term Ξ Δ (τ₁ * τ₂)
--   -- Terms depending on terms.
--   `λ   : ∀ (τ₁ : Type Ξ) → {τ₂ : Type Ξ} 
--          (M : Term Ξ (Δ , τ₁) τ₂) → Term Ξ Δ (τ₁ `→ τ₂)
--   -- Terms depending on sorts.
--   `λⁱ   : ∀ {Ξ} (i : ISort) {Δ : Env Ξ} → 
--            (τ₂ : Type (Ξ , i)) (M : Term (Ξ , i) (Δ ,' i) τ₂) → Term Ξ Δ (Π i τ₂)
  
-- --------------------------------------------------------------------------------
-- -- Let's look at our real needs: the translation of terms...

-- ⟦_⟧Δ : (Δ : Rμ.KEnv) → Rμ.Env Δ → Env Ξ
-- ⟦_⟧Δ = {!!}

-- ⟦_⟧ : ∀ {Δ : Rμ.KEnv}{Γ : Rμ.Env Δ} {Φ : Rμ.PEnv Δ}{τ : Rμ.Type Δ ★} → 
--       Rμ.Term Δ Φ Γ τ → Term Ξ (⟦ Δ ⟧Δ Γ) ⟦ τ ⟧τ
-- ⟦ var v ⟧ = {!!}
-- ⟦ `λ τ M ⟧ = {!!}
-- ⟦ M · M₁ ⟧ = {!!}
-- ⟦ `Λ κ M ⟧ = {!!}
-- ⟦ M ·[ υ ] ⟧ = {!!}
-- ⟦ `ƛ π M ⟧ = {!!}
-- ⟦ M ·⟨ x ⟩ ⟧ = {!!}
-- ⟦ lab l ⟧ = {!!}
-- ⟦ M ▹ M₁ ⟧ = {!!}
-- ⟦ M / M₁ ⟧ = {!!}
-- ⟦ (M ⊹ M₁) π ⟧ = {! Start here...!}
-- ⟦ prj M π ⟧ = {!!}
-- ⟦ Π M ⟧ = {!!}
-- ⟦ Π⁻¹ M ⟧ = {!!}
-- ⟦ t-≡ M x ⟧ = {!!}
-- ⟦ inj M x ⟧ = {!!}
-- ⟦ Σ M ⟧ = {!!}
-- ⟦ Σ⁻¹ M ⟧ = {!!}
-- ⟦ (M ▿ M₁) x ⟧ = {!!}
-- ⟦ syn ρ φ M ⟧ = {!!}
-- ⟦ ana ρ φ τ M ⟧ = {!!}
-- ⟦ Rμ.fold M M₁ M₂ M₃ ⟧ = {!!}
-- ⟦ In ⟧ = {!!}
-- ⟦ Out ⟧ = {!!}

  

