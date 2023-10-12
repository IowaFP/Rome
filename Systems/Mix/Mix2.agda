module Mix.Mix2 where

open import Preludes.Data
open import Data.List
open import Preludes.Relation
open import Data.Nat using (_⊔_)

----------------------------------------------------------------------------------
-- following Xi & Pfenning 99.


--------------------------------------------------------------------------------
-- Index sorts.

data ISort : Set where
  Nat : ISort
  ⊤ : ISort
  _*_ : ISort → ISort → ISort

--------------------------------------------------------------------------------
-- 

data IContext : Set where
  ε : IContext
  _,_ : IContext → ISort → IContext

private
  variable
    Ξ : IContext

data IObject : IContext → Set where
  ivar : ℕ → IObject Ξ
  ⊤    : IObject Ξ
  ⟨_,_⟩ : IObject Ξ → IObject Ξ → IObject Ξ

data Type : IContext → Set where
  δ     : (Ξ : ISort) → IObject Ξ → Type Ξ
  ⊤     : Type Ξ
  _*_   : Type Ξ → Type Ξ → Type Ξ
  _`→_ : Type Ξ → Type Ξ → Type Ξ
  Π     : (i : ISort) → Type (Ξ , i) → Type Ξ
  Σ     : (i : ISort) → Type (Ξ , i) → Type Ξ

--------------------------------------------------------------------------------
-- Interpretation of type level.

module Rμ where
 open import Rome.Kinds.Syntax public
 open import Rome.Types.Syntax public
 open import Rome.Terms.Syntax public

open Rμ.Kind
open Rμ.KEnv
open Rμ.Type
open Rμ.TVar
open Rμ.Term

⟦_⟧κ : Rμ.Kind →  Type Ξ
⟦ ★ ⟧κ =  ⊤ --- This makes little sense.
⟦ L ⟧κ = ⊤
⟦ R[ κ ] ⟧κ = Σ Nat ⟦ κ ⟧κ -- Here be problems...
⟦ κ₁ `→ κ₂ ⟧κ = ⟦ κ₁ ⟧κ `→ ⟦ κ₂ ⟧κ


data Env : IContext → Set where
  ε : Env Ξ
  _,_ : Env Ξ → Type Ξ → Env Ξ
  _,'_   : Env Ξ → (i : ISort) → Env (Ξ , i)

private
  variable
    Δ : Env Ξ
    τ τ₁ τ₂ : Type Ξ

⟦_⟧τ : ∀ {Δ}{κ} → Rμ.Type Δ κ → ∃[ τ ] (⟦ κ ⟧κ ≡ τ)
⟦ U ⟧τ = ⊤ , refl
⟦ tvar x ⟧τ = {!!}
⟦ τ₁ `→ τ₂ ⟧τ = {!!} , {!!} -- ⟦ τ₁ ⟧τ `→ ⟦ τ₂ ⟧τ
⟦ `∀ κ c ⟧τ = {!!}
⟦ `λ κ₁ c ⟧τ = {!!} -- Π {!δ!} {!!}
⟦ c ·[ c₁ ] ⟧τ = {!!}
⟦ μ c ⟧τ = {!!}
⟦ ν c ⟧τ = {!!}
⟦ π' ⇒ c ⟧τ = {!!}
⟦ lab l ⟧τ = {!!}
⟦ c ▹ c₁ ⟧τ = {!!}
⟦ c R▹ c₁ ⟧τ = {!!}
⟦ ⌊ c ⌋ ⟧τ = {!!}
⟦ ε ⟧τ = {!!}
⟦ Π c ⟧τ = {!!}
⟦ Σ c ⟧τ = {!!}
⟦ c ·⌈ c₁ ⌉ ⟧τ = {!!}
⟦ ⌈ c ⌉· c₁ ⟧τ = {!!}

data Term : (Ξ : IContext) → (Δ : Env Ξ) → Type Ξ → Set where
  -- later---Intrinsic De Bruijn nonsense
  var : ℕ → Term Ξ Δ τ
  ⟨⟩   : Term Ξ Δ ⊤
  ⟨_,_⟩ : Term Ξ Δ (τ₁ * τ₂)

  -- As per XiP99 (and, as I suspected) we need to separate
  -- term, type, and index abstraction / application / &c.
  --
  -- Terms depending on terms.
  `λ   : ∀ (τ₁ : Type Ξ) → (τ₂ : Type Ξ) (M : Term Ξ (Δ , τ₁) τ₂) → Term Ξ Δ (τ₁ `→ τ₂)
  -- Terms depending on sorts.
  `λⁱ   : ∀ {Ξ} (i : ISort) {Δ : Env Ξ} → (τ₂ : Type (Ξ , i)) (M : Term (Ξ , i) (Δ ,' i) τ₂) → Term Ξ Δ (Π i τ₂)
  
  


--------------------------------------------------------------------------------
-- Let's look at our real needs: the translation of terms...

⟦_⟧ : Rμ.Term → Term Ξ Δ τ 

  

