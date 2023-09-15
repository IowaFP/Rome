{-# OPTIONS --safe #-}
module F.Terms.Syntax where

open import Agda.Primitive

open import F.Kinds
open import F.Types
open import F.Types.Substitution

--------------------------------------------------------------------------------
-- Environments.

data Env : {ℓ : Level} → KEnv ℓ → Level → Set where
  ε : ∀ {ℓΔ} {Δ : KEnv ℓΔ} →
        Env Δ lzero
  _,_ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓκ} →
          Env Δ ℓΓ → Type Δ (★ ℓκ) → Env Δ (ℓΓ ⊔ ℓκ)

-- Weakening of the kinding env.
weakΓ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓκ} {κ : Kind ℓκ} →
        Env Δ ℓΓ → Env (Δ , κ) ℓΓ
weakΓ ε = ε
weakΓ (Γ , τ) = weakΓ Γ , rename S τ

--------------------------------------------------------------------------------
-- Variables.

data Var : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓκ} {κ : Kind ℓκ} →
           Env Δ ℓΓ → Type Δ κ → Set where
  Z : ∀ {ℓΔ : Level} {Δ : KEnv ℓΔ} {ℓΓ}
        {Γ : Env Δ ℓΓ} {ℓτ} {τ : Type Δ (★ ℓτ)} →
        Var (Γ , τ) τ
  S : ∀ {ℓΔ : Level} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ}
        {ℓυ ℓτ} {τ : Type Δ (★ ℓτ)} {υ : Type Δ (★ ℓυ)} →
         Var Γ υ → Var (Γ , τ) υ        

--------------------------------------------------------------------------------
-- Terms.

data Term : ∀ {ℓΔ} (Δ : KEnv ℓΔ) {ℓΓ ℓτ} → Env Δ ℓΓ → Type Δ (★ ℓτ) → Set where
  ------------------------------------------------------------
  -- System Fω.
  
  var : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓτ} {Γ : Env Δ ℓΓ} {τ : Type Δ (★ ℓτ)} →

           Var Γ τ →
           -------------
           Term Δ Γ τ
  
  `λ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓτ ℓυ} {Γ : Env Δ ℓΓ} {υ : Type Δ (★ ℓυ)}

           (τ : Type Δ (★ ℓτ)) → Term Δ (Γ , τ) υ →
           -------------------------------------
           Term Δ Γ (τ `→ υ)

  _·_ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ ℓτ ℓυ} {Γ : Env Δ ℓΓ} {τ : Type Δ (★ ℓτ)} {υ : Type Δ (★ ℓυ)} →

           Term Δ Γ (τ `→ υ) → Term Δ Γ τ →
           ----------------------------
           Term Δ Γ υ

  `Λ : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ}
         {ℓκ ℓτ} (κ : Kind ℓκ) {τ : Type (Δ , κ) (★ ℓτ)} →

       Term (Δ , κ) (weakΓ Γ) τ →
       ----------------------------------------------------
       Term Δ Γ (`∀ κ τ)

  _·[_] : ∀ {ℓΔ} {Δ : KEnv ℓΔ} {ℓΓ} {Γ : Env Δ ℓΓ} {ℓκ ℓτ}
            {κ : Kind ℓκ} {τ : Type (Δ , κ) (★ ℓτ)} →

           Term Δ Γ (`∀ κ τ) → (υ : Type Δ κ) →
           ----------------------------------
           Term Δ Γ (τ β[ υ ])
 
