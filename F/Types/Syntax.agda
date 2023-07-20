{-# OPTIONS --safe #-}
module F.Types.Syntax where

open import Agda.Primitive
open import Level

open import Data.String

open import F.Kinds.Syntax

--------------------------------------------------------------------------------
-- infix OOP.

infixr 9 _`→_

--------------------------------------------------------------------------------
-- Labels are Strings.

Label : Set
Label = String

--------------------------------------------------------------------------------
-- Kinding Environments, types, and predicates.
--
-- Kinding Environments, types, and predicates are tied up together, like so:
--   - Pred references Ty, KEnv
--   - Type   references KEnv
--   - KEnv references Pred

data Type : {ℓ ι : Level} → KEnv ℓ → Kind ι →  Set

--------------------------------------------------------------------------------
-- Type vars.
data TVar : ∀ {ℓ ι} → KEnv ℓ → Kind ι → Set where
  Z : ∀ {ℓ₁ ℓ₂} {Δ : KEnv ℓ₁} {κ : Kind ℓ₂}
      → TVar (Δ , κ) κ
  S : ∀ {ℓ₁ ℓ₂ ℓ₃} {Δ : KEnv ℓ₁} {κ : Kind ℓ₂} {κ' : Kind ℓ₃}
      → TVar Δ κ → TVar (Δ , κ') κ

--------------------------------------------------------------------------------
-- Types.

data Type where
  ------------------------------------------------------------
  -- Base types (for mechanization).

  -- Unit (Mechanization.)
  U : ∀ {ℓ ι : Level} {Δ : KEnv ℓ} →

         --------------
         Type Δ (★ ι)

  ------------------------------------------------------------
  -- System Fω.

  tvar : ∀ {ℓ₁ ℓ₂ : Level} {Δ : KEnv ℓ₁} {κ : Kind ℓ₂} →

         TVar Δ κ →
         -----------
         Type Δ κ

  _`→_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {Δ : KEnv ℓ₁} →
          Type Δ (★ ℓ₂) → Type Δ (★ ℓ₃) →
          -----------------------------------
          Type Δ (★ (ℓ₂ ⊔ ℓ₃))

  `∀ :  ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {Δ : KEnv ℓ₁} →
          (κ : Kind ℓ₃) → Type (Δ , κ) (★ ℓ₂) →
          -------------------------------------
          Type Δ (★ (ℓ₂ ⊔ (lsuc ℓ₃)))


