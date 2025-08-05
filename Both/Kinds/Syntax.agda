{-# OPTIONS --safe #-}
module Rome.Both.Kinds.Syntax where

open import Rome.Both.Prelude
open import Rome.Preludes.Level

private
  variable
      ι ι₁ ι₂ ι₃ : Level

--------------------------------------------------------------------------------
-- 2.1 Kinds

data Kind : Level → Set where
  ★     : Kind ι
  L     : Kind ι 
  _`→_ : Kind ι₁ → Kind ι₂ → Kind (ι₁ ⊔ ι₂)
  R[_]  : Kind ι → Kind ι

infixr 5 _`→_

--------------------------------------------------------------------------------
-- Partitioning of kinds by labels and label-valued functions

NotLabel : Kind ι → Set 
NotLabel ★ = ⊤
NotLabel L = ⊥
NotLabel (κ₁ `→ κ₂) = NotLabel κ₂
NotLabel R[ κ ] = NotLabel κ

notLabel? : ∀ (κ : Kind ι) → Dec (NotLabel κ)
notLabel? ★ = yes tt
notLabel? L = no λ ()
notLabel? (κ `→ κ₁) = notLabel? κ₁
notLabel? R[ κ ] = notLabel? κ


--------------------------------------------------------------------------------
-- Partitioning of kinds by row/arrow kind

Ground : Kind ι → Set 
Ground ★ = ⊤
Ground L = ⊤
Ground (κ `→ κ₁) = ⊥
Ground R[ κ ] = ⊥

ground? : ∀ (κ : Kind ι) → Dec (Ground κ)
ground? ★ = yes tt
ground? L = yes tt
ground? (_ `→ _) = no (λ ())
ground? R[ _ ] = no (λ ())

--------------------------------------------------------------------------------
-- contexts

data KEnv : Level → Set where
  ∅ : KEnv ι 
  _,,_ : KEnv ι₁ → Kind ι₂ → KEnv (ι₁ ⊔ ι₂)

--------------------------------------------------------------------------------
-- Type variables

private
  variable
    Δ Δ₁ Δ₂ Δ₃ : KEnv ι
    κ κ₁ κ₂ : Kind ι

data TVar : KEnv ι₁ → Kind ι₂ → Set where
  Z : TVar (Δ ,, κ) κ
  S : TVar Δ κ₁ → TVar (Δ ,, κ₂) κ₁
