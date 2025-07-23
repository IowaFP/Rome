{-# OPTIONS --safe #-}
module Rome.Kinds.Syntax where

open import Rome.Prelude

--------------------------------------------------------------------------------
-- 2.1 Kinds

data Kind : Set where
  ★     : Kind
  L     : Kind
  _`→_ : Kind → Kind → Kind
  R[_]  : Kind → Kind

infixr 5 _`→_

--------------------------------------------------------------------------------
-- Partitioning of kinds by labels and label-valued functions

NotLabel : Kind → Set 
NotLabel ★ = ⊤
NotLabel L = ⊥
NotLabel (κ₁ `→ κ₂) = NotLabel κ₂
NotLabel R[ κ ] = NotLabel κ

notLabel? : ∀ κ → Dec (NotLabel κ)
notLabel? ★ = yes tt
notLabel? L = no λ ()
notLabel? (κ `→ κ₁) = notLabel? κ₁
notLabel? R[ κ ] = notLabel? κ


--------------------------------------------------------------------------------
-- Partitioning of kinds by row/arrow kind

Ground : Kind → Set 
Ground ★ = ⊤
Ground L = ⊤
Ground (κ `→ κ₁) = ⊥
Ground R[ κ ] = ⊥

ground? : ∀ κ → Dec (Ground κ)
ground? ★ = yes tt
ground? L = yes tt
ground? (_ `→ _) = no (λ ())
ground? R[ _ ] = no (λ ())

--------------------------------------------------------------------------------
-- contexts

data KEnv : Set where
  ∅ : KEnv
  _,,_ : KEnv → Kind → KEnv

--------------------------------------------------------------------------------
-- Type variables

private
  variable
    Δ Δ₁ Δ₂ Δ₃ : KEnv
    κ κ₁ κ₂ : Kind

data KVar : KEnv → Kind → Set where
  Z : KVar (Δ ,, κ) κ
  S : KVar Δ κ₁ → KVar (Δ ,, κ₂) κ₁
