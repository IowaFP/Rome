{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.Examples where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (lift ; Renaming)
open import Rome.Operational.Types.Properties

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming
open import Rome.Operational.Types.Semantic.NBE

--------------------------------------------------------------------------------
-- Testing.

----------------------------------------
-- Labels.

ℓ ℓ₁ ℓ₂ ℓ₃ : Type Δ L
l l₁ l₂ l₃ : NormalType Δ L
ℓ  = lab "l"
l  = lab "l"

ℓ₁ = lab "l1"
l₁ = lab "l1"

ℓ₂ = lab "l2"
l₂ = lab "l2"

ℓ₃ = lab "l3"
l₃ = lab "l3"

----------------------------------------
-- Some function types.

apply : Type Δ ((★ `→ ★) `→ ★ `→ ★)
apply = (`λ (`λ ((` (S Z)) · (` Z))))

_ : ∀ {Δ} → ⇓ (apply {Δ}) ≡ `λ (`λ (ne (` (S Z) · ne (` Z)))) -- (`λ (`λ ((` ?) · ?)))
_ = refl

apply₂ : Type Δ (★ `→ (★ `→ ★) `→ ★)
apply₂ = `λ (`λ ((` Z) · (` (S Z))))

_ : ∀ {Δ} → ⇓ (apply₂ {Δ}) ≡ `λ (`λ (ne (` Z · ne (` (S Z)))))
_ = refl

ID : Type Δ (★ `→ ★)
ID = `λ (` Z)

_ : ∀ {Δ} → ⇓ (ID {Δ}) ≡ `λ (ne (` Z))
_ = refl

Const-U : Type Δ (★ `→ ★)
Const-U = `λ Unit

_ : ∀ {Δ} → ⇓ (Const-U {Δ}) ≡ `λ Unit
_ = refl

----------------------------------------
-- Simple terms.

A₀ : Type Δ R[ ★ ]
A₀ = (ℓ ▹ Unit)

_ : ∀ {Δ} → ⇓ (A₀ {Δ}) ≡ row (l ▹ Unit)
_ = refl

----------------------------------------
-- Row-kinded function types.

Id-R : Type Δ R[ ★ `→ ★ ]
Id-R = ℓ ▹ (`λ (` Z))

_ : ∀ {Δ} → ⇓ (Id-R {Δ}) ≡ row (l ▹ (`λ (ne (` Z))))
_ = refl

apply-R : Type Δ R[ ((★ `→ ★) `→ ★ `→ ★) ]
apply-R = ℓ₁ ▹ apply

_ : ∀ {Δ} → ⇓ (apply-R {Δ}) ≡ row ((l₁ ▹ ⇓ apply))
_ = refl

----------------------------------------
-- Function types with congruences. 

C₁ : Type Δ ★
C₁ = `Π (ℓ ▹ Unit)

_ : ∀ {Δ} → ⇓ (C₁ {Δ}) ≡ Π (l ▹ Unit)
_ = refl

C₂ : Type Δ (★ `→ ★)
C₂ = `Π (ℓ ▹ (`λ (` Z)))

_ : ∀ {Δ} → ⇓ (C₂ {Δ}) ≡ `λ (Π (l ▹ (ne (` Z))))
_ = refl 

C₃ : Type Δ ★
C₃ = `Π (`Π (ℓ₁ ▹ (ℓ₂ ▹ ((apply · Const-U) · Unit))))

_ : ∀ {Δ} → ⇓ (C₃ {Δ}) ≡ Π (l₁ ▹ (Π (l₂ ▹ Unit)))
_ = refl


----------------------------------------
-- Unreduced Π applications

NR₀ : Type Δ ★
NR₀ = `Π (`Π (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

_ : ⇓ {Δ = Δ} NR₀ ≡ Π (l₁ ▹ (Π (l₂ ▹ Unit)))
_ = refl 

NR₁ : Type Δ (★ `→ ★)
NR₁ = `Π (ℓ₁ ▹ (`Π (ℓ₂ ▹ ID)))

_ : ⇓ {Δ = Δ} NR₁ ≡ `λ (Π (l₁ ▹ (Π (l₂ ▹ (ne (` Z))))))
_ = refl


NR₂ : Type Δ R[ ★ ]
NR₂ = `Π (ℓ₁ ▹ (ℓ₂ ▹ (((apply · Const-U) · Unit))))

_ : ∀ {Δ} → ⇓ (NR₂ {Δ}) ≡ row (l₁ ▹ (Π (l₂ ▹ Unit)))
_ = refl

NR₃ : Type Δ R[ ★ `→ ★ ]
NR₃ = `Π (ℓ₁ ▹ (ℓ₂ ▹ ID))

_ : ⇓ {Δ = Δ} NR₃ ≡ row (l₁ ▹ `λ (Π (l₂ ▹ (ne (` Z)))))
_ = refl

NR₄ : Type Δ R[ R[ ★ ] ]
NR₄ = `Π (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ Unit)))

_ : ⇓ {Δ = Δ} NR₄ ≡ row (l₁ ▹ (row (l₂ ▹ (Π (l₃ ▹ Unit)))))
_ = refl

NR₅ : Type Δ R[ R[ ★ `→ ★ ] ]
NR₅ = `Π (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ ID)))

_ : ⇓ {Δ = Δ} NR₅ ≡ row (l₁ ▹ (row (l₂ ▹ `λ (Π (l₃ ▹ ne (` Z))))))
_ = refl


NR₆ : Type Δ R[ R[ R[ ★ `→ ★ ] ] ]
NR₆ = `Π (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ (ℓ ▹ ID))))

_ : ⇓ {Δ = Δ} NR₆ ≡ row (lab "l1" ▹ row (lab "l2" ▹ row (lab "l3" ▹ `λ (Π (lab "l" ▹ ne (` Z))))))
_ = refl


-- -- ----------------------------------------
-- -- -- Mixed Π and Σ w/ unreduced computation

mix₀ : Type Δ ★
mix₀ = `Π (`Σ (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

_ : ⇓ {Δ = Δ} mix₀ ≡ Π (l₁ ▹ (Σ (l₂ ▹ Unit)))
_ = refl


-- -- --------------------------------------------------------------------------------
-- -- -- Lifting nonsense

lift-λ : Type Δ ★
lift-λ = `Π (`λ (` Z) <$> (ℓ ▹ Unit))

_ : ⇓ {Δ = Δ} lift-λ ≡ Π (lab "l" ▹ Unit)
_ = refl

lift-λ₂  : Type Δ ((★ `→ ★) `→ R[ ★ ])
lift-λ₂ = `Π (ℓ₁ ▹ (`λ (`λ (` Z) <$> (ℓ₂ ▹ Unit)))) -- `Π (ℓ₁ ▹ (`λ  (↑ · (` Z)) · (ℓ₂ ▹ Unit)))

_ : ⇓ {Δ = Δ} lift-λ₂ ≡ `λ (row (lab "l1" ▹ Π (lab "l2" ▹ Unit)))
_ = refl

lift-var : Type Δ (R[ ★ ] `→ R[ ★ ])
lift-var = `λ (`λ (` Z) <$> (` Z))

_ : ⇓ {Δ = Δ} lift-var ≡ `λ (ne (`λ (ne (` Z)) <$> ` Z))
_ = refl 

lift-assoc₁ : Type Δ ★
lift-assoc₁ =  (Π · (ℓ ▹ `λ (` Z))) · Unit

_ : ⇓ {Δ = Δ} lift-assoc₁ ≡ Π (l ▹ Unit)
_ = refl

lift-assoc₂ : Type (Δ ,, (★ `→ ★)) ★
lift-assoc₂ =  (Π · (ℓ ▹ F)) · Unit 
    where
        F = ` Z

_ : ⇓ {Δ = Δ ,, (★ `→ ★)} lift-assoc₂ ≡ Π (l ▹ ne (` Z · Unit))
_ = refl

lift-assoc₃ : Type (Δ ,, R[ ★ `→ ★ ]) ★
lift-assoc₃ =  (Π · F) · Unit
    where
        F = ` Z

lift-assoc₃' : Type (Δ ,, R[ ★ `→ ★ ]) ★
lift-assoc₃' =  Π · (F ?? Unit)
    where
        F = ` Z

_ : ⇓ {Δ = Δ ,, R[ ★ `→ ★ ]} lift-assoc₃ ≡ ⇓ {Δ = Δ ,, R[ ★ `→ ★ ]} lift-assoc₃'
_ = refl
