module Rome.Operational.Types.Semantic.Tests where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (lift ; Renaming)
open import Rome.Operational.Types.Properties

open import Rome.Operational.Types.Normal.Syntax
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

A₀ : Type Δ ★
A₀ = ℓ ▹ Unit

_ : ∀ {Δ} → ⇓ (A₀ {Δ}) ≡ l ▹ Unit
_ = refl

----------------------------------------
-- Row-kinded function types.

constR : Type Δ R[ ★ `→ ★ ]
constR = ℓ R▹ (`λ (` Z))

_ : ∀ {Δ} → ⇓ (constR {Δ}) ≡ l R▹ (`λ (ne (` Z)))
_ = refl


----------------------------------------
-- Function types with congruences. 

C₁ : Type Δ ((★ `→ ★) `→ ★ `→ ★)
C₁ = (ℓ₁ ▹ (ℓ₂ ▹ apply))

_ : ∀ {Δ} → ⇓ (C₁ {Δ}) ≡ (l₁ ▹ (l₂ ▹ (⇓ apply)))
_ = refl


C₂ : Type Δ ★
C₂ = (ℓ₁ ▹ (ℓ₂ ▹ ((apply · Const-U) · Unit)))

_ : ∀ {Δ} → ⇓ (C₂ {Δ}) ≡ (l₁ ▹ (l₂ ▹ Unit))
_ = refl

C₃ : Type Δ ★
C₃ = Π (ℓ R▹ Unit)

_ : ∀ {Δ} → ⇓ (C₃ {Δ}) ≡ Π (l R▹ Unit)
_ = refl

C₄ : Type Δ (★ `→ ★)
C₄ = Π (ℓ R▹ (`λ (` Z)))

_ : ∀ {Δ} → ⇓ (C₄ {Δ}) ≡ Π (l R▹ `λ (ne (` Z)))
_ = refl

C₅ : Type Δ (R[ ★ `→ ★ ])
C₅ = ℓ₁ ▹ (ℓ₂ R▹ ((`λ (` Z))))

C₆ : Type Δ (R[ ★ `→ ★ ])
C₆ = ℓ₁ R▹ (ℓ₂ ▹ ((`λ (` Z))))

-- an equivalence that shouldn't be happening
_ : ∀ {Δ} → ⇓ (C₅ {Δ}) ≡ ⇓ (C₆ {Δ})
_ = {!reflect C₅!}

-- what about even further nesting...
