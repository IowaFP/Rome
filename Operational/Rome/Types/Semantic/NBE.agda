{-# OPTIONS --allow-unsolved-metas #-}
module Operational.Rome.Types.Semantic.NBE where

open import Operational.Rome.Prelude
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

open import Operational.Rome.Types.Syntax
open import Operational.Rome.Types.Renaming using (lift ; Renaming)
open import Operational.Rome.Types.Properties

open import Operational.Rome.Types.Normal.Syntax
open import Operational.Rome.Types.Semantic.Syntax
open import Operational.Rome.Types.Semantic.Renaming

Congruence : ∀ Δ κ₁ κ₂ → Set
Congruence Δ κ₁ κ₂ = SemFunction Δ κ₁ κ₂ → SemFunction Δ κ₁ κ₂



--------------------------------------------------------------------------------
-- reflection of neutral types
reflectNE : ∀ {κ} → NeutralType Δ κ → SemType Δ κ
reflectNM : ∀ {κ} → NormalType Δ κ → SemType Δ κ
-- ρeflectNE : ∀ {κ} → NeutralType Δ R[ κ ] → Σ[ n ∈ ℕ ] (SemType-R Δ κ n)

reflectNE {κ = ★} τ = ne τ
reflectNE {κ = L} τ = ne τ
reflectNE {κ = R[ κ ]} τ = {!!} -- ne τ
reflectNE {κ = κ `→ κ₁} τ = left τ

reflectNM {κ = ★} τ = τ
reflectNM {κ = L} τ = τ
reflectNM {κ = κ₁ `→ κ₂} (ne x) = left x
reflectNM {κ = κ₁ `→ κ₂} (`λ τ) = right λ ρ τ' → {!reflectNM τ !}
reflectNM {κ = κ₁ `→ κ₂} (τ₁ ▹ τ₂) = left (τ₁ ▹ {!!})
reflectNM {κ = κ₁ `→ κ₂} (Π τ) = {!!}
reflectNM {κ = κ₁ `→ κ₂} (Σ τ) = {!!}
reflectNM {κ = κ₁ `→ κ₂} (↑ τ) = {!!}
reflectNM {κ = κ₁ `→ κ₂} (τ ↑) = {!!}
reflectNM {κ = R[ κ ]} τ = {!!}


-- ρeflectNE {κ = ★} τ = {!!} -- ne τ
-- ρeflectNE {κ = L} τ = {!!} -- ne τ
-- ρeflectNE {κ = _ `→ _} τ = {!!} -- left τ -- left τ
-- ρeflectNE {κ = R[ κ ]} τ = {!!} -- ρeflectNE {κ = {!!}} {n = {!!}} {!!}

--------------------------------------------------------------------------------
-- reification of semantic types

reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ
reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = R[ ★ ]} τ = τ
reify {κ = R[ L ]} τ = τ
reify {κ = R[ κ₁ `→ κ₂ ]} (left τ) = ne τ
-- Impossible case... Need to make congruences intrinsic.
reify {κ = R[ κ₁ `→ κ₂ ]} (right F) = {!!} -- need lifting
reify {κ = R[ R[ κ₁ ] ]} τ = {!!}
reify {κ = κ₁ `→ κ₂} (left τ) = ne τ
reify {κ = κ₁ `→ κ₂} (right F) = `λ (reify ((F S (reflectNE (` Z)))))
-- reify {κ = _ `→ _} (right ⟨ [] , F ⟩) = `λ (reify ((F S (reflectNE (` Z)))))
-- reify {κ = _ `→ _} (right ⟨ Π , F ⟩) = Π {!!} -- `λ (reify ((F S (reflectNE (` Z)))))

-- reify {κ = R[ κ₁ `→ κ₂ ]} (right ⟨ (x R▹)  , F ⟩) = {!!}



--------------------------------------------------------------------------------
-- Semantic environments

Env : KEnv → KEnv → Set
Env Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → SemType Δ₂ κ

extende : (η : Env Δ₁ Δ₂) → (V : SemType Δ₂ κ) → Env (Δ₁ ,, κ) Δ₂
extende η V Z     = V
extende η V (S x) = η x

↑e : Env Δ₁ Δ₂ → Env (Δ₁ ,, κ) (Δ₂ ,, κ)
↑e η = extende (weakenSem ∘ η) (reflectNE (` Z))

--------------------------------------------------------------------------------
-- Semantic application
_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
left A ·V V = reflectNE (A · (reify V))
right F ·V V = F id V


--------------------------------------------------------------------------------
-- Reflection of types

reflect : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
reflect-★ : Type Δ₁ ★ → Env Δ₁ Δ₂ → SemType Δ₂ ★
reflect-L : Type Δ₁ L → Env Δ₁ Δ₂ → SemType Δ₂ L
reflect-R : Type Δ₁ R[ κ ] → Env Δ₁ Δ₂ → SemType Δ₂ R[ κ ]
reflect-→ : Type Δ₁ (κ₁ `→ κ₂) → Env Δ₁ Δ₂ → SemType Δ₂ (κ₁ `→ κ₂)

-- _▹ : NormalType Δ L → SemFunction Δ κ₁ κ₂
-- (l ▹) F ρ = 

reflect {κ = ★} τ η = reflect-★ τ η
reflect {κ = L} τ η = reflect-L τ η
reflect {κ = _ `→ _} τ η = reflect-→ τ η
reflect {κ = R[ κ ]} τ η = reflect-R τ η

reflect-★ (` x) η = η x
reflect-★ Unit η  = Unit
reflect-★ (τ₁ · τ₂) η = (reflect τ₁ η) ·V (reflect τ₂ η)
reflect-★ (τ₁ `→ τ₂) η = (reflect-★ τ₁ η) `→ (reflect-★ τ₂ η)
reflect-★ (`∀ κ τ) η = `∀ _ (reflect-★ τ (↑e η))
reflect-★ (μ τ) η with reflect-→ τ η 
... | left F = μ (ne F)
-- This is just η-expansion
... | right F = μ (`λ (F S (ne (` Z)))) 
reflect-★ (τ₁ ▹ τ₂) η = reflect-L τ₁ η ▹ reflect-★ τ₂ η
reflect-★ ⌊ τ ⌋ η = ⌊ reflect-L τ η ⌋
reflect-★ (Π τ) η = Π (reflect-R τ η)
reflect-★ (Σ τ) η = Σ (reflect-R τ η)

reflect-L (` x) η = η x
reflect-L (τ₁ · τ₂) η = (reflect τ₁ η) ·V (reflect τ₂ η)
reflect-L (lab l) η = lab l
reflect-L (τ₁ ▹ τ₂) η = (reflect-L τ₁ η) ▹ (reflect-L τ₂ η)
reflect-L (Π τ) η = Π (reflect-R τ η)
reflect-L (Σ τ) η = Σ (reflect-R τ η)

reflect-→ (` x) η = η x
reflect-→ (`λ τ) η = right (λ ρ v → reflect τ (extende (renSem ρ ∘ η) v))
reflect-→ (τ₁ · τ₂) η =  (reflect τ₁ η) ·V (reflect τ₂ η)
reflect-→ (ℓ ▹ τ₂) η with reflect-→ τ₂ η 
... | left τ = left ((reflect ℓ η) ▹ τ)
... | right F = right λ ρ τ →  reflectNM ((reflect ℓ η) ▹ (reify (F ρ τ))) -- right ⟨ reflect ℓ η ▹ ∷ w , f ⟩
reflect-→ (Π τ) η with reflect-R τ η
... | left x = left (Π x)
... | right F = {!!} -- right ⟨ Π ∷ w , f ⟩
reflect-→ (Σ τ) η with reflect-R τ η
... | left x = left (Σ x)
... | right F = {!!} -- right ⟨ Σ ∷ w , f ⟩
reflect-→ (↑ τ) η = {!!}
reflect-→ (τ ↑) η = {!!}

reflect-R (` x) η = η x 
reflect-R (τ₁ · τ₂) η = reflect τ₁ η ·V reflect τ₂ η
reflect-R {κ = ★} (τ₁ ▹ τ₂) η = (reflect-L τ₁ η) ▹ (reflect-R τ₂ η)
reflect-R {κ = L} (τ₁ ▹ τ₂) η = (reflect-L τ₁ η) ▹ (reflect-R τ₂ η)
reflect-R {κ = κ `→ κ₁} (τ₁ ▹ τ₂) η with reflect-R τ₂ η 
... | left x = left ((reflect-L τ₁ η) ▹ x)
... | right F = {!!} -- right ⟨ ((reflect-L τ₁ η) ▹ ∷ cs) , F ⟩
reflect-R {κ = R[ κ ]} (τ₁ ▹ τ₂) η = {!!}
reflect-R (τ₁ R▹ τ₂) η = {!!}
reflect-R (Π τ) η = {!Π !} -- Π (reflect-R τ η)
reflect-R (Σ τ) η = {!!} -- Π (reflect-R τ η)

idEnv : Env Δ Δ
idEnv = reflectNE ∘ `

-- NormalType forms.
⇓ : Type Δ κ → NormalType Δ κ
⇓ τ = reify (reflect τ idEnv)

--------------------------------------------------------------------------------
-- Testing.

ff : Type Δ ((★ `→ ★) `→ ★ `→ ★)
ff = (`λ (`λ ((` (S Z)) · (` Z))))

ID : Type Δ (★ `→ ★)
ID = `λ (` Z)

ℓ ℓ₁ ℓ₂ ℓ₃ : Type Δ L
ℓ  = lab "l"
ℓ₁ = lab "l1"
ℓ₂ = lab "l2"
ℓ₃ = lab "l3"

Const : Type Δ (★ `→ ★)
Const = `λ Unit

t₀ : Type Δ ((★ `→ ★) `→ ★ `→ ★)
t₀ = (ℓ₁ ▹ (ℓ₂ ▹ ff))

t₁ : Type Δ ★
t₁ = (ℓ₁ ▹ (ℓ₂ ▹ ((ff · Const) · Unit)))

t₂ : Type Δ ★
t₂ = (lab "l") ▹ Unit

t₃ : Type Δ ★
t₃ = Π (ℓ R▹ Unit)

t₄ : Type Δ (★ `→ ★)
t₄ = Π (ℓ R▹ (`λ (` Z)))

_ : {!⇓ t₀ !}

--------------------------------------------------------------------------------
-- 3.3. Completeness of type normalization.
--
-- Completeness states that normalizing two β-equal types yields the same normal
-- form. In other words, `nf` is injective: normalization picks out unique
-- representations for normal forms.
--
-- (OMITTED).


