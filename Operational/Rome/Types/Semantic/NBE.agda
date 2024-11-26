module Operational.Rome.Types.Semantic.NBE where

open import Operational.Rome.Prelude
open import Operational.Rome.Kinds.Syntax
open import Operational.Rome.Kinds.GVars

open import Operational.Rome.Types.Syntax
open import Operational.Rome.Types.Renaming using (↑ ; Renaming)
open import Operational.Rome.Types.Properties

open import Operational.Rome.Types.Normal.Syntax
open import Operational.Rome.Types.Semantic.Syntax
open import Operational.Rome.Types.Semantic.Renaming


--------------------------------------------------------------------------------
-- reflection of neutral types
reflectNE : ∀ {κ} → NeutralType Δ κ → SemType Δ κ
-- ρeflectNE : ∀ {κ} → NeutralType Δ R[ κ ] → Σ[ n ∈ ℕ ] (SemType-R Δ κ n)

reflectNE {κ = ★} τ = ne τ
reflectNE {κ = L} τ = ne τ
reflectNE {κ = R[ κ ]} τ = ne τ
reflectNE {κ = κ `→ κ₁} τ = left τ

-- ρeflectNE {κ = ★} τ = {!!} -- ne τ
-- ρeflectNE {κ = L} τ = {!!} -- ne τ
-- ρeflectNE {κ = _ `→ _} τ = {!!} -- left τ -- left τ
-- ρeflectNE {κ = R[ κ ]} τ = {!!} -- ρeflectNE {κ = {!!}} {n = {!!}} {!!}

--------------------------------------------------------------------------------
-- reification of semantic types

-- conglue : SemFunction Δ₁ κ₁ κ₂ → NormalType Δ₁ (κ₁ `→ κ₂)
reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ

-- conglue ⟨ [] , F ⟩ = `λ (reify ((F S (reflectNE (` Z)))))
-- conglue ⟨ (ℓ ▹) ∷ xs , F ⟩ = ℓ ▹ (conglue ⟨ xs , F ⟩)
-- conglue ⟨ Π ∷ xs , F ⟩ = Π {!conglue ⟨ xs , F ⟩!}
-- conglue ⟨ Σ ∷ xs , F ⟩ = {!!}
-- conglue ⟨ R ∷ xs , F ⟩ = {!!}


reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = R[ κ' ]} τ = {!!} -- τ
reify {κ = κ₁ `→ κ₂} (left τ) = ne τ
reify {κ = κ₁ `→ κ₂} (right ⟨ [] , F ⟩) = `λ (reify ((F S (reflectNE (` Z)))))
reify {κ = κ₁ `→ κ₂} (right ⟨ (x ▹) ∷ ws , F ⟩) = x ▹ (reify (right ⟨ ws , F ⟩))



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
right ⟨ w , F ⟩ ·V V = F id V


--------------------------------------------------------------------------------
-- Reflection of types

reflect : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
reflect-★ : Type Δ₁ ★ → Env Δ₁ Δ₂ → SemType Δ₂ ★
reflect-L : Type Δ₁ L → Env Δ₁ Δ₂ → SemType Δ₂ L
reflect-R : Type Δ₁ R[ κ ] → Env Δ₁ Δ₂ → SemType Δ₂ R[ κ ]
reflect-→ : Type Δ₁ (κ₁ `→ κ₂) → Env Δ₁ Δ₂ → SemType Δ₂ (κ₁ `→ κ₂)

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
... | right ⟨ w , F ⟩ = μ (`λ (F S (ne (` Z)))) 
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
reflect-→ (`λ τ) η = right ⟨ [] , (λ ρ v → reflect τ (extende (renSem ρ ∘ η) v)) ⟩
reflect-→ (τ₁ · τ₂) η =  (reflect τ₁ η) ·V (reflect τ₂ η)
reflect-→ (τ₁ ▹ τ₂) η with reflect-→ τ₂ η 
... | left τ = left ((reflect τ₁ η) ▹ τ)
... | right ⟨ w , f ⟩ = right ⟨ reflect τ₁ η ▹ ∷ w , f ⟩
reflect-→ (Π τ) η with reflect-R τ η
... | c = {!!}
reflect-→ (Σ τ) η = {!!}
reflect-→ (↑ τ) η = {!!}
reflect-→ (τ ↑) η = {!!}

reflect-R (` x) η = η x 
reflect-R (τ₁ · τ₂) η = reflect τ₁ η ·V reflect τ₂ η
reflect-R (τ₁ ▹ τ₂) η = {!!} -- (reflect-L τ₁ η) ▹ (reflect-R τ₂ η)
reflect-R (τ₁ R▹ τ₂) η = {!!} -- (reflect-L τ₁ η) R▹ {!!}
reflect-R (Π τ) η = {!!} -- Π (reflect-R τ η)
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

_ : _
_ = {! ⇓ t₀ !}

--------------------------------------------------------------------------------
-- 3.3. Completeness of type normalization.
--
-- Completeness states that normalizing two β-equal types yields the same normal
-- form. In other words, `nf` is injective: normalization picks out unique
-- representations for normal forms.
--
-- (OMITTED).


