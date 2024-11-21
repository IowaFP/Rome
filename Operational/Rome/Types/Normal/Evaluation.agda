module Operational.Rome.Types.Normal.Evaluation where

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
-- 3.2. Type Normalization algorithm
--
-- This is the NormalTypeization by Evaluation (NBE) technique:
-- 1. Define a "semantic" class of types (values);
-- 2. define "reflection" from the syntactic to the semantic;
-- 3. define "reification" from the semantic to the syntactic; 
-- 4. evaluate each syntactic type to a semantic type; then
-- 5. NormalTypeize by reifying the evaluation.

Env : KEnv → KEnv → Set
Env Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → SemType Δ₂ κ

extende : (η : Env Δ₁ Δ₂) → (V : SemType Δ₂ κ) → Env (Δ₁ ,, κ) Δ₂
extende η V Z     = V
extende η V (S x) = η x

↑e : Env Δ₁ Δ₂ → Env (Δ₁ ,, κ) (Δ₂ ,, κ)
↑e η = extende (weakenSem ∘ η) (reflect (` Z))

-- "SemType application"
_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
left A ·V V = reflect (A · (reify V))
right ⟨ w , F ⟩ ·V V = F id V


eval : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
eval-★ : Type Δ₁ ★ → Env Δ₁ Δ₂ → SemType Δ₂ ★
eval-L : Type Δ₁ L → Env Δ₁ Δ₂ → SemType Δ₂ L
eval-R : Type Δ₁ R[ κ ] → Env Δ₁ Δ₂ → SemType Δ₂ R[ κ ]
eval-→ : Type Δ₁ (κ₁ `→ κ₂) → Env Δ₁ Δ₂ → SemType Δ₂ (κ₁ `→ κ₂)

eval {κ = ★} τ η = eval-★ τ η
eval {κ = L} τ η = eval-L τ η
eval {κ = _ `→ _} τ η = eval-→ τ η
eval {κ = R[ κ ]} τ η = eval-R τ η

eval-★ (` x) η = η x
eval-★ Unit η  = Unit
eval-★ (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
eval-★ (τ₁ `→ τ₂) η = (eval-★ τ₁ η) `→ (eval-★ τ₂ η)
eval-★ (`∀ κ τ) η = `∀ _ (eval-★ τ (↑e η))
eval-★ (μ τ) η with eval-→ τ η 
... | left F = μ (ne F)
-- This is just η-expansion
... | right ⟨ w , F ⟩ = μ (`λ (F S (ne (` Z)))) 
eval-★ (τ₁ ▹ τ₂) η = eval-L τ₁ η ▹ eval-★ τ₂ η
eval-★ ⌊ τ ⌋ η = ⌊ eval-L τ η ⌋
eval-★ (Π τ) η = Π (eval-R τ η)
eval-★ (Σ τ) η = Σ (eval-R τ η)

eval-L (` x) η = η x
eval-L (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
eval-L (lab l) η = lab l
eval-L (τ₁ ▹ τ₂) η = (eval-L τ₁ η) ▹ (eval-L τ₂ η)
eval-L (Π τ) η = Π (eval-R τ η)
eval-L (Σ τ) η = Σ (eval-R τ η)

eval-→ (` x) η = η x
eval-→ (`λ τ) η = right ⟨ [] , (λ ρ v → eval τ (extende (renSem ρ ∘ η) v)) ⟩
eval-→ (τ₁ · τ₂) η =  (eval τ₁ η) ·V (eval τ₂ η)
eval-→ (τ₁ ▹ τ₂) η with eval-→ τ₂ η 
... | left τ = left ((eval τ₁ η) ▹ τ)
... | right ⟨ w , f ⟩ = right ⟨ eval τ₁ η ▹ ∷ w , f ⟩
eval-→ (Π τ) η with eval-R τ η
... | c = {!!}
eval-→ (Σ τ) η = {!!}

eval-R (` x) η = η x 
eval-R (τ₁ · τ₂) η = eval τ₁ η ·V eval τ₂ η
eval-R (τ₁ ▹ τ₂) η = (eval-L τ₁ η) ▹ (eval-R τ₂ η)
eval-R (τ₁ R▹ τ₂) η = (eval-L τ₁ η) R▹ {!!}
eval-R (Π τ) η = Π (eval-R τ η)
eval-R (Σ τ) η = Π (eval-R τ η)

idEnv : Env Δ Δ
idEnv = reflect ∘ `

-- NormalType forms.
⇓ : Type Δ κ → NormalType Δ κ
⇓ τ = reify (eval τ idEnv)

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
t₁ = ((lab "l") ▹ ((ff · Const) · Unit))

t₂ : Type Δ ★
t₂ = (lab "l") ▹ Unit

_ : _
_ = {! reify (eval t₀ idEnv)!}

--------------------------------------------------------------------------------
-- 3.3. Completeness of type normalization.
--
-- Completeness states that normalizing two β-equal types yields the same normal
-- form. In other words, `nf` is injective: normalization picks out unique
-- representations for normal forms.
--
-- (OMITTED).


