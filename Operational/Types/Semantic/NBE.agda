{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.NBE where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (lift ; Renaming)
open import Rome.Operational.Types.Properties

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.Renaming


--------------------------------------------------------------------------------
-- reflection of neutral types
reflectNE : ∀ {κ} → NeutralType Δ κ → SemType Δ κ
-- ρeflectNE : ∀ {κ} → NeutralType Δ R[ κ ] → Σ[ n ∈ ℕ ] (SemType-R Δ κ n)

reflectNE {κ = ★} τ = ne τ
reflectNE {κ = L} τ = ne τ
reflectNE {κ = κ `→ κ₁} τ = left τ
reflectNE {κ = R[ ★ ]} τ = ne τ
reflectNE {κ = R[ L ]} τ = ne τ
reflectNE {κ = R[ _ `→ _ ]} τ = left τ
reflectNE {κ = R[ R[ κ ] ]} τ = {!!}

--------------------------------------------------------------------------------
-- reification of semantic types

reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ
reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} (left τ) = ne τ
reify {κ = κ₁ `→ κ₂} (right ⟨ [] , F ⟩) = `λ (reify (F S (reflectNE {κ = κ₁} (` Z))))
reify {κ = κ₁ `→ κ₂} (right ⟨ (x ▹) ∷ cs , F ⟩) = x ▹ (reify (right ⟨ cs , F ⟩))
reify {κ = κ₁ `→ κ₂} (right ⟨ ΠR▹ x ∷ cs , F ⟩) = Π (x R▹ (reify (right ⟨ cs , F ⟩))) -- x R▹ (reify (right ⟨ cs , F ⟩))
reify {κ = κ₁ `→ κ₂} (right ⟨ ΣR▹ x ∷ cs , F ⟩) = Σ (x R▹ (reify (right ⟨ cs , F ⟩)))
reify {κ = R[ ★ ]} τ = τ
reify {κ = R[ L ]} τ = τ
reify {κ = R[ κ₁ `→ κ₂ ]} (left τ) = ne τ
reify {κ = R[ κ₁ `→ κ₂ ]} (right ⟨ l , ⟨ cs , F ⟩ ⟩) = l R▹ reify (right ⟨ cs , F ⟩)
reify {κ = R[ R[ κ₁ ] ]} τ = {!!}
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
-- extende (weakenSem {Δ = Δ₂} {κ₁ = {!κ'!}} {κ₂ = {!!}} ∘ η {κ = {!κ!}}) (reflectNE {κ = κ} (` Z))
↑e {Δ₁} {Δ₂} {κ} η  = extende η' V -- extende η' V
  where
    η' : Env Δ₁ (Δ₂ ,, κ)
    η' {κ'} v = (weakenSem {Δ = Δ₂} {κ₁ = κ'} {κ₂ = κ}) (η v)

    V  : SemType (Δ₂ ,, κ) κ
    V = reflectNE {κ = κ} (` Z)


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
reflect-→ {Δ₁} {κ₁} {κ₂} {Δ₂} (`λ τ) η = 
  right ⟨ [] , 
    (λ {Δ₃} ρ v → reflect τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v)) ⟩
reflect-→ (τ₁ · τ₂) η =  (reflect τ₁ η) ·V (reflect τ₂ η)
reflect-→ (ℓ ▹ τ₂) η with reflect-→ τ₂ η 
... | left τ = left ((reflect ℓ η) ▹ τ)
... | right ⟨ w , f ⟩ = right ⟨ reflect ℓ η ▹ ∷ w , f ⟩
reflect-→ (Π τ) η with reflect-R τ η
... | left x = left (Π x)
... | right ⟨ l , ⟨ cs , F ⟩ ⟩ = right ⟨ (ΠR▹ l ∷ cs) , F ⟩
reflect-→ (Σ τ) η with reflect-R τ η
... | left x = left (Π x)
... | right ⟨ l , ⟨ cs , F ⟩ ⟩ = right ⟨ (ΣR▹ l ∷ cs) , F ⟩
reflect-→ (↑ τ) η = {!!}
reflect-→ (τ ↑) η = {!!}

reflect-R (` x) η = η x 
reflect-R (τ₁ · τ₂) η = reflect τ₁ η ·V reflect τ₂ η
reflect-R {κ = ★} (τ₁ ▹ τ₂) η = (reflect-L τ₁ η) ▹ (reflect-R τ₂ η)
reflect-R {κ = L} (τ₁ ▹ τ₂) η = (reflect-L τ₁ η) ▹ (reflect-R τ₂ η)
reflect-R {κ = κ₁ `→ κ₂} (τ₁ ▹ τ₂) η with reflect-R τ₂ η 
... | left x = left ((reflect-L τ₁ η) ▹ x)
... | right ⟨ l , ⟨ cs , F ⟩ ⟩ = right ⟨ (reflect-L τ₁ η) , ⟨ (l ▹) ∷ cs , F ⟩ ⟩
reflect-R {κ = R[ κ ]} (τ₁ ▹ τ₂) η = {!!}
reflect-R {κ = ★} (τ₁ R▹ τ₂) η = (reflect-L τ₁ η) R▹ (reflect τ₂ η)
reflect-R {κ = L} (τ₁ R▹ τ₂) η = (reflect-L τ₁ η) R▹ (reflect τ₂ η)
reflect-R {κ = κ₁ `→ κ₂} (τ₁ R▹ τ₂) η  with reflect-→ τ₂ η 
... | left x = left ((reflect-L τ₁ η) R▹ x)
... | right ⟨ cs , F ⟩ = right ⟨ (reflect-L τ₁ η) , ⟨ cs , F ⟩ ⟩
reflect-R {κ = R[ κ ]} (τ₁ R▹ τ₂) η = {!!}
reflect-R (Π τ) η = {!!} -- Π (reflect-R τ η)
reflect-R (Σ τ) η = {!!} -- Π (reflect-R τ η)

-- ignoring:


idEnv : Env Δ Δ
idEnv = reflectNE ∘ `

-- NormalType forms.
⇓ : Type Δ κ → NormalType Δ κ
⇓ τ = reify (reflect τ idEnv)

--------------------------------------------------------------------------------
-- Testing.

----------------------------------------
-- Labels.

ℓ ℓ₁ ℓ₂ ℓ₃ : Type Δ L
ℓ  = lab "l"
ℓ₁ = lab "l1"
ℓ₂ = lab "l2"
ℓ₃ = lab "l3"

----------------------------------------
-- Some function types.

apply : Type Δ ((★ `→ ★) `→ ★ `→ ★)
apply = (`λ (`λ ((` (S Z)) · (` Z))))

ID : Type Δ (★ `→ ★)
ID = `λ (` Z)

Const-U : Type Δ (★ `→ ★)
Const-U = `λ Unit

_ : Type Δ (★ `→ ★)
_ = {!⇓ Const-U!}

----------------------------------------
-- Simple terms.

A₀ : Type Δ ★
A₀ = (lab "l") ▹ Unit

_ = {!!} 

----------------------------------------
-- Row-kinded function types.

constR : Type Δ R[ ★ `→ ★ ]
constR = ℓ R▹ (`λ (` Z))

_ = {!⇓ constR!}


----------------------------------------
-- Terms with congruences.

C₁ : Type Δ ((★ `→ ★) `→ ★ `→ ★)
C₁ = (ℓ₁ ▹ (ℓ₂ ▹ apply))

C₂ : Type Δ ★
C₂ = (ℓ₁ ▹ (ℓ₂ ▹ ((apply · Const-U) · Unit)))

C₃ : Type Δ ★
C₃ = Π (ℓ R▹ Unit)

C₄ : Type Δ (★ `→ ★)
C₄ = Π (ℓ R▹ (`λ (` Z)))

-- This case is broken. See C-c C-n below.
C₅ : Type Δ (R[ ★ `→ ★ ])
C₅ = ℓ₁ ▹ (ℓ₂ R▹ ((`λ (` Z))))

_ : {!⇓ C₅!}

