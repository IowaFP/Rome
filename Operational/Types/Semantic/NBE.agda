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

reflectNE {κ = ★} τ            = ne τ
reflectNE {κ = L} τ            = ne τ
reflectNE {κ = R[ ★ ]} τ       = ne τ
reflectNE {κ = R[ L ]} τ       = ne τ
reflectNE {κ = κ `→ κ₁} τ     = left τ
reflectNE {κ = R[ _ `→ _ ]} τ = left τ
reflectNE {κ = R[ R[ κ ] ]} τ  = {!!}

--------------------------------------------------------------------------------
-- reification of semantic types

reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ
reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} (left τ) = ne τ
reify {κ = κ₁ `→ κ₂} (right ⟨ [] , F ⟩) = `λ (reify (F S (reflectNE {κ = κ₁} (` Z))))
reify {κ = κ₁ `→ κ₂} (right ⟨ Π l ∷ cs , F ⟩) = Π▹ l (reify (right ⟨ cs , F ⟩))
reify {κ = κ₁ `→ κ₂} (right ⟨ Σ x ∷ cs , F ⟩) = {!!}
reify {κ = R[ ★ ]} τ = τ
reify {κ = R[ L ]} τ = τ
reify {κ = R[ κ₁ `→ κ₂ ]} (left τ) = ne τ
reify {κ = R[ κ₁ `→ κ₂ ]} (right ⟨ l , ⟨ cs , F ⟩ ⟩) = l ▹ (reify (right ⟨ cs , F ⟩))
reify {κ = R[ R[ κ₁ ] ]} τ = {!!}

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
-- Simultaneous reflection & evaluation of types to Semantic Types

reflect : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ

-- ----------------------------------------
-- -- Type reflection.

reflect {κ = ★} (` x) η = η x
reflect {κ = ★} Unit η  = Unit
reflect {κ = ★} (τ₁ · τ₂) η = (reflect τ₁ η) ·V (reflect τ₂ η)
reflect {κ = ★} (τ₁ `→ τ₂) η = (reflect τ₁ η) `→ (reflect τ₂ η)
reflect {κ = ★} (`∀ κ τ) η = `∀ _ (reflect τ (↑e η))
reflect {κ = ★} (μ τ) η with reflect τ η 
... | left F = μ (ne F)
-- This is just η-expansion
... | right ⟨ w , F ⟩ = μ (`λ (F S (ne (` Z)))) 
reflect {κ = ★} ⌊ τ ⌋ η = ⌊ reflect τ η ⌋
reflect {κ = ★} (Π τ) η with reflect τ η 
... | ne x = ne (Π x)
... | l ▹ τ = Π▹ l τ
... | Π▹ l τ  = Π▹ l (go τ)
  where
    go : NormalType Δ R[ ★ ] → NormalType Δ ★
    go (ne x) = ne (Π x)
    go (l' ▹ t₂) = Π▹ l' t₂
    go (Π▹ l' t) = Π▹ l' (go t)
    go (Σ t) = {!!}
... | Σ c = {!!}
reflect {κ = ★} (Σ τ) η = Σ (reflect τ η)

-- ----------------------------------------
-- -- Label reflection.

reflect {κ = L} (` x) η = η x
reflect {κ = L} (τ₁ · τ₂) η = (reflect τ₁ η) ·V (reflect τ₂ η)
reflect {κ = L} (lab l) η = lab l
reflect {κ = L} (Π τ) η with reflect τ η 
... | ne x = ne (Π x)
... | l ▹ τ = Π▹ l τ
... | Π▹ l τ  = Π▹ l (go τ)
  where
    go : NormalType Δ R[ L ] → NormalType Δ L
    go (ne x) = ne (Π x)
    go (l' ▹ t₂) = Π▹ l' t₂
    go (Π▹ l' t) = Π▹ l' (go t)
    go (Σ t) = {!!}
... | Σ c = {!!}
reflect {κ = L} (Σ τ) η = Σ (reflect τ η)

-- ----------------------------------------
-- -- function reflection.

reflect {κ = κ₁ `→ κ₂} (` x) η = η x
reflect {κ = κ₁ `→ κ₂} (`λ τ) η = right ⟨ 
  [] , 
  (λ {Δ₃} ρ v → reflect τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v)) ⟩
reflect {κ = κ₁ `→ κ₂} (τ₁ · τ₂) η =  (reflect τ₁ η) ·V (reflect τ₂ η)
reflect {κ = κ₁ `→ κ₂} (Π τ) η with reflect τ η 
... | left x = left (Π x)
... | right ⟨ l₁ , ⟨ [] , F ⟩ ⟩         = right ⟨ Π l₁ ∷ [] , F ⟩
... | right ⟨ l₁ , ⟨ Π l₂ ∷ cs , F ⟩ ⟩ = right ⟨ Π l₁ ∷ Π l₂ ∷ cs , F ⟩
... | right ⟨ l₁ , ⟨ Σ x ∷ cs , F ⟩ ⟩ = right ⟨ {!!} , {!!} ⟩

reflect {κ = κ₁ `→ κ₂} (Σ τ) η = {!!} -- with reflect τ η
-- ... | left x = left (Π x)
-- ... | right ⟨ l , ⟨ cs , F ⟩ ⟩ = {!!} -- right ⟨ (Σ l ∷ cs) , F ⟩
reflect {κ = κ₁ `→ κ₂} (↑ τ) η = {!!}
reflect {κ = κ₁ `→ κ₂} (τ ↑) η = {!!}

-- ----------------------------------------
-- -- Row reflection.

reflect {κ = R[ κ ]} (` x) η = η x
reflect {κ = R[ κ ]} (τ₁ · τ₂) η = reflect τ₁ η ·V reflect τ₂ η
reflect {κ = R[ ★ ]} (τ₁ ▹ τ₂) η = (reflect τ₁ η) ▹ (reflect τ₂ η)
reflect {κ = R[ L ]} (τ₁ ▹ τ₂) η = (reflect τ₁ η) ▹ (reflect τ₂ η)
reflect {κ = R[ κ₁ `→ κ₂ ]} (τ₁ ▹ τ₂) η  with reflect τ₂ η 
... | left x = left ((reflect τ₁ η) ▹ x)
... | right F = right ⟨ (reflect τ₁ η) , F ⟩
reflect {κ = R[ R[ κ ] ]} (τ₁ ▹ τ₂) η = {!!}
reflect {κ = R[ κ ]} (Π τ) η = {!!}
reflect {κ = R[ κ ]} (Σ τ) η = {!!}

--------------------------------------------------------------------------------
-- Evaluation.

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
A₀ = ℓ ▹ Unit

_ : ∀ {Δ} → ⇓ (A₀ {Δ}) ≡ l ▹ Unit
_ = refl

----------------------------------------
-- Row-kinded function types.

Id-R : Type Δ R[ ★ `→ ★ ]
Id-R = ℓ ▹ (`λ (` Z))

_ : ∀ {Δ} → ⇓ (Id-R {Δ}) ≡ l ▹ (`λ (ne (` Z)))
_ = refl

apply-R : Type Δ R[ ((★ `→ ★) `→ ★ `→ ★) ]
apply-R = (ℓ₁ ▹ apply)

_ : ∀ {Δ} → ⇓ (apply-R {Δ}) ≡ (l₁ ▹ ⇓ apply)
_ = refl

----------------------------------------
-- Function types with congruences. 

C₁ : Type Δ ★
C₁ = Π (ℓ ▹ Unit)

_ : ∀ {Δ} → ⇓ (C₁ {Δ}) ≡ Π▹ l Unit
_ = refl

C₂ : Type Δ (★ `→ ★)
C₂ = Π (ℓ ▹ (`λ (` Z)))

_ : ∀ {Δ} → ⇓ (C₂ {Δ}) ≡ Π▹ l (`λ (ne (` Z)))
_ = refl 

C₃ : Type Δ R[ ★ ]
C₃ = Π (ℓ₁ ▹ (ℓ₂ ▹ ((apply · Const-U) · Unit)))

_ : ∀ {Δ} → ⇓ (C₃ {Δ}) ≡ (l₁ ▹ Π▹ l₂ Unit)
_ = {!⇓ C₃!}


-- ----------------------------------------
-- -- Tricky business.

-- -- These types imply my definition of semantic types at row kind is inaccurate:
-- -- I am working under the assumption that where there's a row there's a label---
-- -- which is sort of true---but not necessarily of canonical form.  My
-- -- representation is a bit fucked for the following terms.
-- -- I doubt also that normalization is stable: 
-- --   ∀ τ. ⇓ (embed τ) ≡ τ

shit₁ : Type Δ ★
shit₁ = Π (Π (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

_ : ⇓ shit₁ ≡ Π▹ l₁ (Π▹ l₂ Unit)
_ = {!!}

shit₂ : Type Δ (★ `→ ★)
shit₂ = Π (ℓ₁ ▹ (Π (ℓ₂ ▹ ID)))

_ : ⇓ shit₂ ≡ Π▹ l₁ (Π▹ l₂ (⇓ ID))
_ = {!reflect shit₂!}

lift-L  : Type Δ ((★ `→ ★) `→ ★)
lift-L = `λ (Π (((` Z) ↑) · (ℓ ▹ Unit))) -- `λ Π ((ℓ₁ ▹ (λ x.

_ : ⇓ lift-L ≡ `λ (Π▹ l (ne ((` Z) · Unit)))
_ = {!⇓ hmm!}


-- --------------------------------------------------------------------------------
-- -- Claims.

-- -- row-canonicity : (r : Type Δ R[ κ ]) → ∃[ x ] ∃[ τ ] ((⇓ r ≡ (x ▹ τ)) or isNE (⇓ r))
-- -- row-canonicity (` x) = {!!}
-- -- row-canonicity (r · r₁) = {!!}
-- -- row-canonicity (r ▹ r₁) = {!!}
-- -- row-canonicity (Π r) with ⇓ r 
-- -- ... | c = ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩
-- -- row-canonicity (Σ r) = {!!}
