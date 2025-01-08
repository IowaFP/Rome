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

reflectNE {κ = ★} τ            = ne τ
reflectNE {κ = L} τ            = ne τ
reflectNE {κ = R[ ★ ]} τ       = ne τ
reflectNE {κ = R[ L ]} τ       = ne τ
reflectNE {κ = κ `→ κ₁} τ     = left τ
reflectNE {κ = R[ _ `→ _ ]} τ = left (ne τ) 
reflectNE {κ = R[ R[ κ ] ]} τ = left (ne τ)

--------------------------------------------------------------------------------
-- reification of semantic types

reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ
reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} (left τ) = ne τ
reify {κ = κ₁ `→ κ₂} (right ( [] , F )) = `λ (reify (F S (reflectNE {κ = κ₁} (` Z))))
reify {κ = κ₁ `→ κ₂} (right ( Π l ∷ cs , F )) with flat? κ₂
... | yes p = Π (l ▹ (reify (right (cs , F)))) p -- Π (l ▹ (reify (right (cs , F)))) {!   !}
... | no  p with = `λ {!  !}  -- ne (Π (l ▹ (reify (right (cs , F))))) -- Π▹ l (reify (right ( cs , F )))
reify {κ = κ₁ `→ κ₂} (right ( Σ l ∷ cs , F )) = {!   !} -- ne (Σ (l ▹ (reify (right (cs , F)))))
reify {κ = R[ ★ ]} τ = τ
reify {κ = R[ L ]} τ = τ
reify {κ = R[ κ₁ `→ κ₂ ]} (left τ) = τ
reify {κ = R[ κ₁ `→ κ₂ ]} (right ( l , ( cs , F ) )) = {!   !} 
reify {κ = R[ R[ κ₁ ] ]} (left x) = {!   !}
reify {κ = R[ R[ κ₁ ] ]} (right ( l , τ )) = {!   !} -- ne (l ▹ (reify τ)) -- l ▹ (reify τ)

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

idEnv : Env Δ Δ
idEnv = reflectNE ∘ `

--------------------------------------------------------------------------------
-- Semantic application
_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
left A ·V V = reflectNE (A · (reify V))
right ( w , F ) ·V V = F id V


--------------------------------------------------------------------------------
-- Semantic type function constants


-- _▵_ : SemType Δ L → SemType Δ κ → SemType Δ R[ κ ]
-- _▵_ {κ = ★} ℓ τ = row (ℓ ▹ τ) -- ℓ ▹ τ
-- _▵_ {κ = L} ℓ τ = row (ℓ ▹ τ) -- ℓ ▹ τ
-- _▵_ {κ = κ₁ `→ κ₂} ℓ (left x) = left {!   !}
-- _▵_ {κ = κ₁ `→ κ₂} ℓ (right (cs , F)) = {!   !} -- left (ℓ ▹ reify (right (cs , F))) 
-- _▵_ {κ = R[ κ ]} ℓ τ = {!   !} -- left (ℓ ▹ (reify τ))

-- π : SemType Δ R[ κ ] → SemType Δ κ
-- π {κ = ★} (ne x) = ne (Π x)
-- π {κ = L} (ne x) = ne (Π x)
-- π {κ = κ₁ `→ κ₂} (left x) = left (Π x)
-- π {κ = κ₁ `→ κ₂} (right ( ℓ , ( cs , F ) )) = right ( ((Π ℓ) ∷ cs) , F )
-- π {Δ} {κ = R[ κ ]} (left t) = go t
--   where
--     go : ∀ {κ} → NeutralType Δ R[ κ ] → SemType Δ κ
--     go {★} t = π {Δ} {★} (reflectNE t)
--     go {L} t = π {Δ} {L} (reflectNE t)
--     go {κ₁ `→ κ₂} t = left (Π t)
--     go {R[ ★ ]} t = ne (Π t)
--     go {R[ L ]} t = ne (Π t)
--     go {R[ κ₁ `→ κ₂ ]} t = left (Π t)
--     go {R[ R[ κ ] ]} t = left (Π t)
-- π {Δ} {κ = R[ κ ]} (right ( ℓ , τ )) = ℓ ▵ (π τ)

-- σ : SemType Δ R[ κ ] → SemType Δ κ
-- σ {κ = ★} (ne x) = ne (Σ x)
-- σ {κ = L} (ne x) = ne (Σ x)
-- σ {κ = κ₁ `→ κ₂} (left x) = left (Σ x)
-- σ {κ = κ₁ `→ κ₂} (right ( ℓ , ( cs , F ) )) = right ( ((Σ ℓ) ∷ cs) , F )
-- σ {Δ} {κ = R[ κ ]} (left t) = go t
--   where
--     go : ∀ {κ} → NeutralType Δ R[ κ ] → SemType Δ κ
--     go {★} t = σ {Δ} {★} (reflectNE t)
--     go {L} t = σ {Δ} {L} (reflectNE t)
--     go {κ₁ `→ κ₂} t = left (Σ t)
--     go {R[ ★ ]} t = ne (Σ t)
--     go {R[ L ]} t = ne (Σ t)
--     go {R[ κ₁ `→ κ₂ ]} t = left (Σ t)
--     go {R[ R[ κ ] ]} t = left (Σ t)
-- σ {Δ} {κ = R[ κ ]} (right ( ℓ , τ )) = ℓ ▵ (σ τ)

-- -- ----------------------------------------
-- -- -- Type reflection.

-- reflect : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
-- reflect {κ = ★} (` x) η = η x
-- reflect {κ = ★} Unit η  = Unit
-- reflect {κ = ★} (τ₁ · τ₂) η = (reflect τ₁ η) ·V (reflect τ₂ η)
-- reflect {κ = ★} (τ₁ `→ τ₂) η = (reflect τ₁ η) `→ (reflect τ₂ η)
-- reflect {κ = ★} (`∀ κ τ) η = `∀ _ (reflect τ (↑e η))
-- reflect {κ = ★} (μ τ) η with reflect τ η 
-- ... | left F = μ (ne F)
-- ... | right ( w , F ) = μ (`λ (F S (ne (` Z)))) 
-- reflect {κ = ★} ⌊ τ ⌋ η = ⌊ reflect τ η ⌋

-- -- ----------------------------------------
-- -- -- Label reflection.

-- reflect {κ = L} (` x) η = η x
-- reflect {κ = L} (τ₁ · τ₂) η = (reflect τ₁ η) ·V (reflect τ₂ η)
-- reflect {κ = L} (lab l) η = lab l

-- -- ----------------------------------------
-- -- -- function reflection.

-- reflect {κ = κ₁ `→ κ₂} (` x) η = η x
-- reflect {κ = κ₁ `→ κ₂} (`λ τ) η = right ( 
--   [] , 
--   (λ {Δ₃} ρ v → reflect τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v)) )
-- reflect {κ = κ₁ `→ κ₂} (τ₁ · τ₂) η =  (reflect τ₁ η) ·V (reflect τ₂ η)
-- reflect {κ = κ₁ `→ κ₂} Π η = right ( [] , (λ {κ} ρ v → π v) )
-- reflect {κ = κ₁ `→ κ₂} Σ η = right ( [] , (λ ρ v → σ v) )
-- reflect {κ = _} `▹` η = right ( [] , (λ ρ₁ l → right ( [] , (λ ρ₂ v → (renSem {κ = L} ρ₂ l) ▵ v) )) )
-- -- reflect {κ = κ₁ `→ κ₂} (↑ τ) η = {!!}
-- -- reflect {κ = κ₁ `→ κ₂} (τ ↑) η = {!!}

-- -- ----------------------------------------
-- -- -- Row reflection.

-- reflect {κ = R[ κ ]} (` x) η = η x
-- reflect {κ = R[ κ ]} (τ₁ · τ₂) η = reflect τ₁ η ·V reflect τ₂ η

-- --------------------------------------------------------------------------------
-- -- Evaluation.

-- -- NormalType forms.
-- ⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
-- ⇓ τ = reify (reflect τ idEnv)

-- --------------------------------------------------------------------------------
-- -- Testing.

-- ----------------------------------------
-- -- Labels.

-- ℓ ℓ₁ ℓ₂ ℓ₃ : Type Δ L
-- l l₁ l₂ l₃ : NormalType Δ L
-- ℓ  = lab "l"
-- l  = lab "l"

-- ℓ₁ = lab "l1"
-- l₁ = lab "l1"

-- ℓ₂ = lab "l2"
-- l₂ = lab "l2"

-- ℓ₃ = lab "l3"
-- l₃ = lab "l3"

-- ----------------------------------------
-- -- Some function types.

-- apply : Type Δ ((★ `→ ★) `→ ★ `→ ★)
-- apply = (`λ (`λ ((` (S Z)) · (` Z))))

-- _ : ∀ {Δ} → ⇓ (apply {Δ}) ≡ `λ (`λ (ne (` (S Z) · ne (` Z)))) -- (`λ (`λ ((` ?) · ?)))
-- _ = refl

-- apply₂ : Type Δ (★ `→ (★ `→ ★) `→ ★)
-- apply₂ = `λ (`λ ((` Z) · (` (S Z))))

-- _ : ∀ {Δ} → ⇓ (apply₂ {Δ}) ≡ `λ (`λ (ne (` Z · ne (` (S Z)))))
-- _ = refl

-- ID : Type Δ (★ `→ ★)
-- ID = `λ (` Z)

-- _ : ∀ {Δ} → ⇓ (ID {Δ}) ≡ `λ (ne (` Z))
-- _ = refl

-- Const-U : Type Δ (★ `→ ★)
-- Const-U = `λ Unit

-- _ : ∀ {Δ} → ⇓ (Const-U {Δ}) ≡ `λ Unit
-- _ = refl

-- ----------------------------------------
-- -- Simple terms.

-- A₀ : Type Δ R[ ★ ]
-- A₀ = (`▹` · ℓ) · Unit

-- _ : ∀ {Δ} → ⇓ (A₀ {Δ}) ≡ ne (l ▹ Unit)
-- _ = refl

-- ----------------------------------------
-- -- Row-kinded function types.

-- Id-R : Type Δ R[ ★ `→ ★ ]
-- Id-R = (`▹` · ℓ) · (`λ (` Z))

-- _ : ∀ {Δ} → ⇓ (Id-R {Δ}) ≡ ne (l ▹ (`λ (ne (` Z))))
-- _ = refl

-- apply-R : Type Δ R[ ((★ `→ ★) `→ ★ `→ ★) ]
-- apply-R = (`▹` · ℓ₁) · apply

-- _ : ∀ {Δ} → ⇓ (apply-R {Δ}) ≡ ne ((l₁ ▹ ⇓ apply))
-- _ = refl

-- ----------------------------------------
-- -- Function types with congruences. 

-- -- C₁ : Type Δ ★
-- -- C₁ = Π · (ℓ ▹ Unit)

-- -- _ : ∀ {Δ} → ⇓ (C₁ {Δ}) ≡ Π▹ l Unit
-- -- _ = refl

-- -- C₂ : Type Δ (★ `→ ★)
-- -- C₂ = Π · (ℓ ▹ (`λ (` Z)))

-- -- _ : ∀ {Δ} → ⇓ (C₂ {Δ}) ≡ Π▹ l (`λ (ne (` Z)))
-- -- _ = refl 

-- -- C₃ : Type Δ ★
-- -- C₃ = Π · (ℓ₁ ▹ (Π · (ℓ₂ ▹ ((apply · Const-U) · Unit))))

-- -- _ : ∀ {Δ} → ⇓ (C₃ {Δ}) ≡ Π▹ l₁ (Π▹ l₂ Unit)
-- -- _ = refl


-- -- -- -- ----------------------------------------
-- -- -- -- -- Unreduced Π applications

-- -- NR₀ : Type Δ ★
-- -- NR₀ = Π · (Π · (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

-- -- _ : ⇓ {Δ = Δ} NR₀ ≡ Π▹ l₁ (Π▹ l₂ Unit)
-- -- _ = refl 

-- -- NR₁ : Type Δ (★ `→ ★)
-- -- NR₁ = Π · (ℓ₁ ▹ (Π  · (ℓ₂ ▹ ID)))

-- -- _ : ⇓ {Δ = Δ} NR₁ ≡ Π▹ l₁ (Π▹ l₂ (⇓ ID))
-- -- _ = refl


-- -- NR₂ : Type Δ R[ ★ ]
-- -- NR₂ = Π · (ℓ₁ ▹ (ℓ₂ ▹ ((apply · Const-U) · Unit)))

-- -- _ : ∀ {Δ} → ⇓ (NR₂ {Δ}) ≡ l₁ ▹ (Π▹ l₂ Unit)
-- -- _ = refl

-- -- NR₃ : Type Δ R[ ★ `→ ★ ]
-- -- NR₃ = Π · (ℓ₁ ▹ (ℓ₂ ▹ ID))

-- -- _ : ⇓ {Δ = Δ} NR₃ ≡ l₁ ▹ (Π▹ l₂ (⇓ ID))
-- -- _ = refl

-- -- NR₄ : Type Δ R[ R[ ★ ] ]
-- -- NR₄ = Π · (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ Unit)))

-- -- _ : ⇓ {Δ = Δ} NR₄ ≡ l₁ ▹ (l₂ ▹ (Π▹ l₃ Unit))
-- -- _ = refl

-- -- NR₅ : Type Δ R[ R[ ★ `→ ★ ] ]
-- -- NR₅ = Π · (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ ID)))

-- -- _ : ⇓ {Δ = Δ} NR₅ ≡ l₁ ▹ (l₂ ▹ (Π▹ l₃ (⇓ ID)))
-- -- _ = refl

-- -- -- -- NR₄ and NR₅ do not agree. This is bad.

-- -- NR₆ : Type Δ R[ R[ R[ ★ `→ ★ ] ] ]
-- -- NR₆ = Π · (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ (ℓ ▹ ID))))

-- -- _ : ⇓ {Δ = Δ} NR₆ ≡ (l₁ ▹ (l₂ ▹ (l₃ ▹ (Π▹ l (⇓ ID)))))
-- -- _ = refl


-- -- -- ----------------------------------------
-- -- -- -- Mixed Π and Σ w/ unreduced computation

-- -- mix₀ : Type Δ ★
-- -- mix₀ = Π · (Σ · (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

-- -- _ : ⇓ {Δ = Δ} mix₀ ≡ Π▹ l₁ (Σ▹ l₂ Unit)
-- -- _ = {!refl!}


-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Lifting nonsense

-- -- -- lift-L  : Type Δ ((★ `→ ★) `→ ★)
-- -- -- lift-L = `λ (Π (((` Z) ↑) · (ℓ ▹ Unit))) -- `λ Π ((ℓ₁ ▹ (λ x.

-- -- -- _ : ⇓ {Δ = Δ} lift-L ≡ `λ (Π▹ l (ne ((` Z) · Unit)))
-- -- -- _ = {!⇓ lift-L!}



-- -- -- -- --------------------------------------------------------------------------------
-- -- -- -- -- Claims.

-- -- -- -- -- row-canonicity : (r : Type Δ R[ κ ]) → ∃[ x ] ∃[ τ ] ((⇓ r ≡ (x ▹ τ)) or isNE (⇓ r))
-- -- -- -- -- row-canonicity (` x) = {!!}
-- -- -- -- -- row-canonicity (r · r₁) = {!!}
-- -- -- -- -- row-canonicity (r ▹ r₁) = {!!}
-- -- -- -- -- row-canonicity (Π r) with ⇓ r 
-- -- -- -- -- ... | c = ( {!!} , ( {!!} , {!!} ) )
-- -- -- -- -- row-canonicity (Σ r) = {!!}
 