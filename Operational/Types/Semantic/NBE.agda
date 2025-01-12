{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.NBE where

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


--------------------------------------------------------------------------------
-- reflection of neutral types
reflectNE : ∀ {κ} → NeutralType Δ κ → SemType Δ κ

reflectNE {κ = ★} τ            = ne τ
reflectNE {κ = L} τ            = ne τ
reflectNE {κ = R[ ★ ]} τ       = ne τ
reflectNE {κ = R[ L ]} τ       = ne τ
reflectNE {κ = κ `→ κ₁} τ     = left τ
reflectNE {κ = R[ _ `→ _ ]} τ = left τ
reflectNE {κ = R[ R[ κ ] ]} τ = left (ne τ)

--------------------------------------------------------------------------------
-- reification of semantic types

reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ
reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} (left τ) = ne τ
reify {κ = κ₁ `→ κ₂} (right F) = `λ (reify (F S (reflectNE {κ = κ₁} (` Z))))
reify {κ = R[ ★ ]} τ = τ
reify {κ = R[ L ]} τ = τ
reify {κ = R[ κ₁ `→ κ₂ ]} (left τ) = ne τ
reify {κ = R[ κ₁ `→ κ₂ ]} (right (l , F)) = row (l ▹ (reify (right F))) 
reify {κ = R[ R[ κ₁ ] ]} (left x) =  x  
reify {κ = R[ R[ κ₁ ] ]} (right (l , τ)) = row (l ▹ (reify τ))

-- --------------------------------------------------------------------------------
-- -- Semantic environments

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

revname : Env Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
revname {κ = ★} η Unit = Unit
revname {κ = ★} η (ne (` x)) = η x
revname {κ = ★} η (ne (M · N)) = {!   !}
revname {κ = ★} η (ne (Π x)) = {!   !}
revname {κ = ★} η (ne (Σ x)) = {!   !}
revname {κ = ★} η (τ `→ τ₁) = {!   !}
revname {κ = ★} η (`∀ κ τ) = {!   !}
revname {κ = ★} η (μ τ) = {!   !}
revname {κ = ★} η ⌊ τ ⌋ = {!   !}
revname {κ = ★} η (Π x) = {!   !}
revname {κ = ★} η (Σ x) = {!   !}
revname {κ = L} η τ = {!   !}
revname {κ = κ `→ κ₁} η τ = {!   !}
revname {κ = R[ κ ]} η τ = {!   !}

-- --------------------------------------------------------------------------------
-- -- Semantic application

_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
left A ·V V = reflectNE (A · (reify V))
right F ·V V = F id V



--------------------------------------------------------------------------------
-- Reflecting normal types back to semantic

-- βV : Renaming Δ₁ Δ₂ → NormalType (Δ₁ ,, κ₁) κ₂ → SemType Δ κ₁ → SemType Δ₂ κ₂
-- βV {Δ₁} {Δ₂} {★} {κ₂} {Δ} ρ f τ = {!   !}
-- βV {Δ₁} {Δ₂} {L} {κ₂} {Δ} ρ f τ = {!   !}
-- βV {Δ₁} {Δ₂} {κ₁ `→ κ₃} {κ₂} {Δ} ρ f τ = {!   !}
-- βV {Δ₁} {Δ₂} {R[ κ₁ ]} {κ₂} {Δ} ρ f τ = {!   !} 

-- TODO:
-- I believe 
--    - (i) it should be possible to write reflection of normaltypes back to semantic (Duh), and
--    - (ii) It is necessary to eta-expand types like Π (ℓ ▹ λ x. x) into λ x. (ℓ ▹ Π x)
-- but it's turning out to be quite tricky, as there is a contravariance of Env Δ₁ Δ₂ inducing
-- a requirement for Renaming (Δ₁ ,, κ) Δ₂, which is impossible to produce.

reflectN : ∀ {Δ₁ Δ₂} → NormalType Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
reflectN Unit η = Unit
reflectN (row x) η = {!   !}
reflectN (τ₁ `→ τ₂) η = reflectN τ₁ η `→ reflectN τ₂ η
reflectN (`∀ κ τ) η = {!   !}
reflectN (μ τ) η = {!   !}
reflectN (lab x) η = {!   !}
reflectN ⌊ τ ⌋ η = {!   !}
reflectN (Π x) η = {!   !}
reflectN (Σ x) η = {!   !}
reflectN (ne (` x)) η = η x
reflectN (ne (A · V)) η = {!  reflectNE A ·V  reflectN V η  !}
reflectN (ne (Π x)) η = {!   !}
reflectN (ne (Σ x)) η = {!   !}
reflectN (ne (x ▹ x₁)) η = {!   !} 
reflectN {Δ₁} {Δ₂} (`λ τ) η = right (λ ρ' v → reflectN τ (extende (λ x → renSem ρ' (η x)) v))

-- --------------------------------------------------------------------------------
-- -- Semantic type function constants

_▵_ : SemType Δ L → SemType Δ κ → SemType Δ R[ κ ]
_▵_ {κ = ★} ℓ τ = row (ℓ ▹ τ) -- ℓ ▹ τ
_▵_ {κ = L} ℓ τ = row (ℓ ▹ τ) -- ℓ ▹ τ
_▵_ {κ = κ₁ `→ κ₂} ℓ (left τ) = left (ℓ ▹ τ)
_▵_ {κ = κ₁ `→ κ₂} ℓ (right F) = right (ℓ , F)
_▵_ {κ = R[ κ ]} ℓ τ = left (row (ℓ ▹ (reify τ))) 

-- -- -- TODO: Refactor these to take an environment and be mutually recursive with reflect;
-- -- -- use reflect to define the lifting of Π under a binder
πNE : NeutralType Δ R[ κ ] → SemType Δ κ 
-- πN : ∀ {Δ₁ Δ₂ Δ₃} → NormalType Δ₃ R[ κ ] → Renaming Δ₂ Δ₃ → Env Δ₁ Δ₂ → SemType Δ₃ κ
π : ∀ {Δ₁ Δ₂ Δ₃} → SemType Δ₃ R[ κ ] → Renaming Δ₂ Δ₃ → Env Δ₁ Δ₂ → SemType Δ₃ κ
-- reflect : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ

πNE {κ = ★} τ = ne (Π τ)
πNE {κ = L} τ = ne (Π τ)
πNE {κ = κ₁ `→ κ₂} τ = left (Π τ)
πNE {κ = R[ ★ ]} τ = ne (Π τ)
πNE {κ = R[ L ]} τ = ne (Π τ)
πNE {κ = R[ κ `→ κ₁ ]} τ = left (Π τ)
πNE {κ = R[ R[ κ ] ]} τ = left (ne (Π τ)) 


-- πN {κ = κ} (ne x) ρ η = πNE x
-- πN {κ = ★} (row (x ▹ x₁)) ρ η = Π (x ▹ x₁)
-- πN {κ = ★} (row (Π▹ x x₁)) ρ η = Π (x ▹ (πN x₁ ρ η))
-- πN {κ = ★} (row (Σ▹ x x₁)) ρ η = Σ (x ▹ (πN x₁ ρ η))
-- -- Need Π constructor for Label kind
-- πN {κ = L} (row τ) ρ η = {!   !}
-- πN {κ = κ₁ `→ κ₂} (row (l ▹ ne x)) ρ η = left (Π (l ▹ x))
-- πN {κ = κ₁ `→ κ₂} {Δ₁} {Δ₂} {Δ₃} (row (l ▹ `λ τ)) ρ η = right (λ ρ' v → π ((ren ρ' l) ▵ reflectN τ {!   !}) {!   !} {!   !})
-- πN {κ = κ `→ κ₁} (row (Π▹ x x₁)) ρ η = {!   !}
-- πN {κ = κ `→ κ₁} (row (Σ▹ x x₁)) ρ η = {!   !}
-- πN {κ = R[ κ ]} (row τ) ρ η = {!   !}


π {κ = ★} (ne x) ρ η = ne (Π x)
π {κ = ★} (row (l ▹ τ)) ρ η = Π (l ▹ τ)
π {κ = ★} (row (Π▹ l τ)) ρ η = Π (l ▹ (π {κ = ★} τ ρ η)) 
π {κ = ★} (row (Σ▹ l τ)) ρ η = Σ (l ▹ (π {κ = ★} τ ρ η))
π {κ = L} τ ρ η = {!   !}
π {κ = κ `→ κ₁} (left x) ρ η = left (Π x)
π {κ = κ₁ `→ κ₂} {Δ₁} {Δ₂} {Δ₃} (right (l , F)) ρ η = 
  right (λ ρ' v → π (ren ρ' l ▵ F ρ' v)  (ρ' ∘ ρ) η)
π {κ = R[ κ ]} (left (ne x)) ρ η = πNE x 
π {κ = R[ ★ ]} (left (row τ)) ρ η = {!   !}
π {κ = R[ L ]} (left (row τ)) = {!   !}
π {κ = R[ κ `→ κ₁ ]} (left (row τ)) = {!   !}
π {κ = R[ R[ κ ] ]} (left (row τ)) = {!   !}
π {κ = R[ κ ]} (right (l , τ)) ρ η = l ▵ (π τ ρ η) -- l ▵ (π τ η)


-- -- -- σ : SemType Δ R[ κ ] → SemType Δ κ
-- -- -- σ {κ = ★} (ne x) = ne (Σ x)
-- -- -- σ {κ = L} (ne x) = ne (Σ x)
-- -- -- σ {κ = κ₁ `→ κ₂} (left x) = left (Σ x)
-- -- -- σ {κ = κ₁ `→ κ₂} (right ( ℓ , ( cs , F ) )) = right ( ((Σ ℓ) ∷ cs) , F )
-- -- -- σ {Δ} {κ = R[ κ ]} (left t) = go t
-- -- --   where
-- -- --     go : ∀ {κ} → NeutralType Δ R[ κ ] → SemType Δ κ
-- -- --     go {★} t = σ {Δ} {★} (reflectNE t)
-- -- --     go {L} t = σ {Δ} {L} (reflectNE t)
-- -- --     go {κ₁ `→ κ₂} t = left (Σ t)
-- -- --     go {R[ ★ ]} t = ne (Σ t)
-- -- --     go {R[ L ]} t = ne (Σ t)
-- -- --     go {R[ κ₁ `→ κ₂ ]} t = left (Σ t)
-- -- --     go {R[ R[ κ ] ]} t = left (Σ t)
-- -- -- σ {Δ} {κ = R[ κ ]} (right ( ℓ , τ )) = ℓ ▵ (σ τ)

-- -- ----------------------------------------
-- -- -- Type reflection.


-- reflect {κ = ★} (` x) η = η x
-- reflect {κ = ★} Unit η  = Unit
-- reflect {κ = ★} (τ₁ · τ₂) η = (reflect τ₁ η) ·V (reflect τ₂ η)
-- reflect {κ = ★} (τ₁ `→ τ₂) η = (reflect τ₁ η) `→ (reflect τ₂ η)
-- reflect {κ = ★} (`∀ κ τ) η = `∀ _ (reflect τ (↑e η))
-- reflect {κ = ★} (μ τ) η with reflect τ η 
-- ... | left F = μ (ne F)
-- ... | right F = μ (`λ (F S (ne (` Z)))) 
-- reflect {κ = ★} ⌊ τ ⌋ η = ⌊ reflect τ η ⌋

-- -- -- ----------------------------------------
-- -- -- -- Label reflection.

-- reflect {κ = L} (` x) η = η x
-- reflect {κ = L} (τ₁ · τ₂) η = (reflect τ₁ η) ·V (reflect τ₂ η)
-- reflect {κ = L} (lab l) η = lab l

-- -- -- ----------------------------------------
-- -- -- -- function reflection.

-- reflect {κ = κ₁ `→ κ₂} (` x) η = η x
-- reflect {κ = κ₁ `→ κ₂} (`λ τ) η = right (λ {Δ₃} ρ v → reflect τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v))
-- reflect {κ = κ₁ `→ κ₂} (τ₁ · τ₂) η =  (reflect τ₁ η) ·V (reflect τ₂ η)
-- reflect {κ = κ₁ `→ κ₂} Π η = right (λ {Δ₃} ρ v → π v ρ η)
-- reflect {κ = κ₁ `→ κ₂} Σ η = {!  !} 
-- reflect {κ = _} `▹` η = right (λ ρ₁ l → right (λ ρ₂ v → (renSem {κ = L} ρ₂ l) ▵ v))
-- -- reflect {κ = κ₁ `→ κ₂} (↑ τ) η = {!!}
-- -- reflect {κ = κ₁ `→ κ₂} (τ ↑) η = {!!}

-- -- -- ----------------------------------------
-- -- -- -- Row reflection.

-- reflect {κ = R[ κ ]} (` x) η = η x
-- reflect {κ = R[ κ ]} (τ₁ · τ₂) η = reflect τ₁ η ·V reflect τ₂ η

-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Evaluation.

-- -- -- -- NormalType forms.
-- ⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
-- ⇓ τ = reify (reflect τ idEnv)

-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Testing.

-- -- -- ----------------------------------------
-- -- -- -- Labels.

-- -- -- ℓ ℓ₁ ℓ₂ ℓ₃ : Type Δ L
-- -- -- l τ l₂ l₃ : NormalType Δ L
-- -- -- ℓ  = lab "l"
-- -- -- l  = lab "l"

-- -- -- ℓ₁ = lab "l1"
-- -- -- l₁ = lab "l1"

-- -- -- ℓ₂ = lab "l2"
-- -- -- l₂ = lab "l2"

-- -- -- ℓ₃ = lab "l3"
-- -- -- l₃ = lab "l3"

-- -- -- ----------------------------------------
-- -- -- -- Some function types.

-- -- -- apply : Type Δ ((★ `→ ★) `→ ★ `→ ★)
-- -- -- apply = (`λ (`λ ((` (S Z)) · (` Z))))

-- -- -- _ : ∀ {Δ} → ⇓ (apply {Δ}) ≡ `λ (`λ (ne (` (S Z) · ne (` Z)))) -- (`λ (`λ ((` ?) · ?)))
-- -- -- _ = refl

-- -- -- apply₂ : Type Δ (★ `→ (★ `→ ★) `→ ★)
-- -- -- apply₂ = `λ (`λ ((` Z) · (` (S Z))))

-- -- -- _ : ∀ {Δ} → ⇓ (apply₂ {Δ}) ≡ `λ (`λ (ne (` Z · ne (` (S Z)))))
-- -- -- _ = refl

-- -- -- ID : Type Δ (★ `→ ★)
-- -- -- ID = `λ (` Z)

-- -- -- _ : ∀ {Δ} → ⇓ (ID {Δ}) ≡ `λ (ne (` Z))
-- -- -- _ = refl

-- -- -- Const-U : Type Δ (★ `→ ★)
-- -- -- Const-U = `λ Unit

-- -- -- _ : ∀ {Δ} → ⇓ (Const-U {Δ}) ≡ `λ Unit
-- -- -- _ = refl

-- -- -- ----------------------------------------
-- -- -- -- Simple terms.

-- -- -- A₀ : Type Δ R[ ★ ]
-- -- -- A₀ = (`▹` · ℓ) · Unit

-- -- -- _ : ∀ {Δ} → ⇓ (A₀ {Δ}) ≡ ne (l ▹ Unit)
-- -- -- _ = refl

-- -- -- ----------------------------------------
-- -- -- -- Row-kinded function types.

-- -- -- Id-R : Type Δ R[ ★ `→ ★ ]
-- -- -- Id-R = (`▹` · ℓ) · (`λ (` Z))

-- -- -- _ : ∀ {Δ} → ⇓ (Id-R {Δ}) ≡ ne (l ▹ (`λ (ne (` Z))))
-- -- -- _ = refl

-- -- -- apply-R : Type Δ R[ ((★ `→ ★) `→ ★ `→ ★) ]
-- -- -- apply-R = (`▹` · ℓ₁) · apply

-- -- -- _ : ∀ {Δ} → ⇓ (apply-R {Δ}) ≡ ne ((l₁ ▹ ⇓ apply))
-- -- -- _ = refl

-- -- -- ----------------------------------------
-- -- -- -- Function types with congruences. 

-- -- -- -- C₁ : Type Δ ★
-- -- -- -- C₁ = Π · (ℓ ▹ Unit)

-- -- -- -- _ : ∀ {Δ} → ⇓ (C₁ {Δ}) ≡ Π▹ l Unit
-- -- -- -- _ = refl

-- -- -- -- C₂ : Type Δ (★ `→ ★)
-- -- -- -- C₂ = Π · (ℓ ▹ (`λ (` Z)))

-- -- -- -- _ : ∀ {Δ} → ⇓ (C₂ {Δ}) ≡ Π▹ l (`λ (ne (` Z)))
-- -- -- -- _ = refl 

-- -- -- -- C₃ : Type Δ ★
-- -- -- -- C₃ = Π · (ℓ₁ ▹ (Π · (ℓ₂ ▹ ((apply · Const-U) · Unit))))

-- -- -- -- _ : ∀ {Δ} → ⇓ (C₃ {Δ}) ≡ Π▹ l₁ (Π▹ l₂ Unit)
-- -- -- -- _ = refl


-- -- -- -- -- -- ----------------------------------------
-- -- -- -- -- -- -- Unreduced Π applications

-- -- -- -- NR₀ : Type Δ ★
-- -- -- -- NR₀ = Π · (Π · (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

-- -- -- -- _ : ⇓ {Δ = Δ} NR₀ ≡ Π▹ l₁ (Π▹ l₂ Unit)
-- -- -- -- _ = refl 

-- -- -- -- NR₁ : Type Δ (★ `→ ★)
-- -- -- -- NR₁ = Π · (ℓ₁ ▹ (Π  · (ℓ₂ ▹ ID)))

-- -- -- -- _ : ⇓ {Δ = Δ} NR₁ ≡ Π▹ l₁ (Π▹ l₂ (⇓ ID))
-- -- -- -- _ = refl


-- -- -- -- NR₂ : Type Δ R[ ★ ]
-- -- -- -- NR₂ = Π · (ℓ₁ ▹ (ℓ₂ ▹ ((apply · Const-U) · Unit)))

-- -- -- -- _ : ∀ {Δ} → ⇓ (NR₂ {Δ}) ≡ l₁ ▹ (Π▹ l₂ Unit)
-- -- -- -- _ = refl

-- -- -- -- NR₃ : Type Δ R[ ★ `→ ★ ]
-- -- -- -- NR₃ = Π · (ℓ₁ ▹ (ℓ₂ ▹ ID))

-- -- -- -- _ : ⇓ {Δ = Δ} NR₃ ≡ l₁ ▹ (Π▹ l₂ (⇓ ID))
-- -- -- -- _ = refl

-- -- -- -- NR₄ : Type Δ R[ R[ ★ ] ]
-- -- -- -- NR₄ = Π · (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ Unit)))

-- -- -- -- _ : ⇓ {Δ = Δ} NR₄ ≡ l₁ ▹ (l₂ ▹ (Π▹ l₃ Unit))
-- -- -- -- _ = refl

-- -- -- -- NR₅ : Type Δ R[ R[ ★ `→ ★ ] ]
-- -- -- -- NR₅ = Π · (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ ID)))

-- -- -- -- _ : ⇓ {Δ = Δ} NR₅ ≡ l₁ ▹ (l₂ ▹ (Π▹ l₃ (⇓ ID)))
-- -- -- -- _ = refl

-- -- -- -- -- -- NR₄ and NR₅ do not agree. This is bad.

-- -- -- -- NR₆ : Type Δ R[ R[ R[ ★ `→ ★ ] ] ]
-- -- -- -- NR₆ = Π · (ℓ₁ ▹ (ℓ₂ ▹ (ℓ₃ ▹ (ℓ ▹ ID))))

-- -- -- -- _ : ⇓ {Δ = Δ} NR₆ ≡ (l₁ ▹ (l₂ ▹ (l₃ ▹ (Π▹ l (⇓ ID)))))
-- -- -- -- _ = refl


-- -- -- -- -- ----------------------------------------
-- -- -- -- -- -- Mixed Π and Σ w/ unreduced computation

-- -- -- -- mix₀ : Type Δ ★
-- -- -- -- mix₀ = Π · (Σ · (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

-- -- -- -- _ : ⇓ {Δ = Δ} mix₀ ≡ Π▹ l₁ (Σ▹ l₂ Unit)
-- -- -- -- _ = {!refl!}


-- -- -- -- -- --------------------------------------------------------------------------------
-- -- -- -- -- -- Lifting nonsense

-- -- -- -- -- lift-L  : Type Δ ((★ `→ ★) `→ ★)
-- -- -- -- -- lift-L = `λ (Π (((` Z) ↑) · (ℓ ▹ Unit))) -- `λ Π ((ℓ₁ ▹ (λ x.

-- -- -- -- -- _ : ⇓ {Δ = Δ} lift-L ≡ `λ (Π▹ l (ne ((` Z) · Unit)))
-- -- -- -- -- _ = {!⇓ lift-L!}



-- -- -- -- -- -- --------------------------------------------------------------------------------
-- -- -- -- -- -- -- Claims.

-- -- -- -- -- -- -- row-canonicity : (r : Type Δ R[ κ ]) → ∃[ x ] ∃[ τ ] ((⇓ r ≡ (x ▹ τ)) or isNE (⇓ r))
-- -- -- -- -- -- -- row-canonicity (` x) = {!!}
-- -- -- -- -- -- -- row-canonicity (r · r₁) = {!!}
-- -- -- -- -- -- -- row-canonicity (r ▹ r₁) = {!!}
-- -- -- -- -- -- -- row-canonicity (Π r) with ⇓ r 
-- -- -- -- -- -- -- ... | c = ( {!!} , ( {!!} , {!!} ) )
-- -- -- -- -- -- -- row-canonicity (Σ r) = {!!}
     
       