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
reflectNE {κ = R[ R[ κ ] ]} τ = left τ

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
reify {κ = R[ R[ κ₁ ] ]} (left x) =  ne x
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


-- --------------------------------------------------------------------------------
-- -- Semantic application

_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
left A ·V V = reflectNE (A · (reify V))
right F ·V V = F id V

--------------------------------------------------------------------------------
-- Semantic combinator for labeled types

_▵_ : SemType Δ L → SemType Δ κ → SemType Δ R[ κ ]
_▵_ {κ = ★} ℓ τ = row (ℓ ▹ τ) -- ℓ ▹ τ
_▵_ {κ = L} ℓ τ = row (ℓ ▹ τ) -- ℓ ▹ τ
_▵_ {κ = κ₁ `→ κ₂} ℓ (left τ) = right (ℓ , (λ ρ v → reflectNE ((renNE ρ τ) · (reify v))))
_▵_ {κ = κ₁ `→ κ₂} ℓ (right F) = right (ℓ , F)
_▵_ {κ = R[ κ ]} ℓ τ = right (ℓ , τ)


----------------------------------------
-- Semantic combinators for Π

πNE : NeutralType Δ R[ κ ] → SemType Δ κ 
πNE {κ = ★} τ = ne (Π τ)
πNE {κ = L} τ = ne (Π τ)
πNE {κ = κ₁ `→ κ₂} τ = left (Π τ)
πNE {κ = R[ ★ ]} τ = ne (Π τ)
πNE {κ = R[ L ]} τ = ne (Π τ)
πNE {κ = R[ κ `→ κ₁ ]} τ = left (Π τ)
πNE {κ = R[ R[ κ ] ]} τ = left (Π τ)

π : ∀ {Δ₁ Δ₂ Δ₃} → SemType Δ₃ R[ κ ] → Renaming Δ₂ Δ₃ → Env Δ₁ Δ₂ → SemType Δ₃ κ
π {κ = ★} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (ne x) ρ η = ne (Π x)
π {κ = ★} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (row r) ρ η = Π r
π {κ = L} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (ne x) ρ η = ne (Π x)
π {κ = L} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (row r) ρ η = ΠL r
π {κ = κ₁ `→ κ₂} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (left x) ρ η = left (Π x)
π {κ = κ₁ `→ κ₂} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (right (l , F)) ρ η = right (λ ρ' v → π (ren ρ' l ▵ F ρ' v)  (ρ' ∘ ρ) η)
π {κ = R[ ★ ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (left x) ρ η = ne (Π x)
π {κ = R[ ★ ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (right (l , τ)) ρ η = row (l ▹ (reify (π {κ = ★} τ ρ η)))
π {κ = R[ L ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (left x) ρ η = ne (Π x)
π {κ = R[ L ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (right (l , τ)) ρ η = row (l ▹ (reify (π {κ = L} τ ρ η)))
π {κ = R[ κ₁ `→ κ₂ ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (left x) ρ η = left (Π x)
π {κ = R[ κ₁ `→ κ₂ ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (right (l , left τ)) ρ η = _▵_ {κ = κ₁ `→ κ₂} l (πNE {κ = κ₁ `→ κ₂} τ)
π {κ = R[ κ₁ `→ κ₂ ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (right (l , τ)) ρ η = _▵_ {κ = κ₁ `→ κ₂} l (π {κ = κ₁ `→ κ₂} τ id idEnv)
π {κ = R[ R[ κ ] ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (left x) ρ η = left (Π x)
π {κ = R[ R[ κ ] ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (right (l , left τ)) ρ η = _▵_ {κ = R[ κ ]} l (πNE {κ = R[ κ ]} τ)
π {κ = R[ R[ κ ] ]} {Δ₁ = Δ₁} {Δ₂} {Δ₃} (right (l , τ)) ρ η =  _▵_ {κ = R[ κ ]} l (π {κ = R[ κ ]} τ id idEnv)

----------------------------------------
-- Semantic combinator for Σ

σNE : NeutralType Δ R[ κ ] → SemType Δ κ 
σNE = {!   !}
σ : ∀ {Δ₁ Δ₂ Δ₃} → SemType Δ₃ R[ κ ] → Renaming Δ₂ Δ₃ → Env Δ₁ Δ₂ → SemType Δ₃ κ
σ = {!   !}

----------------------------------------
-- Semantic combinator for Lifting

-- N.b. this is 
_<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
_<$>V_ {κ₁ = ★} {★} (left F) (ne τ) = ne ((ne F) <$> τ)
_<$>V_ {κ₁ = ★} {L} (left F) (ne τ) = ne ((ne F) <$> τ)
_<$>V_ {κ₁ = ★} {κ₂ `→ κ₃} (left F) (ne τ) = left (((ne F) <$> τ))
_<$>V_ {κ₁ = ★} {R[ κ₂ ]} (left F) (ne τ) = left (((ne F) <$> τ))
_<$>V_ {κ₁ = ★} {κ₂} (left x) (row (l ▹ τ)) = l ▵ ((left x) ·V τ)

_<$>V_ {κ₁ = L} {★} (left F) (ne τ) = ne ((ne F) <$> τ)
_<$>V_ {κ₁ = L} {L} (left F) (ne τ) = ne ((ne F) <$> τ)
_<$>V_ {κ₁ = L} {κ₂ `→ κ₃} (left F) (ne τ) = left (((ne F) <$> τ))
_<$>V_ {κ₁ = L} {R[ κ₂ ]} (left F) (ne τ) = left (((ne F) <$> τ))
_<$>V_ {κ₁ = L} {κ₂} (left x) (row (l ▹ τ)) = l ▵ ((left x) ·V τ)

_<$>V_ {κ₁ = κ₁ `→ κ₂} {★} (left F) (left τ) = ne ((ne F) <$> τ)
_<$>V_ {κ₁ = κ₁ `→ κ₂} {★} (left F) (right (l , G)) = _▵_ {κ = ★} l (ne (F · reify (right G)))
_<$>V_ {κ₁ = κ₁ `→ κ₂} {L} (left F) (left τ) = ne ((ne F) <$> τ)
_<$>V_ {κ₁ = κ₁ `→ κ₂} {L} (left F) (right (l , G)) = _▵_ {κ = L} l (ne (F · reify (right G)))
_<$>V_ {κ₁ = κ₁ `→ κ₂} {κ₃ `→ κ₄} (left F) (left τ) = left ((ne F) <$> τ)
_<$>V_ {κ₁ = κ₁ `→ κ₂} {κ₃ `→ κ₄} (left F) (right (l , G)) = {! left F  !} ·V {!   !}
_<$>V_ {κ₁ = κ₁ `→ κ₂} {R[ κ₃ ]} (left F) τ = {!   !}

_<$>V_ {κ₁ = R[ κ₁ ]} {κ₂} (left x) τ = {!   !}

_<$>V_ {κ₁ = κ₁} {κ₂} (right y) τ = {!   !}
-- _<$>V_ {κ₁ = κ₁} {κ₂} (left x) τ = reflectNE (↑ x · (reify τ))
-- _<$>V_ {κ₁ = ★} {★} f@(right F) (ne x) = ne ((reify f) ↑· x)
-- _<$>V_ {κ₁ = ★} {L} f@(right F) (ne x) = ne ((reify f) ↑· x)
-- _<$>V_ {κ₁ = ★} {κ₂ `→ κ₃} f@(right F) (ne x) = left (reify f ↑· x)
-- _<$>V_ {κ₁ = ★} {R[ κ₂ ]} f@(right F) (ne x) = left (reify f ↑· x)
-- _<$>V_ {κ₁ = ★} {κ₂} (right F) (row (l ▹ τ)) = l ▵ (F id τ)
-- _<$>V_ {κ₁ = L} {★} f@(right F) (ne x) = ne ((reify f) ↑· x)
-- _<$>V_ {κ₁ = L} {L} f@(right F) (ne x) = ne ((reify f) ↑· x)
-- _<$>V_ {κ₁ = L} {κ₂ `→ κ₃} f@(right F) (ne x) = left (reify f ↑· x)
-- _<$>V_ {κ₁ = L} {R[ κ₂ ]} f@(right F) (ne x) = left (reify f ↑· x)
-- _<$>V_ {κ₁ = L} {κ₂} (right F) (row (l ▹ τ)) = l ▵ (F id τ)
-- _<$>V_ {κ₁ = κ₁ `→ κ₂} {★} f@(right F) (left x) = ne (((reify f) ↑· x))
-- _<$>V_ {κ₁ = κ₁ `→ κ₂} {L} f@(right F) (left x) = ne (((reify f) ↑· x))
-- _<$>V_ {κ₁ = κ₁ `→ κ₂} {κ₃ `→ κ₄} f@(right F) (left x) = left ((reify f) ↑· x) 
-- _<$>V_ {κ₁ = κ₁ `→ κ₂} {R[ κ₃ ]} f@(right F) (left x) = left ((reify f) ↑· x) 
-- _<$>V_ {κ₁ = κ₁ `→ κ₂} {★} f@(right F) g@(right (l , G)) = row (l ▹ F id (right G)) 
-- _<$>V_ {κ₁ = κ₁ `→ κ₂} {L} f@(right F) g@(right (l , G)) = row (l ▹ F id (right G))
-- _<$>V_ {κ₁ = κ₁ `→ κ₂} {κ₃ `→ κ₄} f@(right F) g@(right (l , G)) with F id (right G) 
-- ... | left x = right (l , λ ρ v → reflectNE (renNE ρ x) ·V v)
-- ... | right y = right (l , y)
-- _<$>V_ {κ₁ = κ₁ `→ κ₂} {R[ κ₃ ]} (right F) (right (l , G)) = right (l , (F id (right G)))
-- _<$>V_ {κ₁ = R[ κ₁ ]} {★} f@(right F) (left x) = ne (reify f ↑· x)
-- _<$>V_ {κ₁ = R[ κ₁ ]} {★} f@(right F) (right (l , τ)) = row (l ▹ (F id τ))
-- _<$>V_ {κ₁ = R[ κ₁ ]} {L} f@(right F) (left x) = ne (reify f ↑· x)
-- _<$>V_ {κ₁ = R[ κ₁ ]} {L} f@(right F) (right (l , τ)) = row (l ▹ (F id τ))
-- _<$>V_ {κ₁ = R[ κ₁ ]} {κ₂ `→ κ₃} f@(right F) (left x) = left ((reify f) ↑· x)
-- _<$>V_ {κ₁ = R[ κ₁ ]} {κ₂ `→ κ₃} f@(right F) (right (l , τ)) with F id τ
-- ... | left x = right (l , λ ρ v → reflectNE (renNE ρ x) ·V v)
-- ... | right y = right (l , y)
-- _<$>V_ {κ₁ = R[ κ₁ ]} {R[ κ₂ ]} f@(right F) (left x) = left ((reify f) ↑· x)
-- _<$>V_ {κ₁ = R[ κ₁ ]} {R[ κ₂ ]} f@(right F) (right (l , τ)) = right (l , (F id τ)) 

----------------------------------------
-- Evaluation of neutral terms to Semantic.
-- N.b. that Types are simultaneously evaluated 
-- and reflected; neutral types and normal types
-- require an environment for reflection so that bodies 
-- of lambdas may be extended.

-- evalNE : ∀ {Δ₁ Δ₂} → NeutralType Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
-- reflect : ∀ {Δ₁ Δ₂} → NormalType Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
-- reflectRow : ∀ {Δ₁ Δ₂} → Row Δ₁ R[ κ ] → Env Δ₁ Δ₂ → SemType Δ₂ R[ κ ]

-- evalNE (` x) η = η x
-- evalNE (τ · x) η = (evalNE τ η) ·V (reflect x η)
-- evalNE {κ = ★} (Π τ) η with evalNE τ η 
-- ... | ne x = ne (Π x)
-- ... | row x = Π x
-- evalNE {κ = L} (Π τ) η with evalNE τ η 
-- ... | ne x = ne (Π x)
-- ... | row x = ΠL x
-- evalNE {κ = κ₁ `→ κ₂} {Δ₁} {Δ₂} (Π τ) η with evalNE τ η 
-- ... | left x = left (Π x)
-- ... | right (l , F) = right (λ {Δ₃} ρ v → π {κ = κ₂} ((renSem {κ = L} ρ l) ▵ F ρ v) ρ η)
-- evalNE {κ = R[ κ ]} (Π τ) η = π (evalNE τ η) id η
-- evalNE {κ = R[ κ₁ ] `→ R[ κ₂ ]} {Δ₁} {Δ₂} (↑ F) η = rmap (evalNE F η)
-- evalNE {κ = R[ κ₂ ] } {Δ₁} {Δ₂} (F ↑· x) η = (reflect F η) <$>V (evalNE x η)
-- evalNE (Σ τ) η = {!   !}

-- ----------------------------------------
-- -- Reflection & evaluation of normal terms to semantic.

-- reflect {κ = κ₁ `→ κ₂} {Δ₁} {Δ₂} (`λ τ) η = right (λ ρ v → reflect τ (extende (λ x → renSem ρ (η x)) v))
-- reflect Unit η = Unit
-- reflect (ne x) η = evalNE x η
-- reflect (row x) η = reflectRow x η
-- reflect (τ₁ `→ τ₂) η = (reflect τ₁ η) `→ (reflect τ₂ η)
-- reflect (`∀ κ τ) η = `∀ κ (reflect τ (↑e η))
-- reflect (μ τ) η with reflect τ η 
-- ... | left F = μ (ne F)
-- ... | right F = μ (`λ (F S (ne (` Z)))) 
-- reflect (lab x) η = lab x
-- reflect ⌊ τ ⌋ η = ⌊ reflect τ η ⌋
-- reflect (Π (l ▹ τ)) η = Π ((reflect l η) ▹ reflect τ η)
-- reflect (ΠL (l ▹ τ)) η = ΠL ((reflect l η) ▹ reflect τ η)
-- reflect (Σ (l ▹ τ)) η = Σ ((reflect l η) ▹ reflect τ η)

-- reflectRow (l ▹ τ) η = (reflect l η) ▵ (reflect τ η)

----------------------------------------
-- Type evaluation.

eval : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
eval {κ = ★} (` x) η = η x
eval {κ = ★} Unit η  = Unit
eval {κ = ★} (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
eval {κ = ★} (τ₁ `→ τ₂) η = (eval τ₁ η) `→ (eval τ₂ η)
eval {κ = ★} (`∀ κ τ) η = `∀ _ (eval τ (↑e η))
eval {κ = ★} (μ τ) η with eval τ η 
... | left F = μ (ne F)
... | right F = μ (`λ (F S (ne (` Z)))) 
eval {κ = ★} ⌊ τ ⌋ η = ⌊ eval τ η ⌋

-- -- ----------------------------------------
-- -- -- Label evaluation.

eval {κ = L} (` x) η = η x
eval {κ = L} (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
eval {κ = L} (lab l) η = lab l

-- -- ----------------------------------------
-- -- -- function evaluation.

eval {κ = κ₁ `→ κ₂} (` x) η = η x
eval {κ = κ₁ `→ κ₂} (`λ τ) η = right (λ {Δ₃} ρ v → eval τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v))
eval {κ = κ₁ `→ κ₂} (τ₁ · τ₂) η =  (eval τ₁ η) ·V (eval τ₂ η)

----------------------------------------
-- Type constants
eval {κ = κ₁ `→ κ₂} Π η = right (λ {Δ₃} ρ v → π v ρ η) -- π v ρ η
eval {κ = κ₁ `→ κ₂} Σ η = {!   !}
eval {κ = R[ κ₂ ]} (f <$> a) η = (eval f η) <$>V (eval a η) -- right (λ ρ f → rmap f)
eval {κ = _} `▹` η = right (λ ρ₁ l → right (λ ρ₂ v → (renSem {κ = L} ρ₂ l) ▵ v))

-- -- ----------------------------------------
-- -- -- Row evaluation.

eval {κ = R[ κ ]} (` x) η = η x
eval {κ = R[ κ ]} (τ₁ · τ₂) η = eval τ₁ η ·V eval τ₂ η

--------------------------------------------------------------------------------
-- Type normalization

-- NormalType forms.
⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
⇓ τ = reify (eval τ idEnv)

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
A₀ = (`▹` · ℓ) · Unit

_ : ∀ {Δ} → ⇓ (A₀ {Δ}) ≡ row (l ▹ Unit)
_ = refl

----------------------------------------
-- Row-kinded function types.

Id-R : Type Δ R[ ★ `→ ★ ]
Id-R = (`▹` · ℓ) · (`λ (` Z))

_ : ∀ {Δ} → ⇓ (Id-R {Δ}) ≡ row (l ▹ (`λ (ne (` Z))))
_ = refl

apply-R : Type Δ R[ ((★ `→ ★) `→ ★ `→ ★) ]
apply-R = (`▹` · ℓ₁) · apply

_ : ∀ {Δ} → ⇓ (apply-R {Δ}) ≡ row ((l₁ ▹ ⇓ apply))
_ = refl

----------------------------------------
-- Function types with congruences. 

C₁ : Type Δ ★
C₁ = `Π (ℓ `▹ Unit)

_ : ∀ {Δ} → ⇓ (C₁ {Δ}) ≡ Π (l ▹ Unit)
_ = refl

C₂ : Type Δ (★ `→ ★)
C₂ = `Π (ℓ `▹ (`λ (` Z)))

_ : ∀ {Δ} → ⇓ (C₂ {Δ}) ≡ `λ (Π (l ▹ (ne (` Z))))
_ = refl 

C₃ : Type Δ ★
C₃ = `Π (`Π (ℓ₁ `▹ (ℓ₂ `▹ ((apply · Const-U) · Unit))))

_ : ∀ {Δ} → ⇓ (C₃ {Δ}) ≡ Π (l₁ ▹ (Π (l₂ ▹ Unit)))
_ = refl


-- -- -- ----------------------------------------
-- -- -- -- Unreduced Π applications

NR₀ : Type Δ ★
NR₀ = `Π (`Π (ℓ₁ `▹ (ℓ₂ `▹ Unit)))

_ : ⇓ {Δ = Δ} NR₀ ≡ Π (l₁ ▹ (Π (l₂ ▹ Unit)))
_ = refl 

NR₁ : Type Δ (★ `→ ★)
NR₁ = `Π (ℓ₁ `▹ (`Π (ℓ₂ `▹ ID)))

_ : ⇓ {Δ = Δ} NR₁ ≡ `λ (Π (l₁ ▹ (Π (l₂ ▹ (ne (` Z))))))
_ = refl


NR₂ : Type Δ R[ ★ ]
NR₂ = `Π (ℓ₁ `▹ (ℓ₂ `▹ (((apply · Const-U) · Unit))))

_ : ∀ {Δ} → ⇓ (NR₂ {Δ}) ≡ row (l₁ ▹ (Π (l₂ ▹ Unit)))
_ = refl

NR₃ : Type Δ R[ ★ `→ ★ ]
NR₃ = `Π (ℓ₁ `▹ (ℓ₂ `▹ ID))

_ : ⇓ {Δ = Δ} NR₃ ≡ row (l₁ ▹ `λ (Π (l₂ ▹ (ne (` Z)))))
_ = refl

NR₄ : Type Δ R[ R[ ★ ] ]
NR₄ = `Π (ℓ₁ `▹ (ℓ₂ `▹ (ℓ₃ `▹ Unit)))

_ : ⇓ {Δ = Δ} NR₄ ≡ row (l₁ ▹ (row (l₂ ▹ (Π (l₃ ▹ Unit)))))
_ = refl

NR₅ : Type Δ R[ R[ ★ `→ ★ ] ]
NR₅ = `Π (ℓ₁ `▹ (ℓ₂ `▹ (ℓ₃ `▹ ID)))

_ : ⇓ {Δ = Δ} NR₅ ≡ row (l₁ ▹ (row (l₂ ▹ `λ (Π (l₃ ▹ ne (` Z))))))
_ = refl


NR₆ : Type Δ R[ R[ R[ ★ `→ ★ ] ] ]
NR₆ = `Π (ℓ₁ `▹ (ℓ₂ `▹ (ℓ₃ `▹ (ℓ `▹ ID))))

_ : ⇓ {Δ = Δ} NR₆ ≡ row (lab "l1" ▹ row (lab "l2" ▹ row (lab "l3" ▹ `λ (Π (lab "l" ▹ ne (` Z))))))
_ = refl


-- -- ----------------------------------------
-- -- -- Mixed Π and Σ w/ unreduced computation

-- mix₀ : Type Δ ★
-- mix₀ = Π · (Σ · (ℓ₁ ▹ (ℓ₂ ▹ Unit)))

-- _ : ⇓ {Δ = Δ} mix₀ ≡ Π▹ l₁ (Σ▹ l₂ Unit)
-- _ = {!refl!}


-- -- --------------------------------------------------------------------------------
-- -- -- Lifting nonsense

-- lift-λ : Type Δ ★
-- lift-λ = `Π (`λ (` Z) <$> (ℓ `▹ Unit))

-- _ : ⇓ {Δ = Δ} lift-λ ≡ Π (lab "l" ▹ Unit)
-- _ = refl

-- lift-λ₂  : Type Δ ((★ `→ ★) `→ R[ ★ ])
-- lift-λ₂ = `Π (ℓ₁ `▹ (`λ (`λ (` Z) <$> (ℓ₂ `▹ Unit)))) -- `Π (ℓ₁ `▹ (`λ  (↑ · (` Z)) · (ℓ₂ ▹ Unit)))


-- _ : ⇓ {Δ = Δ} lift-λ₂ ≡ `λ (row (lab "l1" ▹ Π (lab "l2" ▹ Unit)))
-- _ = refl

-- lift-var : Type Δ (R[ ★ ] `→ R[ ★ ])
-- lift-var = `λ (`λ (` Z) <$> (` Z))

-- _ : ⇓ {Δ = Δ} lift-var ≡ `λ (ne (`λ (ne (` Z)) <$> ` Z))
-- _ = refl

-- -- -- -- -- -- -- --------------------------------------------------------------------------------
-- -- -- -- -- -- -- -- Claims.
  
-- -- -- -- -- -- -- -- row-canonicity : (r : Type Δ R[ κ ]) → ∃[ x ] ∃[ τ ] ((⇓ r ≡ (x ▹ τ)) or isNE (⇓ r))
-- -- -- -- -- -- -- -- row-canonicity (` x) = {!!}
-- -- -- -- -- -- -- -- row-canonicity (r · r₁) = {!!}
-- -- -- -- -- -- -- -- row-canonicity (r ▹ r₁) = {!!}
-- -- -- -- -- -- -- -- row-canonicity (Π r) with ⇓ r 
-- -- -- -- -- -- -- -- ... | c = ( {!!} , ( {!!} , {!!} ) )
-- -- -- -- -- -- -- -- row-canonicity (Σ r) = {!!}
             
              