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
reify {κ = R[ κ₁ `→ κ₂ ]} (right (l , left F)) = row (l ▹ (ne F))
reify {κ = R[ κ₁ `→ κ₂ ]} (right (l , right F)) = row (l ▹ (reify (right F)))
reify {κ = R[ R[ κ₁ ] ]} (left x) =  ne x
reify {κ = R[ R[ κ₁ ] ]} (right (l , τ)) = row (l ▹ (reify τ))

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
right F ·V V = F id V

--------------------------------------------------------------------------------
-- Semantic combinator for labeled types

_▹V_ : SemType Δ L → SemType Δ κ → SemType Δ R[ κ ]
_▹V_ {κ = ★} ℓ τ = row (ℓ ▹ τ) -- ℓ ▹ τ
_▹V_ {κ = L} ℓ τ = row (ℓ ▹ τ) -- ℓ ▹ τ
_▹V_ {κ = κ₁ `→ κ₂} ℓ (left τ) = right (ℓ , (left τ))
_▹V_ {κ = κ₁ `→ κ₂} ℓ (right F) = right (ℓ , (right F))
_▹V_ {κ = R[ κ ]} ℓ τ = right (ℓ , τ)


--------------------------------------------------------------------------------
-- Semantic combinators for Π

πNE : NeutralType Δ R[ κ ] → SemType Δ κ 
πNE {κ = ★} τ = ne (Π τ)
πNE {κ = L} τ = ne (Π τ)
πNE {κ = κ₁ `→ κ₂} τ = left (Π τ)
πNE {κ = R[ ★ ]} τ = ne (Π τ)
πNE {κ = R[ L ]} τ = ne (Π τ)
πNE {κ = R[ κ `→ κ₁ ]} τ = left (Π τ)
πNE {κ = R[ R[ κ ] ]} τ = left (Π τ)

π : ∀ {Δ} → SemType Δ R[ κ ] → SemType Δ κ
π {κ = ★}  (ne x)                 = πNE x
π {κ = ★}  (row r)                = Π r
π {κ = L}   (ne x)                 = πNE x
π {κ = L}   (row r)                = ΠL r
π {κ = κ₁ `→ κ₂}   (left x)               = πNE x
π {κ = κ₁ `→ κ₂}   (right (l , left f))   = right (λ ρ' v → π (ren ρ' l ▹V reflectNE ((renNE ρ' f) · (reify v))))
π {κ = κ₁ `→ κ₂}   (right (l , right F))  = right (λ ρ' v → π (ren ρ' l ▹V F ρ' v))
π {κ = R[ ★ ]}  (left x)               = πNE x
π {κ = R[ ★ ]}  (right (l , τ))        = row (l ▹ (reify (π {κ = ★} τ )))
π {κ = R[ L ]}   (left x)               = πNE x
π {κ = R[ L ]}   (right (l , τ))        = row (l ▹ (reify (π {κ = L} τ )))
π {κ = R[ κ₁ `→ κ₂ ]}   (left x)               = πNE x
π {κ = R[ κ₁ `→ κ₂ ]}   (right (l , left τ))   = _▹V_ {κ                = κ₁ `→ κ₂} l (πNE {κ = κ₁ `→ κ₂} τ)
π {κ = R[ κ₁ `→ κ₂ ]}   (right (l , τ))        = _▹V_ {κ                = κ₁ `→ κ₂} l (π {κ   = κ₁ `→ κ₂} τ)
π {κ = R[ R[ κ ] ]}   (left x)               = πNE x
π {κ = R[ R[ κ ] ]}  (right (l , left τ))   = _▹V_ {κ                = R[ κ ]} l (πNE {κ   = R[ κ ]} τ)
π {κ = R[ R[ κ ] ]} (right (l , τ))  =  _▹V_ {κ = R[ κ ]} l (π {κ = R[ κ ]} τ)

π-Kripke : KripkeFunction Δ R[ κ ] κ
π-Kripke ρ v = π v

--------------------------------------------------------------------------------
-- Semantic combinator for Σ

-- I'll prove Π is stable before duplicating the work for Σ.
σNE : NeutralType Δ R[ κ ] → SemType Δ κ 
σNE {κ = ★} τ = ne (Σ τ)
σNE {κ = L} τ = ne (Σ τ)
σNE {κ = κ₁ `→ κ₂} τ = left (Σ τ)
σNE {κ = R[ ★ ]} τ = ne (Σ τ)
σNE {κ = R[ L ]} τ = ne (Σ τ)
σNE {κ = R[ κ `→ κ₁ ]} τ = left (Σ τ)
σNE {κ = R[ R[ κ ] ]} τ = left (Σ τ)

σ : ∀ {Δ} → SemType Δ R[ κ ] → SemType Δ κ
σ {κ = ★}  (ne x)  = ne (Σ x)
σ {κ = ★}  (row r)  = Σ r
σ {κ = L}  (ne x)  = ne (Σ x)
σ {κ = L}  (row r)  = ΣL r
σ {κ = κ₁ `→ κ₂}  (left x)  = left (Σ x)
σ {κ = κ₁ `→ κ₂}  (right (l , left f))  = right (λ ρ' v → σ (ren ρ' l ▹V reflectNE ((renNE ρ' f) · (reify v))))
σ {κ = κ₁ `→ κ₂}  (right (l , right F))  = right (λ ρ' v → σ (ren ρ' l ▹V F ρ' v))
σ {κ = R[ ★ ]}  (left x)  = σNE x
σ {κ = R[ ★ ]}  (right (l , τ))  = row (l ▹ (reify (σ {κ = ★} τ )))
σ {κ = R[ L ]}  (left x)  = σNE x
σ {κ = R[ L ]}  (right (l , τ))  = row (l ▹ (reify (σ {κ = L} τ )))
σ {κ = R[ κ₁ `→ κ₂ ]}  (left x)  = σNE x
σ {κ = R[ κ₁ `→ κ₂ ]}  (right (l , left τ))  = _▹V_ {κ = κ₁ `→ κ₂} l (σNE {κ = κ₁ `→ κ₂} τ)
σ {κ = R[ κ₁ `→ κ₂ ]}  (right (l , τ))  = _▹V_ {κ = κ₁ `→ κ₂} l (σ {κ = κ₁ `→ κ₂} τ)
σ {κ = R[ R[ κ ] ]}  (left x)  = σNE x
σ {κ = R[ R[ κ ] ]}  (right (l , left τ))  = _▹V_ {κ = R[ κ ]} l (σNE {κ = R[ κ ]} τ)
σ {κ = R[ R[ κ ] ]}  (right (l , τ))  =  _▹V_ {κ = R[ κ ]} l (σ {κ = R[ κ ]} τ)


--------------------------------------------------------------------------------
-- Semantic combinator for Lifting

_<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
_<$>V_ {κ₁ = κ₁} {κ₂} (left F) τ with reify τ 
... | ne τ         = reflectNE ((ne F) <$> τ)
... | row (l ▹ τ) = _▹V_ {κ = κ₂} l (reflectNE (F · τ)) 
_<$>V_ {κ₁ = κ₁} {κ₂} (right F) τ with reify τ 
... | ne x = reflectNE (_<$>_ {κ₁ = κ₁} (reify (right F)) x)
_<$>V_ {κ₁ = ★} {κ₂} (right F) τ               | row (l ▹ τ') = l ▹V (F id τ')
_<$>V_ {κ₁ = L} {κ₂} (right F) τ                | row (l ▹ τ') = l ▹V (F id τ')
_<$>V_ {κ₁ = κ₁ `→ κ₂} {κ₃} (right F) (left x)  | row _ = reflectNE (_<$>_ {κ₁ = κ₁ `→ κ₂} (reify (right F))  x)
_<$>V_ {κ₁ = κ₁ `→ κ₂} {κ₃} (right F) (right (l , left G)) | row _ = l ▹V (F id (left G))
_<$>V_ {κ₁ = κ₁ `→ κ₂} {κ₃} (right F) (right (l , right G)) | row _ = l ▹V (F id (right G))
_<$>V_ {κ₁ = R[ κ₁ ]} {κ₂} (right F) (left x) | row _ = reflectNE (_<$>_ {κ₁ = R[ κ₁ ]} (reify (right F))  x)
_<$>V_ {κ₁ = R[ κ₁ ]} {κ₂} (right F) (right (l , τ)) | row _ = l ▹V (F id τ)

--------------------------------------------------------------------------------
-- Type evaluation.

eval : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
evalPred : Pred Δ₁ R[ κ ] → Env Δ₁ Δ₂ → NormalPred Δ₂ R[ κ ] 

evalPred (ρ₁ · ρ₂ ~ ρ₃) η = reify (eval ρ₁ η) · reify (eval ρ₂ η) ~ reify (eval ρ₃ η)
evalPred (ρ₁ ≲ ρ₂) η = reify (eval ρ₁ η) ≲ reify (eval ρ₂ η)

eval {κ = κ} (` x) η = η x
eval {κ = κ} (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
eval {κ = κ} (τ₁ `→ τ₂) η = (eval τ₁ η) `→ (eval τ₂ η)

eval {κ = ★} Unit η  = Unit
eval {κ = ★} (π ⇒ τ) η = evalPred π η ⇒ eval τ η
eval {κ = ★} (`∀ κ τ) η = `∀ _ (eval τ (↑e η))
eval {κ = ★} (μ τ) η = μ (reify (eval τ η))
eval {κ = ★} ⌊ τ ⌋ η = ⌊ eval τ η ⌋


----------------------------------------
-- Label evaluation.

eval {κ = L} (lab l) η = lab l

----------------------------------------
-- function evaluation.

eval {κ = κ₁ `→ κ₂} (`λ τ) η = right (λ {Δ₃} ρ v → eval τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v))

----------------------------------------
-- Type constants
eval {κ = κ₁ `→ κ₂} Π η = right (λ {Δ₃} ρ v → π v)
eval {κ = κ₁ `→ κ₂} Σ η = right (λ {Δ₃} ρ v → σ v) 
eval {κ = R[ κ₂ ]} (f <$> a) η = (eval f η) <$>V (eval a η) -- right (λ ρ f → rmap f)
eval {κ = _} (l ▹ τ) η = (eval l η) ▹V (eval τ η) -- right (λ ρ₁ l → right (λ ρ₂ v → (renSem {κ = L} ρ₂ l) ▹V v))

--------------------------------------------------------------------------------
-- Type normalization

-- NormalType forms.
⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
⇓ τ = reify (eval τ idEnv)

⇓NE : ∀ {Δ} → NeutralType Δ κ → NormalType Δ κ
⇓NE τ = reify (eval (⇑NE τ) idEnv)


--------------------------------------------------------------------------------
-- Evaluation of 
--   - neutral types to semantic types
--   - normal types to semantic types
--   - rows to semantic types 
--

evalNE : ∀ {Δ₁ Δ₂} → NeutralType Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
reflect : ∀ {Δ₁ Δ₂} → NormalType Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
reflectRow : ∀ {Δ₁ Δ₂} → Row Δ₁ R[ κ ] → Env Δ₁ Δ₂ → SemType Δ₂ R[ κ ]

evalNE τ η = eval (⇑NE τ) η
reflect τ η = eval (⇑ τ) η
reflectRow (l ▹ τ) η = eval (⇑ (row (l ▹ τ))) η
