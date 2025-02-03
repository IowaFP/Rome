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
-- (Generic) Semantic combinators for Π/Σ

record Chi : Set where 
  field
    ΞNE : ∀ {Δ'} {κ : Kind} → NeutralType Δ' R[ κ ] → NeutralType Δ' κ
    Ξ★ : ∀ {Δ'} → Row Δ' R[ ★ ] → NormalType Δ' ★
    ΞL : ∀ {Δ'} → Row Δ' R[ L ] → NormalType Δ' L
    ren-NE : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : NeutralType Δ₁ R[ κ ]) → renNE ρ (ΞNE τ) ≡  ΞNE (renNE ρ τ)
    ren-★ : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : Row Δ₁ R[ ★ ]) → ren ρ (Ξ★ τ) ≡  Ξ★ (renRow ρ τ)
    ren-L : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : Row Δ₁ R[ L ]) → ren ρ (ΞL τ) ≡  ΞL (renRow ρ τ)

ξ : ∀ {Δ} → Chi → SemType Δ R[ κ ] → SemType Δ κ 
ξ {κ = ★} record { ΞNE = ΞNE } (ne x) = reflectNE (ΞNE x)
ξ {κ = ★} record { Ξ★ = Ξ★ } (row r) = Ξ★ r
ξ {κ = L} record { ΞNE   = ΞNE } (ne x)   = reflectNE (ΞNE x) 
ξ {κ = L} record { ΞL  = ΞL } (row r) = ΞL r 
ξ {κ = κ₁ `→ κ₂} record { ΞNE = ΞNE } (left x) = reflectNE (ΞNE x) 
ξ {κ = κ₁ `→ κ₂} Ξ  (right (l , left f))   = 
  right (λ ρ' v → ξ Ξ (ren ρ' l ▹V reflectNE ((renNE ρ' f) · (reify v)))) 
ξ {κ = κ₁ `→ κ₂} Ξ  (right (l , right F))  = 
  right (λ ρ' v → ξ Ξ (ren ρ' l ▹V F ρ' v)) 
ξ {κ = R[ ★ ]} record { ΞNE = ΞNE }  (left x)  = reflectNE (ΞNE x) 
ξ {κ = R[ ★ ]} Ξ  (right (l , τ))          = row (l ▹ (reify (ξ {κ = ★} Ξ τ )))
ξ {κ = R[ L ]}  record { ΞNE = ΞNE } (left x)  =  reflectNE (ΞNE x)
ξ {κ = R[ L ]}  Ξ  (right (l , τ))         = row (l ▹ (reify (ξ {κ = L} Ξ τ )))
ξ {κ = R[ κ₁ `→ κ₂ ]} record { ΞNE = ΞNE }  (left x) =  reflectNE (ΞNE x)
ξ {κ = R[ κ₁ `→ κ₂ ]} record { ΞNE = ΞNE } (right (l , left τ)) =  _▹V_ {κ = κ₁ `→ κ₂} l (reflectNE {κ = κ₁ `→ κ₂} (ΞNE τ))
ξ {κ = R[ κ₁ `→ κ₂ ]} Ξ  (right (l , τ)) = _▹V_ {κ = κ₁ `→ κ₂} l (ξ {κ = κ₁ `→ κ₂} Ξ τ)
ξ {κ = R[ R[ κ ] ]} record { ΞNE = ΞNE }  (left x) =  reflectNE (ΞNE x)
ξ {κ = R[ R[ κ ] ]} record { ΞNE = ΞNE }  (right (l , left τ)) =  
    _▹V_ {κ = R[ κ ]} l (reflectNE {κ = R[ κ ]} (ΞNE τ))
ξ {κ = R[ R[ κ ] ]} Ξ  (right (l , τ)) = 
    _▹V_ {κ = R[ κ ]} l (ξ {κ = R[ κ ]} Ξ τ)

open Chi 

Π-rec Σ-rec : Chi 
Π-rec = record
  { ΞNE = Π ; Ξ★ = Π ; ΞL = ΠL ; ren-NE = λ ρ τ → refl ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }
Σ-rec = 
  record
  { ΞNE = Σ ; Ξ★ = Σ ; ΞL = ΣL ; ren-NE = λ ρ τ → refl ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }

π σ : ∀ {Δ} → SemType Δ R[ κ ] → SemType Δ κ
π = ξ Π-rec
σ = ξ Σ-rec

π-Kripke σ-Kripke : KripkeFunction Δ R[ κ ] κ
π-Kripke ρ v = π v
σ-Kripke ρ v = σ v

--------------------------------------------------------------------------------
-- Semantic combinator for Lifting

_<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
_<$>V_ {κ₁ = κ₁} {κ₂} (left F) τ with reify τ 
... | ne τ         = reflectNE ((ne F) <$> τ)
... | row (l ▹ τ) = _▹V_ {κ = κ₂} l (reflectNE (F · τ)) 
_<$>V_ {κ₁ = ★} {κ₂} (right F) (ne x) = reflectNE ((reify (right F)) <$> x)
_<$>V_ {κ₁ = ★} {κ₂} (right F) (row (l ▹ τ)) = l ▹V (F id τ)
_<$>V_ {κ₁ = L} {κ₂} (right F) (ne x) = reflectNE ((reify (right F)) <$> x)
_<$>V_ {κ₁ = L} {κ₂} (right F) (row (l ▹ τ)) = l ▹V (F id τ)
_<$>V_ {κ₁ = κ₁ `→ κ₂} {κ₃} (right F) (left x)  = reflectNE (_<$>_ {κ₁ = κ₁ `→ κ₂} (reify (right F))  x)
_<$>V_ {κ₁ = κ₁ `→ κ₂} {κ₃} (right F) (right (l , G)) = l ▹V (F id G)
_<$>V_ {κ₁ = R[ κ₁ ]} {κ₂} (right F) (left x)  = reflectNE (_<$>_ {κ₁ = R[ κ₁ ]} (reify (right F))  x)
_<$>V_ {κ₁ = R[ κ₁ ]} {κ₂} (right F) (right (l , τ)) = l ▹V (F id τ)

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
 