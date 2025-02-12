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
reflectNE {κ = R[ κ ]} τ       = left τ
reflectNE {κ = κ `→ κ₁} τ     = left τ

--------------------------------------------------------------------------------
-- reification of semantic types

reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ
reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} (left τ) = ne τ
reify {κ = κ₁ `→ κ₂} (right F) = `λ (reify (F S (reflectNE {κ = κ₁} (` Z))))
reify {κ = R[ κ ]} (left x) = ne x
reify {κ = R[ κ ]} (right (l , τ)) = row (l ▹ (reify τ))

reify∘reflect≡ne : ∀ (τ : NeutralType Δ κ) → reify (reflectNE τ) ≡ ne τ 
reify∘reflect≡ne {κ = ★} τ = refl
reify∘reflect≡ne {κ = L} τ = refl
reify∘reflect≡ne {κ = κ `→ κ₁} τ = refl
reify∘reflect≡ne {κ = R[ κ ]} τ = refl

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
-- Semantic application and applicators Π, Σ, and <?>

_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
π σ : ∀ {Δ} → SemType Δ R[ κ ] → SemType Δ κ

_<?>_ : NeutralType Δ R[ κ₁ `→ κ₂ ] → SemType Δ κ₁ → SemType Δ R[ κ₂ ]
f <?> a = left ((`λ (ne ((` Z) · (ren S (reify a))))) <$> f)

left (Π f) ·V V = π (f <?> V)
left (Σ f) ·V V = σ (f <?> V)
left A ·V V = reflectNE (A · (reify V))
right F ·V V = F id V

--------------------------------------------------------------------------------
-- Semantic lifting

_<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
_<$>V_ {κ₁ = κ₁} {κ₂} F (left x) = left (reify F <$> x) 
_<$>V_ {κ₁ = κ₁} {κ₂} F (right (l , τ)) = right (l , (F ·V τ))

--------------------------------------------------------------------------------
-- Semantic combinator for labeled types

_▹V_ : SemType Δ L → SemType Δ κ → SemType Δ R[ κ ]
_▹V_ {κ = κ} ℓ τ = right (ℓ , τ)


--------------------------------------------------------------------------------
-- (Generic) Semantic combinators for Π/Σ

record Xi : Set where 
  field
    ΞNE : ∀ {Δ'} {κ : Kind} → NeutralType Δ' R[ κ ] → NeutralType Δ' κ
    Ξ★ : ∀ {Δ'} → Row Δ' R[ ★ ] → NormalType Δ' ★
    ΞL : ∀ {Δ'} → Row Δ' R[ L ] → NormalType Δ' L
    ren-NE : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : NeutralType Δ₁ R[ κ ]) → renNE ρ (ΞNE τ) ≡  ΞNE (renNE ρ τ)
    ren-★ : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : Row Δ₁ R[ ★ ]) → ren ρ (Ξ★ τ) ≡  Ξ★ (renRow ρ τ)
    ren-L : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : Row Δ₁ R[ L ]) → ren ρ (ΞL τ) ≡  ΞL (renRow ρ τ)

open Xi
ξ : ∀ {Δ} → Xi → SemType Δ R[ κ ] → SemType Δ κ 
ξ {κ = κ} Ξ (left x) = reflectNE (Ξ .ΞNE x)
ξ {κ = ★} Ξ (right (l , τ)) = Ξ .Ξ★ (l ▹ τ)
ξ {κ = L} Ξ (right (l , τ)) = Ξ .ΞL (l ▹ τ)
ξ {κ = κ₁ `→ κ₂} Ξ (right (l , τ)) = right (λ ρ v → ξ Ξ ((ren ρ l) ▹V ((renSem {κ = κ₁ `→ κ₂} ρ τ) ·V v)))
ξ {κ = R[ κ ]} Ξ (right (l , τ)) = right (l , ξ Ξ τ)

Π-rec Σ-rec : Xi 
Π-rec = record
  { ΞNE = Π ; Ξ★ = Π ; ΞL = ΠL ; ren-NE = λ ρ τ → refl ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }
Σ-rec = 
  record
  { ΞNE = Σ ; Ξ★ = Σ ; ΞL = ΣL ; ren-NE = λ ρ τ → refl ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }


π = ξ Π-rec
σ = ξ Σ-rec

ξ-Kripke : Xi → KripkeFunction Δ R[ κ ] κ
ξ-Kripke Ξ ρ v = ξ Ξ v

π-Kripke σ-Kripke : KripkeFunction Δ R[ κ ] κ
π-Kripke = ξ-Kripke Π-rec
σ-Kripke = ξ-Kripke Σ-rec

--------------------------------------------------------------------------------
-- Semantic combinator for Lifting



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
 
