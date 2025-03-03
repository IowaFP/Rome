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
-- reflection of neutral types & reification of semantic types
reflect : ∀ {κ} → NeutralType Δ κ → SemType Δ κ
reify : ∀ {κ} → SemType Δ κ → NormalType Δ κ

reflect {κ = ★} τ            = ne τ
reflect {κ = L} τ            = ne τ
reflect {κ = R[ κ ]} τ       = just (left τ)
reflect {κ = κ₁ `→ κ₂} τ     = λ ρ v → reflect (renNE ρ τ · reify v)


reifyKripke : KripkeFunction Δ κ₁ κ₂ → NormalType Δ (κ₁ `→ κ₂)
reifyKripke {κ₁ = κ₁} F = `λ (reify (F S (reflect {κ = κ₁} (` Z))))

reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} F = reifyKripke F
reify {κ = R[ κ ]} (just (left x)) = ne x
reify {κ = R[ κ ]} (just (right (l , τ))) = l ▹ (reify τ)
reify {κ = R[ κ ]} nothing = ε

--------------------------------------------------------------------------------
-- Semantic environments

Env : KEnv → KEnv → Set
Env Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → SemType Δ₂ κ

extende : (η : Env Δ₁ Δ₂) → (V : SemType Δ₂ κ) → Env (Δ₁ ,, κ) Δ₂
extende η V Z     = V
extende η V (S x) = η x

↑e : Env Δ₁ Δ₂ → Env (Δ₁ ,, κ) (Δ₂ ,, κ)
↑e {Δ₁} {Δ₂} {κ} η  = extende η' V -- extende η' V
  where
    η' : Env Δ₁ (Δ₂ ,, κ)
    η' {κ'} v = (weakenSem {Δ = Δ₂} {κ₁ = κ'} {κ₂ = κ}) (η v)

    V  : SemType (Δ₂ ,, κ) κ
    V = reflect {κ = κ} (` Z)

idEnv : Env Δ Δ
idEnv = reflect ∘ `

--------------------------------------------------------------------------------
-- Semantic helpers for row-kind construction

_▹V_ : SemType Δ L → SemType Δ κ → SemType Δ R[ κ ]
_▹V_ {κ = κ} ℓ τ = just (right (ℓ , τ))

ne-R : NeutralType Δ R[ κ ] → SemType Δ R[ κ ]
ne-R = just ∘ left

εV : SemType Δ R[ κ ] 
εV = nothing

--------------------------------------------------------------------------------
-- Semantic application

_·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
F ·V V = F id V

-- --------------------------------------------------------------------------------
-- -- Semantic lifting

_<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
_<$>V_ {κ₁ = κ₁} {κ₂} F (just (left x)) = just (left (reifyKripke F <$> x))
_<$>V_ {κ₁ = κ₁} {κ₂} F (just (right (l , τ))) = just (right (l , F ·V τ))
_<$>V_ {κ₁ = κ₁} {κ₂} F nothing = nothing

--------------------------------------------------------------------------------
-- Semantic flap

apply : SemType Δ κ₁ → SemType Δ ((κ₁ `→ κ₂) `→ κ₂)
apply a = λ ρ F → F ·V (renSem ρ a)

infixr 0 _<?>V_
_<?>V_ : SemType Δ R[ κ₁ `→ κ₂ ] → SemType Δ κ₁ → SemType Δ R[ κ₂ ]
f <?>V a = apply a <$>V f


-- --------------------------------------------------------------------------------
-- -- (Generic) Semantic combinators for Π/Σ

record Xi : Set where 
  field
    Ξ★ : ∀ {Δ'} → NormalType  Δ' R[ ★ ] → NormalType Δ' ★
    ΞL : ∀ {Δ'} → NormalType Δ' R[ L ] → NormalType Δ' L
    ren-★ : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : NormalType Δ₁ R[ ★ ]) → ren ρ (Ξ★ τ) ≡  Ξ★ (ren ρ τ)
    ren-L : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : NormalType Δ₁ R[ L ]) → ren ρ (ΞL τ) ≡  ΞL (ren ρ τ)

open Xi
ξ : ∀ {Δ} → Xi → SemType Δ R[ κ ] → SemType Δ κ 
ξ {κ = ★} Ξ x = Ξ .Ξ★ (reify x)
ξ {κ = L} Ξ x = Ξ .ΞL (reify x)
ξ {κ = κ₁ `→ κ₂} Ξ F = λ ρ v → ξ Ξ (renSem ρ F <?>V v)
ξ {κ = R[ κ ]} Ξ x = (λ ρ v → ξ Ξ v) <$>V x

Π-rec Σ-rec : Xi 
Π-rec = record
  {  Ξ★ = Π ; ΞL = ΠL ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }
Σ-rec = 
  record
  { Ξ★ = Σ ; ΞL = ΣL ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }

π σ : ∀ {Δ} → SemType Δ R[ κ ] → SemType Δ κ
π = ξ Π-rec
σ = ξ Σ-rec

ξ-Kripke : Xi → KripkeFunction Δ R[ κ ] κ
ξ-Kripke Ξ ρ v = ξ Ξ v

π-Kripke σ-Kripke : KripkeFunction Δ R[ κ ] κ
π-Kripke = ξ-Kripke Π-rec
σ-Kripke = ξ-Kripke Σ-rec

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

eval {κ = κ₁ `→ κ₂} (`λ τ) η = λ ρ v → eval τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v)

-- ----------------------------------------
-- -- Type constants
eval {κ = κ₁ `→ κ₂} Π η = λ ρ v → π v
eval {κ = κ₁ `→ κ₂} Σ η = λ ρ v → σ v
eval {κ = R[ κ₂ ]} (f <$> a) η = (eval f η) <$>V (eval a η)
eval {κ = _} (l ▹ τ) η = (eval l η) ▹V (eval τ η) 
eval ε η = nothing

-- -- --------------------------------------------------------------------------------
-- -- -- Type normalization

-- NormalType forms.
⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
⇓ τ = reify (eval τ idEnv)

⇓NE : ∀ {Δ} → NeutralType Δ κ → NormalType Δ κ
⇓NE τ = reify (eval (⇑NE τ) idEnv)
 
