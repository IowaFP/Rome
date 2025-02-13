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
reflect {κ = R[ κ ]} τ       = left τ
reflect {κ = κ₁ `→ κ₂} τ     = λ ρ v → reflect (renNE ρ τ · reify v)

-- reflectN : ∀ {κ} → NormalType Δ κ → SemType Δ κ
-- reflectN {κ = ★} τ = τ
-- reflectN {κ = L} τ = τ
-- reflectN {κ = κ `→ κ₁} τ = λ ρ v → reflect {! ren ρ τ   !}
-- reflectN {κ = R[ κ ]} τ = {!   !}
reifyKripke : KripkeFunction Δ κ₁ κ₂ → NormalType Δ (κ₁ `→ κ₂)
reifyKripke {κ₁ = κ₁} F = `λ (reify (F S (reflect {κ = κ₁} (` Z))))

reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} F = reifyKripke F
reify {κ = R[ ★ ]} (left x) = ne x
reify {κ = R[ L ]} (left x) = ne x
reify {κ = R[ κ₁ `→ κ₂ ]} (left x) = ne x
reify {κ = R[ R[ κ ] ]} (left x) = {!   !} -- ne x
reify {κ = R[ κ ]} (right (l , τ)) = l ▹ (reify τ)

-- --------------------------------------------------------------------------------
-- -- Semantic environments

-- Env : KEnv → KEnv → Set
-- Env Δ₁ Δ₂ = ∀ {κ} → KVar Δ₁ κ → SemType Δ₂ κ

-- extende : (η : Env Δ₁ Δ₂) → (V : SemType Δ₂ κ) → Env (Δ₁ ,, κ) Δ₂
-- extende η V Z     = V
-- extende η V (S x) = η x

-- ↑e : Env Δ₁ Δ₂ → Env (Δ₁ ,, κ) (Δ₂ ,, κ)
-- -- extende (weakenSem {Δ = Δ₂} {κ₁ = {!κ'!}} {κ₂ = {!!}} ∘ η {κ = {!κ!}}) (reflect {κ = κ} (` Z))
-- ↑e {Δ₁} {Δ₂} {κ} η  = extende η' V -- extende η' V
--   where
--     η' : Env Δ₁ (Δ₂ ,, κ)
--     η' {κ'} v = (weakenSem {Δ = Δ₂} {κ₁ = κ'} {κ₂ = κ}) (η v)

--     V  : SemType (Δ₂ ,, κ) κ
--     V = reflect {κ = κ} (` Z)

-- idEnv : Env Δ Δ
-- idEnv = reflect ∘ `


-- --------------------------------------------------------------------------------
-- -- Semantic application

-- _·V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
-- F ·V V = F id V

-- --------------------------------------------------------------------------------
-- -- Semantic flap

-- _<?>_ : SemType Δ R[ κ₁ `→ κ₂ ] → SemType Δ κ₁ → SemType Δ R[ κ₂ ]
-- (left f) <?> a = left ((`λ (ne ((` Z) · (ren S (reify a))))) <$> f)
-- (right (l , F)) <?> a = right (l , F ·V a)

-- --------------------------------------------------------------------------------
-- -- Semantic lifting

-- _<$>V_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
-- _<$>V_ {κ₁ = κ₁} {κ₂} F (left x) = left (reifyKripke F <$> x) -- ne (reifyKripke F <$> x) -- (reify F <$> x) 
-- _<$>V_ {κ₁ = κ₁} {κ₂} F (right (l , τ)) = right (l , F ·V τ) -- l ▹ {!   !} -- (l , (F ·V τ))

-- --------------------------------------------------------------------------------
-- -- Semantic combinator for labeled types

-- _▹V_ : SemType Δ L → SemType Δ κ → SemType Δ R[ κ ]
-- _▹V_ {κ = κ} ℓ τ = right (ℓ , τ)


-- --------------------------------------------------------------------------------
-- -- (Generic) Semantic combinators for Π/Σ

-- record Xi : Set where 
--   field
--     -- ΞNE : ∀ {Δ'} {κ : Kind} → NeutralType Δ' R[ κ ] → NeutralType Δ' κ
--     Ξ★ : ∀ {Δ'} → NormalType  Δ' R[ ★ ] → NormalType Δ' ★
--     ΞL : ∀ {Δ'} → NormalType Δ' R[ L ] → NormalType Δ' L
--     -- ren-NE : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : NeutralType Δ₁ R[ κ ]) → renNE ρ (ΞNE τ) ≡  ΞNE (renNE ρ τ)
--     ren-★ : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : NormalType Δ₁ R[ ★ ]) → ren ρ (Ξ★ τ) ≡  Ξ★ (ren ρ τ)
--     ren-L : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : NormalType Δ₁ R[ L ]) → ren ρ (ΞL τ) ≡  ΞL (ren ρ τ)

-- open Xi
-- ξ : ∀ {Δ} → Xi → SemType Δ R[ κ ] → SemType Δ κ 
-- ξ {κ = ★} Ξ (left x) = Ξ .Ξ★ (ne x)
-- ξ {κ = L} Ξ (left x) = Ξ .ΞL (ne x)
-- ξ {κ = κ₁ `→ κ₂} Ξ (left x) = λ ρ v → ξ Ξ (left (renNE ρ x) <?> v)
-- ξ {κ = R[ κ ]} Ξ (left x) = (λ ρ v → ξ Ξ v) <$>V (left x) 
-- ξ {κ = ★} Ξ (right (l , τ)) = Ξ .Ξ★ (l ▹ τ)
-- ξ {κ = L} Ξ (right (l , τ)) = Ξ .ΞL (l ▹ τ)
-- ξ {κ = κ₁ `→ κ₂} Ξ (right (l , τ)) = λ ρ v → ξ Ξ ((ren ρ l) ▹V ((renSem {κ = κ₁ `→ κ₂} ρ τ) ·V v))
-- ξ {κ = R[ κ ]} Ξ (right (l , τ)) = right (l , ξ Ξ τ)

-- Π-rec Σ-rec : Xi 
-- Π-rec = record
--   {  Ξ★ = Π ; ΞL = ΠL ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }
-- Σ-rec = 
--   record
--   { Ξ★ = Σ ; ΞL = ΣL ; ren-★ = λ ρ τ → refl ; ren-L = λ ρ τ → refl }

-- π σ : ∀ {Δ} → SemType Δ R[ κ ] → SemType Δ κ
-- π = ξ Π-rec
-- σ = ξ Σ-rec

-- ξ-Kripke : Xi → KripkeFunction Δ R[ κ ] κ
-- ξ-Kripke Ξ ρ v = ξ Ξ v

-- π-Kripke σ-Kripke : KripkeFunction Δ R[ κ ] κ
-- π-Kripke = ξ-Kripke Π-rec
-- σ-Kripke = ξ-Kripke Σ-rec

-- --------------------------------------------------------------------------------
-- -- Type evaluation.

-- eval : Type Δ₁ κ → Env Δ₁ Δ₂ → SemType Δ₂ κ
-- evalPred : Pred Δ₁ R[ κ ] → Env Δ₁ Δ₂ → NormalPred Δ₂ R[ κ ] 

-- evalPred (ρ₁ · ρ₂ ~ ρ₃) η = reify (eval ρ₁ η) · reify (eval ρ₂ η) ~ reify (eval ρ₃ η)
-- evalPred (ρ₁ ≲ ρ₂) η = reify (eval ρ₁ η) ≲ reify (eval ρ₂ η)

-- eval {κ = κ} (` x) η = η x
-- eval {κ = κ} (τ₁ · τ₂) η = (eval τ₁ η) ·V (eval τ₂ η)
-- eval {κ = κ} (τ₁ `→ τ₂) η = (eval τ₁ η) `→ (eval τ₂ η)

-- eval {κ = ★} Unit η  = Unit
-- eval {κ = ★} (π ⇒ τ) η = evalPred π η ⇒ eval τ η
-- eval {κ = ★} (`∀ κ τ) η = `∀ _ (eval τ (↑e η))
-- eval {κ = ★} (μ τ) η = μ (reify (eval τ η))
-- eval {κ = ★} ⌊ τ ⌋ η = ⌊ eval τ η ⌋

-- ----------------------------------------
-- -- Label evaluation.

-- eval {κ = L} (lab l) η = lab l

-- ----------------------------------------
-- -- function evaluation.

-- eval {κ = κ₁ `→ κ₂} (`λ τ) η = λ ρ v → eval τ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v)

-- -- ----------------------------------------
-- -- -- Type constants
-- eval {κ = κ₁ `→ κ₂} Π η = λ ρ v → π v
-- eval {κ = κ₁ `→ κ₂} Σ η = λ ρ v → σ v
-- eval {κ = R[ κ₂ ]} (f <$> a) η = (eval f η) <$>V (eval a η)
-- eval {κ = _} (l ▹ τ) η = (eval l η) ▹V (eval τ η) 

-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Type normalization

-- -- NormalType forms.
-- ⇓ : ∀ {Δ} → Type Δ κ → NormalType Δ κ
-- ⇓ τ = reify (eval τ idEnv)

-- ⇓NE : ∀ {Δ} → NeutralType Δ κ → NormalType Δ κ
-- ⇓NE τ = reify (eval (⇑NE τ) idEnv)
 
