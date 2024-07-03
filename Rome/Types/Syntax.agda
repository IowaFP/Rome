{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Types.Syntax where

open import Preludes.Level
open import Preludes.Relation
open import Preludes.Data

open import Rome.GVars.Kinds
open import Rome.Kinds.Syntax


--------------------------------------------------------------------------------
-- infix OOP.

infixr 9 _`→_
infixr 9 _⇒_
infixr 10 _▹_
infixr 10 _R▹_
infixr 10 _≲_
infix 10 _·_~_
infixl 11 _·[_]

infix 12 ↑_ _↑

--------------------------------------------------------------------------------
-- Labels are Strings.

Label : Set
Label = String


--------------------------------------------------------------------------------
-- Kinding Environments, types, and predicates... And multirows.
data Type : KEnv ℓ → Kind ι →  Set
data Pred (Δ : KEnv ℓ) : (κ : Kind ι) → Set

data Pred Δ where
  _≲_ : ∀ {κ : Kind ι} →
          (ρ₁ : Type Δ R[ κ ]) →
          (ρ₂ : Type Δ R[ κ ]) →
          Pred Δ κ

  _·_~_ : ∀ {κ : Kind ι} →
            (ρ₁ : Type Δ R[ κ ]) →
            (ρ₂ : Type Δ R[ κ ]) →
            (ρ₃ : Type Δ R[ κ ]) →
            Pred Δ κ

--------------------------------------------------------------------------------
-- Type vars.
data TVar : KEnv ℓ → Kind ι → Set where
  Z : TVar (Δ ، κ) κ
  S : TVar Δ κ₁ → TVar (Δ ، κ₂) κ₁

S² : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂) κ
S³ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃) κ
S⁴ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄) κ
S⁵ : TVar Δ κ → TVar (Δ ، κ₁ ، κ₂ ، κ₃ ، κ₄ ، κ₅) κ

S² x = S (S x)
S³ x = S (S² x)
S⁴ x = S (S³ x)
S⁵ x = S (S⁴ x)

--------------------------------------------------------------------------------
-- Multirows.

data MultiRow : KEnv ℓ → Kind ι → Set 
_∉_ : Label → MultiRow Δ κ → Set
_∉?_ : ∀ (l : Label) (m : MultiRow Δ κ) → Dec (l ∉ m)

data MultiRow where
  _▹_ : (l : Label) → (τ : Type Δ κ) → MultiRow Δ κ
  _▹_，_ : (l : Label) → (τ : Type Δ κ) → (xs : MultiRow Δ κ) → 
          {_ : True (l ∉? xs)}  → MultiRow Δ κ

l₁ ∉ (l₂ ▹ τ)  = l₁ ≡ l₂
l₁ ∉ (l₂ ▹ _ ， mr) with l₁ ≟ l₂
... | yes p  = ⊥₀
... | no  p  = l₁ ∉ mr 


l₁ ∉? (l₂ ▹ τ)  = l₁ ≟ l₂
l₁ ∉? (l₂ ▹ τ ， m) with l₁ ≟ l₂
... | yes refl = no (λ ())
... | no  p = l₁ ∉? m

--------------------------------------------------------------------------------
-- Types.

data Type where

  ------------------------------------------------------------
  -- System Fω.

  tvar :

         TVar Δ κ →
         -----------
         Type Δ κ

  _`→_ :
          Type Δ (★ ℓ₁) → Type Δ (★ ℓ₂) →
          -----------------------------------
          Type Δ (★ (ℓ₁ ⊔ ℓ₂))

  `∀ :
          (κ : Kind ℓκ) → Type (Δ ، κ) (★ ℓ) →
          -------------------------------------
          Type Δ (★ (ℓ ⊔ (lsuc ℓκ)))

  `λ :
          (κ₁ : Kind ℓκ₁) → Type (Δ ، κ₁) κ₂ →
          -----------------------------------------
          Type Δ (κ₁ `→ κ₂)

  _·[_] :
          Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
          -----------------------------
          Type Δ κ₂

  ------------------------------------------------------------
  -- Qualified types.

  _⇒_ : ∀ {κ : Kind ℓκ} →
         (π : Pred Δ κ) → Type Δ (★ ℓ) →
         --------------------------------
         Type Δ (★ (lsuc ℓκ ⊔ ℓ))

  ------------------------------------------------------------
  -- System Rω.

  ε : Type Δ R[ κ ]

  Row : MultiRow Δ κ → 
       -------------
       Type Δ R[ κ ]

  -- Labels.
  lab :
        Label →
        ----------
        Type Δ (L ℓ)

  -- singleton formation.
  _▹_ :
        Type Δ (L ℓ) → Type Δ κ →
        -------------------
        Type Δ κ

  -- Row singleton formation.
  _R▹_ :
         Type Δ (L ℓ) → Type Δ κ →
         -------------------
         Type Δ R[ κ ]

  -- label constant formation.
  ⌊_⌋ :
        Type Δ (L ℓ) →
        ----------
        Type Δ (★ ℓ)

  -- Record formation.
  Π :
      Type Δ R[ κ ] →
      -------------
      Type Δ  κ

  -- Variant formation.
  Σ :
      Type Δ R[ κ ] →
      -------------
      Type Δ κ

  -- Lifting/mapping operations... I claim the kinds are at least
  -- self-evident now, even if the placement of arrows is a little bit
  -- arbitrary...

  ↑_ : {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} →
       Type Δ R[ κ₁ `→ κ₂ ] →
       ------------------------------
       Type Δ (κ₁ `→ R[ κ₂ ])


  _↑ : {κ₁ : Kind ℓ₁} {κ₂ : Kind ℓ₂} →
       Type Δ (κ₁ `→ κ₂) →
       ------------------------------
       Type Δ (R[ κ₁ ] `→ R[ κ₂ ])

  ------------------------------------------------------------
  -- System Rωμ.

  -- μ formation.
  μ : ∀ {ℓ} →
      (τ : Type Δ ((★ ℓ) `→ (★ ℓ))) →
      -----------------------------------------------
      Type Δ (★ ℓ)

--------------------------------------------------------------------------------
-- Testing.
