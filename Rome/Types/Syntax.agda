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
-- infixr 10 _▹_
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
data Row : KEnv ℓ → Kind ι → Set 


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

  ⦃-_-⦄ : Row Δ κ → 
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
-- Primitive rows.

data _∈_ : Type Δ R[ κ ] → Row Δ κ → Set
_⊆_ : Row Δ κ → Row Δ κ → Set
_∉_ : Label → Row Δ κ → Set 

data Row where
  _▹_ : (l : Label) → (τ : Type Δ κ) → Row Δ κ
  _▹_，_ : (l : Label) → (τ : Type Δ κ) → (xs : Row Δ κ) → 
          {_ : l ∉ xs}  → Row Δ κ

infixr 5 _▹_
infixr 4 _▹_，_

l₁ ∉ (l₂ ▹ τ)  with l₁ ≟ l₂ 
... | yes p = ⊥₀
... | no  p = ⊤₀
l₁ ∉ (l₂ ▹ _ ， mr) with l₁ ≟ l₂
... | yes p  = ⊥₀
... | no  p  = l₁ ∉ mr 

--------------------------------------------------------------------------------
-- Row membership.

data _∈_ where
  end : ∀ {ℓ}{l}{τ : Type Δ κ} →

        --------------------------------
         (lab {ℓ = ℓ} l R▹ τ) ∈ (l ▹ τ)

  here : ∀ {ℓ}{l}{τ : Type Δ κ} {m : Row Δ κ} {ev : l ∉ m} → 

         ---------------------------------------
         (lab {ℓ = ℓ} l R▹ τ) ∈ (l ▹ τ ， m) {ev}

  there  : ∀ {ℓ}{l₁ l₂}{τ₁ τ₂ : Type Δ κ} {m : Row Δ κ} {ev : l₂ ∉ m} → 

            (lab {ℓ = ℓ} l₁ R▹ τ₁) ∈ m  → 
           ---------------------------------------------
           (lab {ℓ = ℓ} l₁ R▹ τ₁) ∈ ((l₂ ▹ τ₂ ， m) {ev})

_⊆_ {Δ = Δ} {κ = κ} m₁ m₂ =
  ∀ {ℓ} (l : Label) (τ : Type Δ κ) → 
    (lab {ℓ = ℓ} l R▹ τ) ∈ m₁ → (lab {ℓ = ℓ} l R▹ τ) ∈ m₂

there⊆ : ∀ {l₁} {τ₁ : Type Δ κ} (ρ₁ ρ₂ : Row Δ κ) {ev : l₁ ∉ ρ₁} → 
         (l₁ ▹ τ₁ ， ρ₁) {ev} ⊆ ρ₂ → ρ₁ ⊆ ρ₂
there⊆ ρ₁ ρ₂ ι l₂ τ₂ e = ι _ _ (there e)

--------------------------------------------------------------------------------
-- Simple row concatenation.


-- :) I remain foolishly committed to recursively defined predicates for no good reason.
_#_ : Row Δ κ → Row Δ κ → Set
_++_ : (ρ₁ : Row Δ κ) → (ρ₂ : Row Δ κ) → {_ : ρ₁ # ρ₂} → Row Δ κ

(l ▹ τ) # ρ₂ =  l ∉ ρ₂
((l ▹ τ ， ρ₁) # ρ₂) = l ∉ ρ₂ × Σ[ ev ∈ (ρ₁ # ρ₂) ] (l ∉ ((ρ₁ ++ ρ₂) {ev}))

((l ▹ τ) ++ ρ₂) {ev} = (l ▹ τ ， ρ₂) {ev}
(((l ▹ τ ， ρ₁) {ev₁}) ++ ρ₂) {_ , ( ρ₁#ρ₂ , l∉ρ₁++ρ₂)} = (l ▹ τ ， (ρ₁ ++ ρ₂) {ρ₁#ρ₂}) {l∉ρ₁++ρ₂} 

infixr 10 _++_
infixr 10 _#_
