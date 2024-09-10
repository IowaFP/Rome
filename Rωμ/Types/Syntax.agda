module Rωμ.Types.Syntax where

open import Preludes.Relation
open import Preludes.Data
open import Rωμ.Kinds.Syntax
open import Rωμ.GVars.Kinds


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

data Type : KEnv → Kind →  Set
data Pred (Δ : KEnv) : (κ : Kind) → Set
data Row : KEnv → Kind → Set 

data Pred Δ where
  _≲_ : ∀ {κ : Kind} →
          (ρ₁ : Type Δ R[ κ ]) →
          (ρ₂ : Type Δ R[ κ ]) →
          Pred Δ κ

  _·_~_ : ∀ {κ : Kind} →
            (ρ₁ : Type Δ R[ κ ]) →
            (ρ₂ : Type Δ R[ κ ]) →
            (ρ₃ : Type Δ R[ κ ]) →
            Pred Δ κ

--------------------------------------------------------------------------------
-- Type vars.
data TVar : KEnv → Kind → Set where
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
          Type Δ ★ → Type Δ ★ →
          -----------------------------------
          Type Δ ★

  `∀ :
          (κ : Kind) → Type (Δ ، κ) ★ →
          -------------------------------------
          Type Δ ★

  `λ :
          (κ₁ : Kind) → Type (Δ ، κ₁) κ₂ →
          -----------------------------------------
          Type Δ (κ₁ `→ κ₂)

  _·[_] :
          Type Δ (κ₁ `→ κ₂) → Type Δ κ₁ →
          -----------------------------
          Type Δ κ₂

  ------------------------------------------------------------
  -- Qualified types.

  _⇒_ : ∀ {κ : Kind} →
         (π : Pred Δ κ) → Type Δ ★ →
         --------------------------------
         Type Δ ★

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
        Type Δ L

  -- singleton formation.
  _▹_ :
        Type Δ L → Type Δ κ →
        -------------------
        Type Δ κ

  -- Row singleton formation.
  _R▹_ :
         Type Δ L → Type Δ κ →
         -------------------
         Type Δ R[ κ ]

  -- label constant formation.
  ⌊_⌋ :
        Type Δ L →
        ----------
        Type Δ ★

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

  ↑_ : {κ₁ : Kind} {κ₂ : Kind} →
       Type Δ R[ κ₁ `→ κ₂ ] →
       ------------------------------
       Type Δ (κ₁ `→ R[ κ₂ ])


  _↑ : {κ₁ : Kind} {κ₂ : Kind} →
       Type Δ (κ₁ `→ κ₂) →
       ------------------------------
       Type Δ (R[ κ₁ ] `→ R[ κ₂ ])

  ------------------------------------------------------------
  -- System Rωμ.

  -- μ formation.
  μ : 
      (τ : Type Δ (★ `→ ★)) →
      -----------------------------------------------
      Type Δ ★

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
  end : ∀ {l}{τ : Type Δ κ} →

        --------------------------------
         (lab l R▹ τ) ∈ (l ▹ τ)

  here : ∀ {l} {τ : Type Δ κ} {m : Row Δ κ} {ev : l ∉ m} → 

         ---------------------------------------
         (lab l R▹ τ) ∈ (l ▹ τ ， m) {ev}

  there  : ∀ {l₁ l₂}{τ₁ τ₂ : Type Δ κ} {m : Row Δ κ} {ev : l₂ ∉ m} → 

            (lab l₁ R▹ τ₁) ∈ m  → 
           ---------------------------------------------
           (lab l₁ R▹ τ₁) ∈ ((l₂ ▹ τ₂ ， m) {ev})

_⊆_ {Δ = Δ} {κ = κ} m₁ m₂ =
  ∀ (l : Label) (τ : Type Δ κ) → 
    (lab l R▹ τ) ∈ m₁ → (lab l R▹ τ) ∈ m₂

there⊆ : ∀ {l₁} {τ₁ : Type Δ κ} (ρ₁ ρ₂ : Row Δ κ) {ev : l₁ ∉ ρ₁} → 
         (l₁ ▹ τ₁ ， ρ₁) {ev} ⊆ ρ₂ → ρ₁ ⊆ ρ₂
there⊆ ρ₁ ρ₂ ι l₂ τ₂ e = ι _ _ (there e)

--------------------------------------------------------------------------------
-- Simple row concatenation.

_#_ : Row Δ κ → Row Δ κ → Set
_++_ : (ρ₁ : Row Δ κ) → (ρ₂ : Row Δ κ) → {_ : ρ₁ # ρ₂} → Row Δ κ

(l ▹ τ) # ρ₂ =  l ∉ ρ₂
((l ▹ τ ， ρ₁) # ρ₂) = l ∉ ρ₂ × Σ[ ev ∈ (ρ₁ # ρ₂) ] (l ∉ ((ρ₁ ++ ρ₂) {ev}))

((l ▹ τ) ++ ρ₂) {ev} = (l ▹ τ ， ρ₂) {ev}
(((l ▹ τ ， ρ₁) {ev₁}) ++ ρ₂) {_ , ( ρ₁#ρ₂ , l∉ρ₁++ρ₂)} = (l ▹ τ ， (ρ₁ ++ ρ₂) {ρ₁#ρ₂}) {l∉ρ₁++ρ₂} 

infixr 10 _++_
infixr 10 _#_
