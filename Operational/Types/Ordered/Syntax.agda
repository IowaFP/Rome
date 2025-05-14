module Rome.Operational.Types.Ordered.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

-- open import Rome.Operational.Types.Syntax

--------------------------------------------------------------------------------
-- Types


infixl 5 _·_
infixr 5 _≲_
data Pred (Ty : KEnv → Kind → Set) Δ : Kind → Set
data Type Δ : Kind → Set 

SimpleRow : (Ty : KEnv → Kind → Set) → KEnv → Kind → Set 
SimpleRow Ty Δ ★        = ⊥
SimpleRow Ty Δ L        = ⊥
SimpleRow Ty Δ (_ `→ _) = ⊥
SimpleRow Ty Δ R[ κ ]   = List (Ty Δ L × Ty Δ κ)

open import Data.String using (_<_)

Ordered : SimpleRow Type Δ R[ κ ] → Set 
ordered? : ∀ (xs : SimpleRow Type Δ R[ κ ]) → Dec (Ordered xs)

--------------------------------------------------------------------------------
-- Predicates

data Pred Ty Δ where
  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : Ty Δ R[ κ ]) → 
       --------------------- 
       Pred Ty Δ R[ κ ]

  _≲_ : 

       (ρ₁ ρ₂ : Ty Δ R[ κ ]) →
       ----------
       Pred Ty Δ R[ κ ]  
       
data Type Δ where

  ` : 
      (α : KVar Δ κ) →
      --------
      Type Δ κ

  `λ : 
      
      (τ : Type (Δ ,, κ₁) κ₂) → 
      ---------------
      Type Δ (κ₁ `→ κ₂)

  _·_ : 
      
      (τ₁ : Type Δ (κ₁ `→ κ₂)) → 
      (τ₂ : Type Δ κ₁) → 
      ----------------
      Type Δ κ₂

  _`→_ : 

         (τ₁ : Type Δ ★) →
         (τ₂ : Type Δ ★) → 
         --------
         Type Δ ★

  `∀    :
      
         {κ : Kind} → (τ : Type (Δ ,, κ) ★) →
         -------------
         Type Δ ★

  μ     :
      
         (φ : Type Δ (★ `→ ★)) → 
         -------------
         Type Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : 

         (π : Pred Type Δ R[ κ₁ ]) → (τ : Type Δ ★) → 
         ---------------------
         Type Δ ★       


  ------------------------------------------------------------------
  -- Rω business

  ⦅_⦆ : (xs : SimpleRow Type Δ R[ κ ]) → True (ordered? xs) → 
        ----------------------
        Type Δ R[ κ ]

  -- labels
  lab :
    
        (l : Label) → 
        --------
        Type Δ L

  -- label constant formation
  ⌊_⌋ :
        (τ : Type Δ L) →
        ----------
        Type Δ ★

--   ε : 

--     ------------
--     Type Δ R[ κ ]

  -- Row formation
  _▹_ :
         (l : Type Δ L) → (τ : Type Δ κ) → 
         -------------------
         Type Δ R[ κ ]

  _<$>_ : 

       (φ : Type Δ (κ₁ `→ κ₂)) → (τ : Type Δ R[ κ₁ ]) → 
       ----------------------------------------
       Type Δ R[ κ₂ ]

  -- Record formation
  Π     :

          ----------------
          Type Δ (R[ κ ] `→ κ)

  -- Variant formation
  Σ     :

          ----------------
          Type Δ (R[ κ ] `→ κ)

Ordered [] = ⊤
Ordered (x ∷ []) = ⊤
Ordered ((lab l₁ , _) ∷ (lab l₂ , _) ∷ xs) = l₁ < l₂ × Ordered xs
Ordered _ = ⊥

ordered? [] = yes tt
ordered? (x ∷ []) = yes tt
ordered? ((lab l₁ , _) ∷ (lab l₂ , _) ∷ xs) with l₁ <? l₂ | ordered? xs
... | yes p | yes q  = yes (p , q)
... | yes p | no q  = no (λ { (_ , oxs) → q oxs })
... | no p  | yes q  = no (λ { (x , _) → p x})
... | no  p | no  q  = no (λ { (x , _) → p x})
ordered? ((` α , snd₁) ∷ (` α₁ , snd₂) ∷ xs) = no (λ ())
ordered? ((` α , snd₁) ∷ (fst₂ · fst₃ , snd₂) ∷ xs) = no (λ ())
ordered? ((` α , snd₁) ∷ (lab l , snd₂) ∷ xs) = no (λ ())
ordered? ((fst₁ · fst₂ , snd₁) ∷ (` α , snd₂) ∷ xs) = no (λ ())
ordered? ((fst₁ · fst₂ , snd₁) ∷ (fst₃ · fst₄ , snd₂) ∷ xs) = no (λ ())
ordered? ((fst₁ · fst₂ , snd₁) ∷ (lab l , snd₂) ∷ xs) = no (λ ())
ordered? ((lab l , snd₁) ∷ (` α , snd₂) ∷ xs) = no (λ ())
ordered? ((lab l , snd₁) ∷ (fst₂ · fst₃ , snd₂) ∷ xs) = no (λ ())

--------------------------------------------------------------------------------
-- The empty row is the empty simple row

ε : Type Δ R[ κ ]
ε = ⦅ [] ⦆ tt

--------------------------------------------------------------------------------
-- Type constant smart-ish constructors

-- Record formation
`Π : Type Δ R[ κ ] → Type Δ κ 
`Π τ = Π · τ 

-- Variant formation
`Σ : Type Δ R[ κ ] → Type Δ κ 
`Σ τ = Σ · τ 

Unit : Type Δ ★
Unit = Π · ε

sing : Type (Δ ,, L) R[ ★ ] 
sing = ⦅ [ (` Z , Unit) ] ⦆ tt
-- Example simple row
sr : Type (Δ ,, L) R[ ★ ] 
sr = ⦅ (lab "a" , Unit) ∷ (lab "b" , (Σ · ε)) ∷ (lab "c" , ((`λ (` Z)) · Unit)) ∷ (lab "e" , Unit) ∷ [] ⦆ tt

-- --------------------------------------------------------------------------------
-- -- Delabeling

-- import Rome.Operational.Types.Syntax as Types
-- delabel : Type Δ κ → Types.Type Δ κ 
-- delabelPred : Pred Type Δ κ → Types.Pred Types.Type Δ κ 
-- delabelRow : SimpleRow Type Δ R[ κ ] → Types.SimpleRow Types.Type Δ R[ κ ]

-- delabelPred (ρ₁ · ρ₂ ~ ρ₃) = Types._·_~_ (delabel ρ₁)  (delabel ρ₂) (delabel ρ₃)
-- delabelPred (ρ₁ ≲ ρ₂) = Types._≲_ (delabel ρ₁) (delabel ρ₂)

-- delabel (` α) = Types.` α
-- delabel (`λ τ) = Types.`λ (delabel τ)
-- delabel (τ₁ · τ₂) = delabel τ₁ Types.· delabel τ₂
-- delabel (τ₁ `→ τ₂) = delabel τ₁ Types.`→ delabel τ₂
-- delabel (`∀ τ) = Types.`∀ (delabel τ)
-- delabel (μ τ) = Types.μ (delabel τ)
-- delabel (π ⇒ τ) = (delabelPred π) Types.⇒ (delabel τ)
-- delabel (⦅ [] ⦆ x) = Types.⦅ [] ⦆
-- delabel (⦅ xs ⦆ _) = {!!}
-- delabel (lab l) = {!!}
-- delabel ⌊ τ ⌋ = {!!}
-- delabel (τ ▹ τ₁) = {!!}
-- delabel (τ <$> τ₁) = {!!}
-- delabel Π = {!!}
-- delabel Σ = {!!}
