module Rome.Operational.Types.Syntax where

open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Data.String using (_<_; _<?_)

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

  ⦅_⦆ : (xs : SimpleRow Type Δ R[ κ ]) (ordered : True (ordered? xs)) →
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
  -- _▹_ :
  --        (l : Type Δ L) → (τ : Type Δ κ) → 
  --        -------------------
  --        Type Δ R[ κ ]

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

fmap× : ∀ {Ty : KEnv → Kind → Set} → (∀ {κ} → Ty Δ₁ κ → Ty Δ₂ κ) → Ty Δ₁ L × Ty Δ₁ κ → Ty Δ₂ L × Ty Δ₂ κ
fmap× f (x , y) = f x , f y

map-overᵣ : ∀ (ρ : SimpleRow Type Δ₁ R[ κ₁ ]) (f : Type Δ₁ κ₁ → Type Δ₁ κ₂) → 
              Ordered ρ → Ordered (map (overᵣ f) ρ)
map-overᵣ [] f oρ = tt
map-overᵣ (x ∷ []) f oρ = tt
map-overᵣ ((lab l₁ , _) ∷ (lab l₂ , _) ∷ ρ) f (l₁<l₂ , oρ) = l₁<l₂ , (map-overᵣ ρ f oρ)

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

--------------------------------------------------------------------------------
-- Admissable constants

-- for partial application of infix fmap.
`↑ : Type Δ ((κ₁ `→ κ₂) `→ R[ κ₁ ] `→ R[ κ₂ ])
`↑ = `λ (`λ (` (S Z) <$> ` Z))

-- Flapping. See https://hoogle.haskell.org/?hoogle=f%20(a%20-%3E%20b)%20-%3E%20a%20-%3E%20f%20b%20
flap : Type Δ (R[ κ₁ `→ κ₂ ] `→ κ₁ `→ R[ κ₂ ])
flap = `λ (`λ ((`λ ((` Z) · (` (S Z)))) <$> (` (S Z))))

_??_ : Type Δ (R[ κ₁ `→ κ₂ ]) → Type Δ κ₁ → Type Δ R[ κ₂ ]
f ?? a = flap · f · a

Unit : Type Δ ★
Unit = Π · ε

-- Example simple row
sr : Type Δ R[ ★ ] 
sr = ⦅ (lab "a" , Unit) ∷ (lab "b" , (Σ · ε)) ∷ (lab "c" , ((`λ (` Z)) · Unit)) ∷ (lab "d" , Unit) ∷ [] ⦆ tt
       -- (λ { 
       --      fzero → Unit 
       --    ; (fsuc fzero) →  Σ · ε 
       --    ; (fsuc (fsuc fzero)) → ((`λ (` Z)) · Unit)
       --    ; (fsuc (fsuc (fsuc fzero))) → Unit }) ⦆
  
