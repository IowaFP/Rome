module Rome.Types.Pre.Syntax where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars


data Pred (Δ : KEnv) : Set 
data Type (Δ : KEnv) : Set 
data Pred Δ where
    _·_~_ : 

        (ρ₁ ρ₂ ρ₃ : Type Δ) → 
        --------------------- 
        Pred Δ 

    _≲_ : 

        (ρ₁ ρ₂ : Type Δ) →
        ----------
        Pred Δ

data Type Δ where

    ` : 
        KVar Δ κ  → 
        --------
        Type Δ 

    `λ : ∀
    
        (τ : Type (Δ ,, κ₁)) → 
        ---------------
        Type Δ

    _·_ : 
    
        (τ₁ : Type Δ) → 
        (τ₂ : Type Δ) → 
        ----------------
        Type Δ

    _`→_ : 

            (τ₁ : Type Δ) →
            (τ₂ : Type Δ) → 
            --------
            Type Δ

    `∀    :
    
            {κ : Kind} → (τ : Type (Δ ,, κ)) →
            -------------
            Type Δ

    μ     :
    
            (φ : Type Δ) → 
            -------------
            Type Δ

    ------------------------------------------------------------------
    -- Qualified types

    _⇒_ : 

            (π : Pred Δ) → (τ : Type Δ) → 
            ---------------------
            Type Δ       


    ------------------------------------------------------------------
    -- Rω business

    -- labels
    lab :
    
        (l : Label) → 
        --------
        Type Δ

    -- label constant formation
    ⌊_⌋ :
        (τ : Type Δ) →
        ----------
        Type Δ

    ε : 

        ------------
        Type Δ

    -- Row formation
    _▹_ :
            (l : Type Δ) → (τ : Type Δ) → 
            -------------------
            Type Δ

    _<$>_ : 

        (φ : Type Δ) → (τ : Type Δ) → 
        ----------------------------------------
        Type Δ

    -- Record formation
    Π     :

            ----------------
            Type Δ

    -- Variant formation
    Σ     :

            ----------------
            Type Δ
