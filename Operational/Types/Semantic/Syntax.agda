{-# OPTIONS --allow-unsolved-metas #-}
module Rome.Operational.Types.Semantic.Syntax where

open import Data.Product using (_×_ ; _,_)
open import Rome.Operational.Prelude
open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Renaming using (liftₖ ; Renamingₖ)

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming


--------------------------------------------------------------------------------
-- Semantic types (signatures)
  
SemType : KEnv → Kind → Set
KripkeFunction : KEnv → Kind → Kind → Set
KripkeFunction Δ₁ κ₁ κ₂ =  (∀ {Δ₂} → Renamingₖ Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂)

--------------------------------------------------------------------------------
-- Semantic Rows

Row : KEnv → Kind → Set 
Row Δ ★ = ⊥ 
Row Δ L = ⊥ 
Row Δ (_ `→ _) = ⊥ 
Row Δ R[ κ ] = ∃[ n ](Fin n → SemType Δ κ)

_⨾⨾_ :  SemType Δ κ → Row Δ R[ κ ] → Row Δ R[ κ ]
τ ⨾⨾ (n , P) =  suc n , λ { fzero    → τ 
                          ; (fsuc x) → P x }

-- the empty row                                  
εV : Row Δ R[ κ ] 
εV = 0 , λ ()

-- Singleton rows
⁅_⁆ : SemType Δ κ → Row Δ R[ κ ] 
⁅ τ ⁆ = 1 , λ { fzero → τ }

subst-Fin : ∀ {n m : ℕ} → n ≡ m → Fin n → Fin m
subst-Fin refl x = x

subst-Row : ∀ {A : Set} {n m : ℕ} → n ≡ m → (f : Fin n → A) → Fin m → A 
subst-Row refl f = f

--------------------------------------------------------------------------------
-- Semantic types (definition)


SemType Δ ★ = NormalType Δ ★
SemType Δ L = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = KripkeFunction Δ₁ κ₁ κ₂ 
SemType Δ R[ κ ] = NeutralType Δ R[ κ ] or Row Δ R[ κ ]
