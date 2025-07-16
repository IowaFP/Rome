module Rome.Operational.Types.Theorems.Denotation where

open import Rome.Operational.Prelude

open import Rome.Operational.Kinds.Syntax
open import Rome.Operational.Kinds.GVars

open import Rome.Operational.Types.Syntax
open import Rome.Operational.Types.Substitution
open import Rome.Operational.Types.Renaming

open import Rome.Operational.Types.Normal.Syntax
open import Rome.Operational.Types.Normal.Renaming
open import Rome.Operational.Types.Normal.Properties.Renaming

open import Rome.Operational.Types.Semantic.Syntax
open import Rome.Operational.Types.Semantic.NBE
open import Rome.Operational.Types.Semantic.Renaming

open import Rome.Operational.Types.Theorems.Completeness
open import Rome.Operational.Types.Theorems.Soundness
open import Rome.Operational.Types.Theorems.Stability

open import Rome.Operational.Types.Equivalence.Relation

--------------------------------------------------------------------------------
--

postulate 
  ⟦_⟧nf : NormalType Δ κ → Set 

⟦_⟧ : Type Δ κ → Set 
⟦ τ ⟧ = ⟦ ⇓ τ ⟧nf 

all-denotations-respected : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⟦ τ₁ ⟧ ≡ ⟦ τ₂ ⟧
all-denotations-respected eq = cong ⟦_⟧nf (completeness eq)  

normalization-respected : ∀ {τ : Type Δ κ} {υ : NormalType Δ κ } → ⇓ τ ≡ υ → ⟦ τ ⟧ ≡ ⟦ υ ⟧nf 
normalization-respected refl = refl

more? : ∀ {τ : NormalType Δ κ} {υ : Type Δ κ } → ⇑ τ ≡t υ → ⟦ τ ⟧nf ≡ ⟦ υ ⟧
more? eq rewrite (sym (completeness eq)) = cong ⟦_⟧nf (sym (stability _)) 


--------------------------------------------------------------------------------
-- The above makes me think it would be more interesting to define ⟦_⟧ and ⟦_⟧nf independently.
-- Although then I would need a notion of reduction on semantic types.
