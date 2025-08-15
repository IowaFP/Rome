module Rome.Both.Types.Theorems.Denotation where

open import Rome.Both.Prelude

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars
open import Rome.Both.Kinds.Denotation

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Substitution
open import Rome.Both.Types.Renaming

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Properties.Renaming

open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.NBE
open import Rome.Both.Types.Semantic.Renaming

open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Consistency
open import Rome.Both.Types.Theorems.Stability

open import Rome.Both.Types.Equivalence.Relation

--------------------------------------------------------------------------------
-- Any denotation of normal types can be lifted to types in a manner that
-- respects type equivalence.
-- 
-- (N.b. need also a meaning of environments, but could instead define this over
-- closed types.)

module anyDenotation (⟦_⟧nf : NormalType Δ κ → ⟦ κ ⟧k) where 

  ⟦_⟧t : Type Δ κ → ⟦ κ ⟧k
  ⟦ τ ⟧t = ⟦_⟧nf (⇓ τ)

  all-denotations-respected : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⟦ τ₁ ⟧t ≡ ⟦ τ₂ ⟧t
  all-denotations-respected eq = cong ⟦_⟧nf (soundness eq)  

  normalization-respected : ∀ {τ : Type Δ κ} {υ : NormalType Δ κ } → ⇓ τ ≡ υ → ⟦ τ ⟧t ≡ ⟦ υ ⟧nf 
  normalization-respected refl = refl

  more? : ∀ {τ : NormalType Δ κ} {υ : Type Δ κ } → ⇑ τ ≡t υ → ⟦ τ ⟧nf ≡ ⟦ υ ⟧t
  more? eq rewrite (sym (soundness eq)) = cong ⟦_⟧nf (sym (stability _)) 
