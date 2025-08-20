module Rome.Types.Theorems.Denotation where

open import Rome.Prelude

open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Substitution
open import Rome.Types.Renaming

open import Rome.Types.Normal.Syntax
open import Rome.Types.Normal.Renaming
open import Rome.Types.Normal.Properties.Renaming

open import Rome.Types.Semantic.Syntax
open import Rome.Types.Semantic.NBE
open import Rome.Types.Semantic.Renaming

open import Rome.Types.Theorems.Soundness
open import Rome.Types.Theorems.Consistency
open import Rome.Types.Theorems.Stability

open import Rome.Types.Equivalence.Relation

open import Rome.Terms.Normal.Syntax
open import Rome.Terms.Normal.Reduction
open import Rome.Terms.Normal.GVars

--------------------------------------------------------------------------------
--

postulate 
  ⟦_⟧nf : NormalType Δ κ → Set 
  ⟦_⟧ : ∀ {τ : NormalType Δ ★} → NormalTerm Γ τ → Set 

⟦_⟧t : Type Δ κ → Set 
⟦ τ ⟧t = ⟦ ⇓ τ ⟧nf 

all-denotations-respected : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⟦ τ₁ ⟧t ≡ ⟦ τ₂ ⟧t
all-denotations-respected eq = cong ⟦_⟧nf (soundness eq)  

normalization-respected : ∀ {τ : Type Δ κ} {υ : NormalType Δ κ } → ⇓ τ ≡ υ → ⟦ τ ⟧t ≡ ⟦ υ ⟧nf 
normalization-respected refl = refl

more? : ∀ {τ : NormalType Δ κ} {υ : Type Δ κ } → ⇑ τ ≡t υ → ⟦ τ ⟧nf ≡ ⟦ υ ⟧t
more? eq rewrite (sym (soundness eq)) = cong ⟦_⟧nf (sym (stability _)) 

⟦Consistency⟧ : ∀ {τ : NormalType ∅ ★} (M N : NormalTerm ∅ τ) → M —→ N → ⟦ M ⟧ ≡ ⟦ N ⟧
⟦Consistency⟧ M N (ξ-·1 step) = {! ⟦Consistency⟧ _ _ step  !}
⟦Consistency⟧ M N (ξ-·2 step) = {!   !}
⟦Consistency⟧ M N (ξ-·[] step) = {!   !}
⟦Consistency⟧ M N (ξ-·⟨⟩ step) = {!   !}
⟦Consistency⟧ M N (ξ-Out step) = {!   !}
⟦Consistency⟧ M N (ξ-In step) = {!   !}
⟦Consistency⟧ M N (ξ-Π▹₁ M₁ ℓ₁ ℓ₂ step) = {!   !}
⟦Consistency⟧ M N (ξ-Σ M₁ M₂ i step) = {!   !}
⟦Consistency⟧ M N (ξ-Π/₁ M₁ M₂ ℓ step) = {!   !}
⟦Consistency⟧ M N (ξ-Π/₂ M₁ ℓ₁ ℓ₂ step) = {!   !}
⟦Consistency⟧ M N (ξ-Σ▹₁ M₁ ℓ₁ ℓ₂ step) = {!   !}
⟦Consistency⟧ M N (ξ-Σ/₁ M₁ M₂ ℓ step) = {!   !}
⟦Consistency⟧ M N (ξ-Σ/₂ M₁ ℓ₁ ℓ₂ step) = {!   !}
⟦Consistency⟧ M N (ξ-prj M₁ M₂ e step) = {!   !}
⟦Consistency⟧ M N (ξ-prj⇒ M₁ e₁ e₂ x) = {!   !}
⟦Consistency⟧ M N (ξ-inj M₁ M₂ e step) = {!   !}
⟦Consistency⟧ M N (ξ-inj⇒ M₁ e₁ e₂ x) = {!   !}
⟦Consistency⟧ M N (ξ-⊹₁ M₁ M₂ N₁ e step) = {!   !}
⟦Consistency⟧ M N (ξ-⊹₂ M₁ N₁ N₂ e step) = {!   !}
⟦Consistency⟧ M N (ξ-⊹₃ M₁ N₁ e₁ e₂ x) = {!   !}
⟦Consistency⟧ M N (ξ-▿₁ M₁ M₂ N₁ e step) = {!   !}
⟦Consistency⟧ M N (ξ-▿₂ M₁ N₁ N₂ e step) = {!   !}
⟦Consistency⟧ M N (ξ-▿₃ M₁ N₁ e₁ e₂ x) = {!   !}
⟦Consistency⟧ M N (ξ-Syn ρ φ M₁ M₂ step) = {!   !}
⟦Consistency⟧ M N (ξ-Ana ρ φ τ eq₁ eq₂ M₁ M₂ step) = {!   !}
⟦Consistency⟧ M N (ξ-⟨⟩ x) = {!   !}
⟦Consistency⟧ M N β-λ = {!   !}
⟦Consistency⟧ M N β-Λ = {!   !}
⟦Consistency⟧ M N β-ƛ = {!   !}
⟦Consistency⟧ M N δ-In = {!   !}
⟦Consistency⟧ M N (δ-fix M₁) = {!   !}
⟦Consistency⟧ M N (δ-Π▹ M₁) = {!   !}
⟦Consistency⟧ M N (δ-Σ▹ M₁) = {!   !}
⟦Consistency⟧ M N (δ-Π/ .N ℓ) = {!   !}
⟦Consistency⟧ M N (δ-Σ/ .N ℓ) = {!   !}
⟦Consistency⟧ M N (δ-prj rys i) = {!   !}
⟦Consistency⟧ M N (δ-inj l M₁ i h) = {!   !}
⟦Consistency⟧ M N (δ-⊹ r₁ r₂ i₁ i₂ i₃) = {!   !}
⟦Consistency⟧ M N (δ-▿₁ F G e M₁ i₁ i₂) = {!   !}
⟦Consistency⟧ M N (δ-▿₂ F G e M₁ i₁ i₂) = {!   !}
⟦Consistency⟧ M N (δ-ana φ _ φυ eq₂ M₁ l N₁ V i) = {!   !}
⟦Consistency⟧ M N (δ-syn φ eq M₁) = {!   !} 


--------------------------------------------------------------------------------
-- The above makes me think it would be more interesting to define ⟦_⟧ and ⟦_⟧nf independently.
-- Although then I would need a notion of reduction on semantic types.
