module Rome.Both.Types.Theorems.Denotation where

open import Rome.Both.Prelude

open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Syntax
open import Rome.Both.Types.Substitution
open import Rome.Both.Types.Renaming

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Normal.Renaming
open import Rome.Both.Types.Normal.Properties.Renaming

open import Rome.Both.Types.Semantic.Syntax
open import Rome.Both.Types.Semantic.NBE
open import Rome.Both.Types.Semantic.Renaming

open import Rome.Both.Types.Theorems.Completeness
open import Rome.Both.Types.Theorems.Soundness
open import Rome.Both.Types.Theorems.Stability

open import Rome.Both.Types.Equivalence.Relation

open import Rome.Both.Terms.Normal.Syntax
open import Rome.Both.Terms.Normal.Reduction
open import Rome.Both.Terms.Normal.GVars

--------------------------------------------------------------------------------
--

postulate 
  ⟦_⟧nf : NormalType Δ κ → Set 
  ⟦_⟧ : ∀ {τ : NormalType Δ ★} → NormalTerm Γ τ → Set 

⟦_⟧t : Type Δ κ → Set 
⟦ τ ⟧t = ⟦ ⇓ τ ⟧nf 

all-denotations-respected : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡t τ₂ → ⟦ τ₁ ⟧t ≡ ⟦ τ₂ ⟧t
all-denotations-respected eq = cong ⟦_⟧nf (completeness eq)  

normalization-respected : ∀ {τ : Type Δ κ} {υ : NormalType Δ κ } → ⇓ τ ≡ υ → ⟦ τ ⟧t ≡ ⟦ υ ⟧nf 
normalization-respected refl = refl

more? : ∀ {τ : NormalType Δ κ} {υ : Type Δ κ } → ⇑ τ ≡t υ → ⟦ τ ⟧nf ≡ ⟦ υ ⟧t
more? eq rewrite (sym (completeness eq)) = cong ⟦_⟧nf (sym (stability _)) 

⟦Soundness⟧ : ∀ {τ : NormalType ∅ ★} (M N : NormalTerm ∅ τ) → M —→ N → ⟦ M ⟧ ≡ ⟦ N ⟧
⟦Soundness⟧ M N (ξ-·1 step) = {! ⟦Soundness⟧ _ _ step  !}
⟦Soundness⟧ M N (ξ-·2 step) = {!   !}
⟦Soundness⟧ M N (ξ-·[] step) = {!   !}
⟦Soundness⟧ M N (ξ-·⟨⟩ step) = {!   !}
⟦Soundness⟧ M N (ξ-Out step) = {!   !}
⟦Soundness⟧ M N (ξ-In step) = {!   !}
⟦Soundness⟧ M N (ξ-Π▹₁ M₁ ℓ₁ ℓ₂ step) = {!   !}
⟦Soundness⟧ M N (ξ-Σ M₁ M₂ i step) = {!   !}
⟦Soundness⟧ M N (ξ-Π/₁ M₁ M₂ ℓ step) = {!   !}
⟦Soundness⟧ M N (ξ-Π/₂ M₁ ℓ₁ ℓ₂ step) = {!   !}
⟦Soundness⟧ M N (ξ-Σ▹₁ M₁ ℓ₁ ℓ₂ step) = {!   !}
⟦Soundness⟧ M N (ξ-Σ/₁ M₁ M₂ ℓ step) = {!   !}
⟦Soundness⟧ M N (ξ-Σ/₂ M₁ ℓ₁ ℓ₂ step) = {!   !}
⟦Soundness⟧ M N (ξ-prj M₁ M₂ e step) = {!   !}
⟦Soundness⟧ M N (ξ-prj⇒ M₁ e₁ e₂ x) = {!   !}
⟦Soundness⟧ M N (ξ-inj M₁ M₂ e step) = {!   !}
⟦Soundness⟧ M N (ξ-inj⇒ M₁ e₁ e₂ x) = {!   !}
⟦Soundness⟧ M N (ξ-⊹₁ M₁ M₂ N₁ e step) = {!   !}
⟦Soundness⟧ M N (ξ-⊹₂ M₁ N₁ N₂ e step) = {!   !}
⟦Soundness⟧ M N (ξ-⊹₃ M₁ N₁ e₁ e₂ x) = {!   !}
⟦Soundness⟧ M N (ξ-▿₁ M₁ M₂ N₁ e step) = {!   !}
⟦Soundness⟧ M N (ξ-▿₂ M₁ N₁ N₂ e step) = {!   !}
⟦Soundness⟧ M N (ξ-▿₃ M₁ N₁ e₁ e₂ x) = {!   !}
⟦Soundness⟧ M N (ξ-Syn ρ φ M₁ M₂ step) = {!   !}
⟦Soundness⟧ M N (ξ-Ana ρ φ τ eq₁ eq₂ M₁ M₂ step) = {!   !}
⟦Soundness⟧ M N (ξ-⟨⟩ x) = {!   !}
⟦Soundness⟧ M N β-λ = {!   !}
⟦Soundness⟧ M N β-Λ = {!   !}
⟦Soundness⟧ M N β-ƛ = {!   !}
⟦Soundness⟧ M N δ-In = {!   !}
⟦Soundness⟧ M N (δ-fix M₁) = {!   !}
⟦Soundness⟧ M N (δ-Π▹ M₁) = {!   !}
⟦Soundness⟧ M N (δ-Σ▹ M₁) = {!   !}
⟦Soundness⟧ M N (δ-Π/ .N ℓ) = {!   !}
⟦Soundness⟧ M N (δ-Σ/ .N ℓ) = {!   !}
⟦Soundness⟧ M N (δ-prj rys i) = {!   !}
⟦Soundness⟧ M N (δ-inj l M₁ i h) = {!   !}
⟦Soundness⟧ M N (δ-⊹ r₁ r₂ i₁ i₂ i₃) = {!   !}
⟦Soundness⟧ M N (δ-▿₁ F G e M₁ i₁ i₂) = {!   !}
⟦Soundness⟧ M N (δ-▿₂ F G e M₁ i₁ i₂) = {!   !}
⟦Soundness⟧ M N (δ-ana φ _ φυ eq₂ M₁ l N₁ V i) = {!   !}
⟦Soundness⟧ M N (δ-syn φ eq M₁) = {!   !} 


--------------------------------------------------------------------------------
-- The above makes me think it would be more interesting to define ⟦_⟧ and ⟦_⟧nf independently.
-- Although then I would need a notion of reduction on semantic types.
