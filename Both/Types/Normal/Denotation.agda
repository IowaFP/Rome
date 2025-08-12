module Rome.Both.Types.Normal.Denotation where 
open import Rome.Both.Prelude
open import Rome.Preludes.Level

open import Rome.Both.Kinds.Denotation
open import Rome.Both.Kinds.Syntax
open import Rome.Both.Kinds.GVars

open import Rome.Both.Types.Normal.Syntax
open import Rome.Both.Types.Syntax

open import Rome.IndexCalculus.Rows as Ix

--------------------------------------------------------------------------------
-- Denotation of type variables

⟦_⟧tv : TVar Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k 
⟦ Z ⟧tv (_ , k) = k
⟦ S α ⟧tv (η , _) = ⟦ α ⟧tv η

--------------------------------------------------------------------------------
-- Denotation of normal types, neutral types, predicates, and rows

⟦_⟧nf : NormalType Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦_⟧ne : NeutralType Δ κ → ⟦ Δ ⟧ke → ⟦ κ ⟧k
⟦_⟧p : ∀ {κ : Kind ι} → Pred (NormalType Δ R[ κ ]) → ⟦ Δ ⟧ke → Set (lsuc ι)
⟦_⟧row : SimpleRow (NormalType Δ R[ κ ]) → ⟦ Δ ⟧ke → ⟦ R[ κ ] ⟧k

⟦ ρ₁ ≲ ρ₂ ⟧p H = Ix._≲_ (⟦ ρ₁ ⟧nf H) (⟦ ρ₂ ⟧nf H)
⟦ ρ₁ · ρ₂ ~ ρ₃ ⟧p H = Ix._·_~_ (⟦ ρ₁ ⟧nf H) (⟦ ρ₂ ⟧nf H) (⟦ ρ₃ ⟧nf H)

⟦ ` α ⟧ne η = ⟦ α ⟧tv η
⟦ n · τ ⟧ne η = ⟦ n ⟧ne η (⟦ τ ⟧nf η) 

⟦ ne n ⟧nf η = ⟦ n ⟧ne η
⟦ φ <$> x ⟧nf η with ⟦ x ⟧ne η 
... | (n , P) = n , map₂ (⟦ φ ⟧nf η) ∘ P
⟦ `λ {κ₁ = κ₁} τ ⟧nf η = λ (x : ⟦ κ₁ ⟧k) → ⟦ τ ⟧nf (η , x)
⟦ τ₁ `→ τ₂ ⟧nf η = ⟦ τ₁ ⟧nf η → ⟦ τ₂ ⟧nf η
⟦ `∀ {κ = κ} τ ⟧nf η = ∀ (x : ⟦ κ ⟧k) → ⟦ τ ⟧nf (η , x)
⟦ π ⇒ τ ⟧nf η = {! (⟦ π ⟧p η) →  ⟦ τ ⟧nf η !} -- (⟦ π ⟧p η) → ⟦ τ ⟧nf η
⟦ ⦅ ρ ⦆ oρ ⟧nf η = {!   !}
⟦ lab l ⟧nf η = # l
⟦ ⌊ τ ⌋ ⟧nf η = ⊤'
⟦ Π ρ ⟧nf η = {! Ix  !}
⟦ Σ ρ ⟧nf η = {!   !}
⟦ ρ₂ ─ ρ₁ ⟧nf η = {!   !}
⟦ l ▹ₙ τ ⟧nf η = sing (unlabel (⟦ l ⟧ne η) , ⟦ τ ⟧nf η)